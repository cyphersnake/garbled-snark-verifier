#![feature(maybe_uninit_array_assume_init)]

use std::{
    collections::HashMap,
    fs,
    hash::Hash,
    io::{self, BufWriter, Write},
    mem::{self, MaybeUninit},
    path::Path,
    ptr,
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    },
    thread,
    time::{Duration, Instant, SystemTime, UNIX_EPOCH},
};

use bitcoin::hashes::{hash160, Hash as _H};
use crossbeam::channel;
use garbled_snark_verifier::{
    circuit::{errors::CircuitError, file_gate_provider::FileGateProvider, GateProvider},
    Circuit, Delta, GarbledWire, GarbledWires, WireId, S,
};
use rand::{rngs::StdRng, Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;
use serde::{Deserialize, Serialize};

// Include wire values generated from main branch
include!("../wire_values.rs");

/// Create input handler with actual proof values from main branch
fn create_proof_input_handler() -> Box<dyn Fn(WireId) -> Option<bool>> {
    // Create a HashMap for fast lookup
    let mut wire_values = HashMap::new();

    // Add all proof component values to the map
    for (wire_id, value) in PUBLIC_WIRE_VALUES.iter() {
        wire_values.insert(WireId(*wire_id as usize), *value);
    }

    for (wire_id, value) in PROOF_A_WIRE_VALUES.iter() {
        wire_values.insert(WireId(*wire_id as usize), *value);
    }

    for (wire_id, value) in PROOF_B_WIRE_VALUES.iter() {
        wire_values.insert(WireId(*wire_id as usize), *value);
    }

    for (wire_id, value) in PROOF_C_WIRE_VALUES.iter() {
        wire_values.insert(WireId(*wire_id as usize), *value);
    }

    Box::new(move |wire_id| wire_values.get(&wire_id).copied())
}

type DefaultHasher = blake3::Hasher;

#[derive(Serialize, Deserialize)]
struct LabelPair([u8; 16], [u8; 16]);

#[derive(Deserialize)]
struct Config {
    circuit_file_path: String,
    num_of_garbling: Option<usize>,
    save_path: String,
    save_ciphertext_ids: Vec<usize>,
}

struct ThreadStats {
    thread_id: usize,
    gates_processed: usize,
    duration: Duration,
    xor_result: S,
}

fn spawn_progress_monitor(
    gate_counter: Arc<AtomicUsize>,
    total_gates: usize,
    thread_id: Option<usize>,
) -> thread::JoinHandle<()> {
    thread::spawn(move || {
        let start_time = Instant::now();
        let mut last_count = 0;
        let mut last_time = start_time;

        loop {
            thread::sleep(Duration::from_millis(1000));

            let current_count = gate_counter.load(Ordering::Relaxed);
            let current_time = Instant::now();

            if current_count == 0 {
                continue;
            }
            if current_count == usize::MAX {
                break;
            }

            let elapsed = (current_time - last_time).as_secs_f64();
            let gates_per_second = if elapsed > 0.0 {
                (current_count - last_count) as f64 / elapsed
            } else {
                0.0
            };

            let mem_info = if let Some(usage) = memory_stats::memory_stats() {
                format!(
                    "Physical: {:.2} MB, Virtual: {:.2} MB",
                    usage.physical_mem as f64 / 1024.0 / 1024.0,
                    usage.virtual_mem as f64 / 1024.0 / 1024.0
                )
            } else {
                "Memory: N/A".to_string()
            };

            let percentage = if total_gates > 0 {
                (current_count as f64 / total_gates as f64) * 100.0
            } else {
                0.0
            };

            let thread_prefix = if let Some(id) = thread_id {
                format!("Thread {}: ", id)
            } else {
                String::new()
            };

            if let Some(id) = thread_id {
                // For multi-threaded: use ANSI escape codes to update specific line
                print!(
                    "\x1b[s\x1b[{}H{}Gate: {current_count}/{total_gates} ({percentage:.1}%) | Speed: {gates_per_second:.0} gates/s | {mem_info}\x1b[K\x1b[u",
                    id + 1, thread_prefix
                );
            } else {
                // For single-threaded: use carriage return
                print!(
                    "\r{}Gate: {current_count}/{total_gates} ({percentage:.1}%) | Speed: {gates_per_second:.0} gates/s | {mem_info}",
                    thread_prefix
                );
            }
            io::stdout().flush().unwrap();

            last_count = current_count;
            last_time = current_time;

            if current_count > 0 && gates_per_second == 0.0 && elapsed > 3.0 {
                break;
            }
        }
    })
}

fn run_multiple_garbling<H: digest::Digest + Default + Clone>(
    circuit_file_path: &str,
    circuit_template: &Circuit<FileGateProvider>,
    num_of_garbling: usize,
    save_path: &str,
    save_ciphertext_ids: &[usize],
) -> Result<Vec<ThreadStats>, CircuitError> {
    // Create timestamp for this run
    let timestamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_secs();
    let timestamp_dir = format!("{}/{}", save_path, timestamp);
    
    println!("Starting {} independent garbling threads...", num_of_garbling);
    println!("Saving to timestamped directory: {}", timestamp_dir);

    // Reserve space for thread progress lines
    for _ in 0..num_of_garbling {
        println!();
    }

    let handles: Vec<_> = (0..num_of_garbling)
        .enumerate()
        .map(|(id, thread_id)| {
            let circuit_file_path = circuit_file_path.to_string();
            let input_wires = circuit_template.input_wires.clone();
            let output_wires = circuit_template.output_wires.clone();
            let num_wire = circuit_template.num_wire;
            let timestamped_save_path = timestamp_dir.clone();
            let should_save_ciphertexts = save_ciphertext_ids.contains(&id);

            thread::spawn(move || {
                let start_time = Instant::now();
                let mut rng = ChaCha8Rng::seed_from_u64(id as u64);

                // Create a new FileGateProvider for this thread
                let file_gate_provider = match FileGateProvider::new(&circuit_file_path) {
                    Ok(provider) => provider,
                    Err(e) => {
                        return Err(CircuitError::GarblingFailed(format!(
                            "Failed to create FileGateProvider: {}",
                            e
                        )))
                    }
                };

                // Create a new circuit for this thread
                let thread_circuit = Circuit {
                    num_wire,
                    input_wires,
                    output_wires,
                    gates: file_gate_provider,
                    gate_count: Default::default(),
                };

                match garble_with_streaming_thread::<H, _>(
                    &thread_circuit,
                    &mut rng,
                    Some(thread_id),
                    &timestamped_save_path,
                    should_save_ciphertexts,
                ) {
                    Ok((_, xor_result)) => {
                        let duration = start_time.elapsed();
                        Ok(ThreadStats {
                            thread_id,
                            gates_processed: thread_circuit.gates.gate_count().unwrap_or(0),
                            duration,
                            xor_result,
                        })
                    }
                    Err(e) => Err(e),
                }
            })
        })
        .collect();

    let mut results = Vec::new();
    for handle in handles {
        let result = handle
            .join()
            .map_err(|_| CircuitError::GarblingFailed("Thread join failed".to_string()))?;
        results.push(result?);
    }

    Ok(results)
}

fn garble_with_streaming<H: digest::Digest + Default + Clone, G: GateProvider>(
    circuit: &Circuit<G>,
    rng: &mut impl Rng,
) -> Result<(GarbledWires, S), CircuitError> {
    garble_with_streaming_thread::<H, G>(circuit, rng, None, "", false)
}

#[inline(always)]
pub fn concat_16<T: Copy>(a: &[T; 16], b: &[T; 16]) -> [T; 32] {
    // --- choose ONE of the two lines below ---------------------------
    // Modern compiler (≥1.70):
    // let mut out: [MaybeUninit<T>; 32] = MaybeUninit::uninit_array();

    // Legacy compiler:
    let mut out: [MaybeUninit<T>; 32] =
        unsafe { MaybeUninit::<[MaybeUninit<T>; 32]>::uninit().assume_init() };
    // ------------------------------------------------------------------

    unsafe {
        ptr::copy_nonoverlapping(a.as_ptr(), out.as_mut_ptr() as *mut T, 16);
        ptr::copy_nonoverlapping(b.as_ptr(), (out.as_mut_ptr() as *mut T).add(16), 16);

        MaybeUninit::array_assume_init(out)
    }
}

fn garble_with_streaming_thread<H: digest::Digest + Default + Clone, G: GateProvider>(
    circuit: &Circuit<G>,
    rng: &mut impl Rng,
    thread_id: Option<usize>,
    save_path: &str,
    should_save_ciphertexts: bool,
) -> Result<(GarbledWires, S), CircuitError> {
    log::debug!(
        "garble_streaming: start wires={} gates={:?}",
        circuit.num_wire,
        circuit.gates.gate_count()
    );

    // Create save directory if needed
    let save_dir = if !save_path.is_empty() && thread_id.is_some() {
        let dir_path = format!("{}/{}", save_path, thread_id.unwrap());
        fs::create_dir_all(&dir_path).map_err(|e| {
            CircuitError::GarblingFailed(format!("Failed to create save directory {}: {}", dir_path, e))
        })?;
        Some(dir_path)
    } else {
        None
    };

    // Setup ciphertext file writer if needed
    let mut ciphertext_writer = if should_save_ciphertexts && save_dir.is_some() {
        let ciphertext_path = format!("{}/ciphertexts.bin", save_dir.as_ref().unwrap());
        let file = fs::File::create(&ciphertext_path).map_err(|e| {
            CircuitError::GarblingFailed(format!("Failed to create ciphertext file {}: {}", ciphertext_path, e))
        })?;
        Some(BufWriter::new(file))
    } else {
        None
    };

    let delta = Delta::generate(rng);
    let mut wires = GarbledWires::new(circuit.num_wire);
    let mut issue_fn = || GarbledWire::random(rng, &delta);

    [
        circuit.get_false_wire_constant(),
        circuit.get_true_wire_constant(),
    ]
    .iter()
    .chain(circuit.input_wires.iter())
    .for_each(|wire_id| {
        wires.get_or_init(*wire_id, &mut issue_fn).unwrap();
    });

    // Print bitcoin::hash160 of all public input wires (garbled) - accumulated
    let mut all_input_bytes = Vec::new();
    for &wire_id in &circuit.input_wires {
        if let Ok(garbled_wire) = wires.get(wire_id) {
            all_input_bytes.extend_from_slice(&garbled_wire.label0.0);
            all_input_bytes.extend_from_slice(&garbled_wire.label1.0);
        }
    }
    let input_hash =
        <bitcoin::hashes::hash160::Hash as bitcoin::hashes::Hash>::hash(&all_input_bytes);

    println!(
        "Bitcoin hash160 of all public input wires (garbled): {:?}",
        input_hash
    );

    // Save input labels if save directory exists
    if let Some(ref save_dir) = save_dir {
        let mut input_labels = Vec::new();
        for &wire_id in &circuit.input_wires {
            if let Ok(garbled_wire) = wires.get(wire_id) {
                input_labels.push(LabelPair(garbled_wire.label0.0, garbled_wire.label1.0));
            }
        }
        let input_labels_path = format!("{}/inputs_labels.json", save_dir);
        let input_labels_json = serde_json::to_string_pretty(&input_labels).map_err(|e| {
            CircuitError::GarblingFailed(format!("Failed to serialize input labels: {}", e))
        })?;
        fs::write(&input_labels_path, input_labels_json).map_err(|e| {
            CircuitError::GarblingFailed(format!("Failed to write input labels to {}: {}", input_labels_path, e))
        })?;
    }

    log::debug!("garble_streaming: delta={delta:?}");

    let (sender, receiver) = channel::bounded::<S>(10000);

    // Progress tracking with atomic counter
    // Use zero as signal to abort thread
    let gate_counter = Arc::new(AtomicUsize::new(0));

    // Spawn progress monitoring thread
    let total_gates = circuit.gates.gate_count().unwrap_or(0);
    let progress_thread = spawn_progress_monitor(gate_counter.clone(), total_gates, thread_id);

    let ciphertext_accumulator_thread = thread::spawn(move || {
        let mut xor_result = S::zero();
        while let Ok(ciphertext) = receiver.recv() {
            xor_result = S(
                blake3::hash(&concat_16(&xor_result.0, &ciphertext.0)).as_bytes()[0..16]
                    .try_into()
                    .unwrap(),
            );
            
            // Write ciphertext to file if writer is available
            if let Some(ref mut writer) = ciphertext_writer {
                if let Err(e) = writer.write_all(&ciphertext.0) {
                    log::error!("Failed to write ciphertext to file: {}", e);
                    break;
                }
            }
        }
        
        // Flush the writer if it exists
        if let Some(ref mut writer) = ciphertext_writer {
            if let Err(e) = writer.flush() {
                log::error!("Failed to flush ciphertext file: {}", e);
            }
        }
        
        xor_result
    });

    circuit.gates.gates().enumerate().try_for_each(|(i, g)| {
        gate_counter.store(i + 1, Ordering::Relaxed);

        match g.as_ref().garble::<H>(i, &mut wires, &delta, rng) {
            Ok(Some(row)) => {
                log::debug!("garble_streaming: gate[{i}] table_entries={row:?}");
                if let Err(err) = sender.send(row) {
                    return Err(CircuitError::GarblingFailed(format!("Send failed {err:?}")));
                }
                Ok(())
            }
            Ok(None) => {
                log::debug!("garble_streaming: gate[{i}] free");
                Ok(())
            }
            Err(err) => {
                log::error!("garble_streaming: gate[{i}] error={err:?}");
                Err(err)
            }
        }?;

        Ok(())
    })?;

    println!("eval done");

    drop(sender);

    let xor_result = ciphertext_accumulator_thread
        .join()
        .map_err(|_| CircuitError::GarblingFailed("XOR thread join failed".to_string()))?;

    println!("xor_result: {xor_result:?}");

    // Wait for progress thread to finish and print final newline
    gate_counter.store(usize::MAX, Ordering::Relaxed);
    let _ = progress_thread.join();
    println!();

    // Print bitcoin::hash160 of all output wires (garbled) - after full garbling process
    let mut all_output_bytes = Vec::new();
    for &wire_id in &circuit.output_wires {
        if let Ok(garbled_wire) = wires.get(wire_id) {
            all_output_bytes.extend_from_slice(&garbled_wire.label0.0);
            all_output_bytes.extend_from_slice(&garbled_wire.label1.0);
        }
    }
    let output_hash =
        <bitcoin::hashes::hash160::Hash as bitcoin::hashes::Hash>::hash(&all_output_bytes);
    println!(
        "Bitcoin hash160 of all output wires (garbled): {}",
        output_hash
    );

    // Save output labels and ciphertext hash if save directory exists
    if let Some(ref save_dir) = save_dir {
        // Save output labels
        let mut output_labels = Vec::new();
        for &wire_id in &circuit.output_wires {
            if let Ok(garbled_wire) = wires.get(wire_id) {
                output_labels.push(LabelPair(garbled_wire.label0.0, garbled_wire.label1.0));
            }
        }
        let output_labels_path = format!("{}/output_labels.json", save_dir);
        let output_labels_json = serde_json::to_string_pretty(&output_labels).map_err(|e| {
            CircuitError::GarblingFailed(format!("Failed to serialize output labels: {}", e))
        })?;
        fs::write(&output_labels_path, output_labels_json).map_err(|e| {
            CircuitError::GarblingFailed(format!("Failed to write output labels to {}: {}", output_labels_path, e))
        })?;

        // Save ciphertext hash
        let hash_path = format!("{}/ciphertext_hash.bin", save_dir);
        fs::write(&hash_path, &xor_result.0).map_err(|e| {
            CircuitError::GarblingFailed(format!("Failed to write ciphertext hash to {}: {}", hash_path, e))
        })?;
    }

    log::debug!("garble_streaming: complete xor_result={xor_result:?}");
    Ok((wires, xor_result))
}

fn evaluate_with_streaming<G: GateProvider>(
    circuit: &Circuit<G>,
    get_input: impl Fn(WireId) -> Option<bool>,
) -> Result<impl Iterator<Item = (WireId, bool)>, garbled_snark_verifier::circuit::evaluation::Error>
{
    log::debug!(
        "evaluate_streaming: start wires={} gates={:?}",
        circuit.num_wire,
        circuit.gates.gate_count()
    );

    use bitvec::prelude::*;
    let mut wire_values = bitvec![0; circuit.num_wire];

    // Initialize constant wires
    wire_values.set(circuit.get_false_wire_constant().0, false);
    wire_values.set(circuit.get_true_wire_constant().0, true);

    // Initialize input wires
    for &wire_id in &circuit.input_wires {
        let value = get_input(wire_id)
            .ok_or(garbled_snark_verifier::circuit::evaluation::Error::LostInput(wire_id))?;
        wire_values.set(wire_id.0, value);
    }

    // Progress tracking with atomic counter
    let gate_counter = Arc::new(AtomicUsize::new(0));

    // Spawn progress monitoring thread
    let total_gates = circuit.gates.gate_count().unwrap_or(0);
    let progress_thread = spawn_progress_monitor(gate_counter.clone(), total_gates, None);

    // Process gates with progress tracking
    circuit
        .gates
        .gates()
        .enumerate()
        .try_for_each(|(i, gate)| {
            gate_counter.store(i + 1, Ordering::Relaxed);

            let a = wire_values[gate.wire_a().0];
            let b = wire_values[gate.wire_b().0];
            let result = gate.gate_type().f()(a, b);
            wire_values.set(gate.wire_c().0, result);

            log::debug!("evaluate_streaming: gate[{i}] a={a} b={b} result={result}");

            Ok::<(), garbled_snark_verifier::circuit::evaluation::Error>(())
        })?;

    // Wait for progress thread to finish and print final newline
    gate_counter.store(usize::MAX, Ordering::Relaxed);
    let _ = progress_thread.join();
    println!();

    log::debug!("evaluate_streaming: complete");

    Ok(circuit
        .output_wires
        .iter()
        .map(move |&wire_id| (wire_id, wire_values[wire_id.0])))
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("File-based Circuit Example");
    println!("=========================");

    // Load config file from command line argument
    let config_file_path = std::env::args()
        .nth(1)
        .ok_or("Usage: cargo run --example file_circuit_example <config.toml>")?;

    println!("Loading config file: {config_file_path}");

    // Read and parse TOML config file
    let config_contents = std::fs::read_to_string(&config_file_path)
        .map_err(|e| format!("Failed to read config file '{}': {}", config_file_path, e))?;
    
    let config: Config = toml::from_str(&config_contents)
        .map_err(|e| format!("Failed to parse config file '{}': {}", config_file_path, e))?;

    let circuit_file_path = config.circuit_file_path;
    let num_of_garbling = config.num_of_garbling.unwrap_or_else(|| {
        thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(4)
    });
    let save_path = config.save_path;
    let save_ciphertext_ids = config.save_ciphertext_ids;

    println!("Loading circuit file: {circuit_file_path}");
    println!("Using {num_of_garbling} garblings for parallel processing");
    println!("Save path: {save_path}");
    println!("Save ciphertext for garbling IDs: {:?}", save_ciphertext_ids);

    // Create a FileGateProvider from the circuit file
    let file_gate_provider = FileGateProvider::new(&circuit_file_path)?;
    println!(
        "File contains {} gates",
        file_gate_provider.gate_count().unwrap()
    );

    // Create a Circuit using the FileGateProvider
    // For now, we'll use placeholder values - in reality these would be detected
    let file_circuit = Circuit {
        num_wire: 11659311111,
        input_wires: PUBLIC_WIRE_VALUES
            .iter()
            .chain(PROOF_A_WIRE_VALUES.iter())
            .chain(PROOF_B_WIRE_VALUES.iter())
            .chain(PROOF_C_WIRE_VALUES.iter())
            .map(|(wire_id, _val)| WireId(*wire_id as usize))
            .collect::<Vec<WireId>>(),
        output_wires: vec![WireId(OUTPUT_WIRE_VALUE.0 as usize)],
        gates: file_gate_provider,
        gate_count: Default::default(),
    };

    println!("Created file-based circuit (input/output detection not implemented)");

    // Use proof values from main branch as input handler
    let input_handler = create_proof_input_handler();

    println!(
        "Created input handler with {} wire values",
        PUBLIC_WIRE_VALUES.len()
            + PROOF_A_WIRE_VALUES.len()
            + PROOF_B_WIRE_VALUES.len()
            + PROOF_C_WIRE_VALUES.len()
    );

    // Run circuit evaluation with progress tracking
    println!("\nRunning circuit evaluation with progress tracking...");

    //let start_time = Instant::now();
    //let _result = evaluate_with_streaming(&file_circuit, input_handler)?.collect::<Vec<_>>()[0].1;
    //let evaluation_duration = start_time.elapsed();

    //// Display final evaluation statistics
    //let total_gates = file_circuit.gates.gate_count().unwrap_or(0);
    //let gates_per_sec = if evaluation_duration.as_secs_f64() > 0.0 {
    //    total_gates as f64 / evaluation_duration.as_secs_f64()
    //} else {
    //    0.0
    //};

    //println!("\nEvaluation completed!");
    //println!("  Total gates: {total_gates}");
    //println!("  Total time: {:.2}s", evaluation_duration.as_secs_f64());
    //println!("  Average throughput: {gates_per_sec:.0} gates/s");

    //let final_mem_info = if let Some(usage) = memory_stats::memory_stats() {
    //    format!(
    //        "Physical: {:.2} MB, Virtual: {:.2} MB",
    //        usage.physical_mem as f64 / 1024.0 / 1024.0,
    //        usage.virtual_mem as f64 / 1024.0 / 1024.0
    //    )
    //} else {
    //    "Memory: N/A".to_string()
    //};
    //println!("  Final memory usage: {final_mem_info}");

    println!("\nTesting multiple parallel garbling...");
    match run_multiple_garbling::<DefaultHasher>(&circuit_file_path, &file_circuit, num_of_garbling, &save_path, &save_ciphertext_ids) {
        Ok(results) => {
            println!(
                "All {} garbling threads completed successfully!",
                results.len()
            );

            let total_gates: usize = results.iter().map(|r| r.gates_processed).sum();
            let total_duration = results
                .iter()
                .map(|r| r.duration)
                .max()
                .unwrap_or(Duration::ZERO);
            let avg_gates_per_sec = if total_duration.as_secs_f64() > 0.0 {
                total_gates as f64 / total_duration.as_secs_f64()
            } else {
                0.0
            };

            println!("\nAggregate Statistics:");
            println!("  Total gates processed: {}", total_gates);
            println!("  Total time: {:.2}s", total_duration.as_secs_f64());
            println!("  Average throughput: {:.0} gates/s", avg_gates_per_sec);

            println!("\nPer-thread Statistics:");
            for stats in &results {
                let gates_per_sec = if stats.duration.as_secs_f64() > 0.0 {
                    stats.gates_processed as f64 / stats.duration.as_secs_f64()
                } else {
                    0.0
                };
                println!(
                    "  Thread {}: {} gates in {:.2}s ({:.0} gates/s)",
                    stats.thread_id,
                    stats.gates_processed,
                    stats.duration.as_secs_f64(),
                    gates_per_sec
                );
            }
        }
        Err(e) => {
            println!("Multiple garbling failed: {:?}", e);
        }
    }

    println!("\nFile-based circuit loading successful!");
    println!("Next steps: Implement input/output wire detection for your specific circuit");

    Ok(())
}
