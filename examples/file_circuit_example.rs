use std::{
    collections::HashMap,
    io::{self, Write},
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    },
    thread,
    time::{Duration, Instant},
    usize,
};

use bitvec::access::BitAccess;
use crossbeam::channel;
use garbled_snark_verifier::{
    circuit::{errors::CircuitError, file_gate_provider::FileGateProvider, GateProvider},
    Circuit, Delta, GarbledWire, GarbledWires, WireId, S,
};
use rand::Rng;

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

struct ThreadStats {
    thread_id: usize,
    gates_processed: usize,
    duration: Duration,
    delta: Delta,
    xor_result: S,
}

fn spawn_progress_monitor(
    gate_counter: Arc<AtomicUsize>,
    total_gates: usize,
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

            print!(
                "\rGate: {current_count}/{total_gates} ({percentage:.1}%) | Speed: {gates_per_second:.0} gates/s | {mem_info}"
            );
            io::stdout().flush().unwrap();

            last_count = current_count;
            last_time = current_time;

            if current_count > 0 && gates_per_second == 0.0 && elapsed > 3.0 {
                break;
            }
        }
    })
}

//fn run_multiple_garbling<H: digest::Digest + Default + Clone, G: GateProvider + Clone + Send>(
//    circuit: &Circuit<G>,
//    num_threads: usize,
//) -> Result<Vec<ThreadStats>, CircuitError> {
//    println!("Starting {} independent garbling threads...", num_threads);
//
//    let handles: Vec<_> = (0..num_threads)
//        .enumerate()
//        .map(|(id, thread_id)| {
//            let circuit_clone = circuit.clone();
//            thread::spawn(move || {
//                let start_time = Instant::now();
//                let mut rng = StdRng::seed_from_u64(id as u64);
//
//                match garble_with_streaming::<H, _>(&circuit_clone, &mut rng) {
//                    Ok((_, delta, xor_result)) => {
//                        let duration = start_time.elapsed();
//                        Ok(ThreadStats {
//                            thread_id,
//                            gates_processed: circuit_clone.gates.gate_count().unwrap_or(0),
//                            duration,
//                            delta,
//                            xor_result,
//                        })
//                    }
//                    Err(e) => Err(e),
//                }
//            })
//        })
//        .collect();
//
//    let mut results = Vec::new();
//    for handle in handles {
//        let result = handle
//            .join()
//            .map_err(|_| CircuitError::GarblingFailed("Thread join failed".to_string()))?;
//        results.push(result?);
//    }
//
//    Ok(results)
//}

fn garble_with_streaming<H: digest::Digest + Default + Clone, G: GateProvider>(
    circuit: &Circuit<G>,
    rng: &mut impl Rng,
) -> Result<(GarbledWires, Delta, S), CircuitError> {
    log::debug!(
        "garble_streaming: start wires={} gates={:?}",
        circuit.num_wire,
        circuit.gates.gate_count()
    );

    let delta = Delta::generate();
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

    log::debug!("garble_streaming: delta={delta:?}");

    let (sender, receiver) = channel::bounded::<S>(10000);

    // Progress tracking with atomic counter
    // Use zero as signal to abort thread
    let gate_counter = Arc::new(AtomicUsize::new(0));

    // Spawn progress monitoring thread
    let total_gates = circuit.gates.gate_count().unwrap_or(0);
    let progress_thread = spawn_progress_monitor(gate_counter.clone(), total_gates);

    let xor_thread = thread::spawn(move || {
        let mut xor_result = S::zero();
        while let Ok(ciphertext) = receiver.recv() {
            xor_result ^= &ciphertext;
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

    let xor_result = xor_thread
        .join()
        .map_err(|_| CircuitError::GarblingFailed("XOR thread join failed".to_string()))?;

    println!("xor_result: {xor_result:?}");

    // Wait for progress thread to finish and print final newline
    gate_counter.store(usize::MAX, Ordering::Relaxed);
    let _ = progress_thread.join();
    println!();

    log::debug!("garble_streaming: complete xor_result={xor_result:?}");
    Ok((wires, delta, xor_result))
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
    let progress_thread = spawn_progress_monitor(gate_counter.clone(), total_gates);

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

    // Load circuit file - replace with your actual circuit file path
    let circuit_file_path = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "circuit.bin".to_string());

    // Get number of threads from command line argument
    let num_threads = std::env::args()
        .nth(2)
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or_else(|| {
            thread::available_parallelism()
                .map(|n| n.get())
                .unwrap_or(4)
        });

    println!("Loading circuit file: {circuit_file_path}");
    println!("Using {num_threads} threads for parallel garbling");

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

    let start_time = Instant::now();
    let _result = evaluate_with_streaming(&file_circuit, input_handler)?.collect::<Vec<_>>()[0].1;
    let evaluation_duration = start_time.elapsed();

    // Display final evaluation statistics
    let total_gates = file_circuit.gates.gate_count().unwrap_or(0);
    let gates_per_sec = if evaluation_duration.as_secs_f64() > 0.0 {
        total_gates as f64 / evaluation_duration.as_secs_f64()
    } else {
        0.0
    };

    println!("\nEvaluation completed!");
    println!("  Total gates: {total_gates}");
    println!("  Total time: {:.2}s", evaluation_duration.as_secs_f64());
    println!("  Average throughput: {gates_per_sec:.0} gates/s");

    let final_mem_info = if let Some(usage) = memory_stats::memory_stats() {
        format!(
            "Physical: {:.2} MB, Virtual: {:.2} MB",
            usage.physical_mem as f64 / 1024.0 / 1024.0,
            usage.virtual_mem as f64 / 1024.0 / 1024.0
        )
    } else {
        "Memory: N/A".to_string()
    };
    println!("  Final memory usage: {final_mem_info}");

    println!("\nTesting multiple parallel garbling...");
    //match run_multiple_garbling::<DefaultHasher, _>(&file_circuit, num_threads) {
    //    Ok(results) => {
    //        println!(
    //            "All {} garbling threads completed successfully!",
    //            results.len()
    //        );

    //        let total_gates: usize = results.iter().map(|r| r.gates_processed).sum();
    //        let total_duration = results
    //            .iter()
    //            .map(|r| r.duration)
    //            .max()
    //            .unwrap_or(Duration::ZERO);
    //        let avg_gates_per_sec = if total_duration.as_secs_f64() > 0.0 {
    //            total_gates as f64 / total_duration.as_secs_f64()
    //        } else {
    //            0.0
    //        };

    //        println!("\nAggregate Statistics:");
    //        println!("  Total gates processed: {}", total_gates);
    //        println!("  Total time: {:.2}s", total_duration.as_secs_f64());
    //        println!("  Average throughput: {:.0} gates/s", avg_gates_per_sec);

    //        println!("\nPer-thread Statistics:");
    //        for stats in &results {
    //            let gates_per_sec = if stats.duration.as_secs_f64() > 0.0 {
    //                stats.gates_processed as f64 / stats.duration.as_secs_f64()
    //            } else {
    //                0.0
    //            };
    //            println!(
    //                "  Thread {}: {} gates in {:.2}s ({:.0} gates/s)",
    //                stats.thread_id,
    //                stats.gates_processed,
    //                stats.duration.as_secs_f64(),
    //                gates_per_sec
    //            );
    //        }
    //    }
    //    Err(e) => {
    //        println!("Multiple garbling failed: {:?}", e);
    //    }
    //}

    println!("\nFile-based circuit loading successful!");
    println!("Next steps: Implement input/output wire detection for your specific circuit");

    Ok(())
}
