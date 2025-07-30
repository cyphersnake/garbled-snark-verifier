use std::{collections::HashMap, thread};

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

    let xor_thread = thread::spawn(move || {
        let mut xor_result = S::zero();
        while let Ok(ciphertext) = receiver.recv() {
            xor_result ^= &ciphertext;
        }
        xor_result
    });

    circuit.gates.gates().enumerate().try_for_each(|(i, g)| {
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

    drop(sender);

    let xor_result = xor_thread
        .join()
        .map_err(|_| CircuitError::GarblingFailed("XOR thread join failed".to_string()))?;

    log::debug!("garble_streaming: complete xor_result={:?}", xor_result);
    Ok((wires, delta, xor_result))
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("File-based Circuit Example");
    println!("=========================");

    // Load circuit file - replace with your actual circuit file path
    let circuit_file_path = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "circuit.bin".to_string());

    println!("Loading circuit file: {circuit_file_path}");

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

    // For demonstration, show that we can iterate through gates lazily
    println!("\nDemonstrating lazy gate loading (first 5 gates):");

    // TODO: Once input/output detection is implemented:
    //let result = file_circuit
    //    .simple_evaluate(input_handler)?
    //    .collect::<Vec<_>>()[0]
    //    .1;

    //assert!(result);

    println!("\nTesting streaming garbling...");
    let mut rng = rand::rng();
    match garble_with_streaming::<DefaultHasher, _>(&file_circuit, &mut rng) {
        Ok((_wires, delta, xor_result)) => {
            println!("Streaming garbling successful!");
            println!("  Wires object created");
            println!("  Delta: {:?}", delta);
            println!("  XOR of all ciphertexts: {:?}", xor_result);
        }
        Err(e) => {
            println!("Streaming garbling failed: {:?}", e);
        }
    }

    println!("\nFile-based circuit loading successful!");
    println!("Next steps: Implement input/output wire detection for your specific circuit");

    Ok(())
}
