use ark_crypto_primitives::snark::{CircuitSpecificSetupSNARK, SNARK};
use ark_ec::pairing::Pairing;
use ark_ff::{PrimeField, UniformRand};
use ark_groth16::Groth16;
use ark_relations::lc;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_std::{
    rand::{RngCore, SeedableRng},
    test_rng,
};
use garbled_snark_verifier::circuits::bn254::fr::Fr;
use garbled_snark_verifier::circuits::bn254::g1::G1Affine;
use garbled_snark_verifier::circuits::bn254::g2::G2Affine;
use garbled_snark_verifier::circuits::groth16::{
    groth16_verifier_evaluate, groth16_verifier_evaluate_montgomery,
};
use serde_json::json;
use std::env;

/// Format large numbers in human-readable format (M for millions, B for billions)
fn format_number(n: u64) -> String {
    if n >= 1_000_000_000 {
        format!("{:.1}B", n as f64 / 1_000_000_000.0)
    } else if n >= 1_000_000 {
        format!("{:.1}M", n as f64 / 1_000_000.0)
    } else if n >= 1_000 {
        format!("{:.1}K", n as f64 / 1_000.0)
    } else {
        n.to_string()
    }
}

/// Circuit size parameter k, where the number of constraints = 2^k
/// k = 6 means 2^6 = 64 constraints for the test circuit
const K: usize = 6;

#[derive(Copy, Clone)]
struct DummyCircuit<F: PrimeField> {
    pub a: Option<F>,
    pub b: Option<F>,
    pub num_variables: usize,
    pub num_constraints: usize,
}

impl<F: PrimeField> ConstraintSynthesizer<F> for DummyCircuit<F> {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        let a = cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
        let b = cs.new_witness_variable(|| self.b.ok_or(SynthesisError::AssignmentMissing))?;
        let c = cs.new_input_variable(|| {
            let a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
            let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;

            Ok(a * b)
        })?;

        for _ in 0..(self.num_variables - 3) {
            let _ = cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
        }

        for _ in 0..self.num_constraints - 1 {
            cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)?;
        }

        cs.enforce_constraint(lc!(), lc!(), lc!())?;

        Ok(())
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let json_output = args.contains(&"--json".to_string());

    if !json_output {
        println!("Running Groth16 verifier gate count example");
        println!("Circuit size: k = {}, constraints = {}", K, 1 << K);
    }

    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());
    let circuit = DummyCircuit::<<ark_bn254::Bn254 as Pairing>::ScalarField> {
        a: Some(<ark_bn254::Bn254 as Pairing>::ScalarField::rand(&mut rng)),
        b: Some(<ark_bn254::Bn254 as Pairing>::ScalarField::rand(&mut rng)),
        num_variables: 10,
        num_constraints: 1 << K,
    };
    let (pk, vk) = Groth16::<ark_bn254::Bn254>::setup(circuit, &mut rng).unwrap();

    let c = circuit.a.unwrap() * circuit.b.unwrap();

    let proof = Groth16::<ark_bn254::Bn254>::prove(&pk, circuit, &mut rng).unwrap();

    if !json_output {
        println!("Setup and proof generation completed");
    }

    let public = Fr::wires_set(c);
    let proof_a = G1Affine::wires_set_montgomery(proof.a);
    let proof_b = G2Affine::wires_set_montgomery(proof.b);
    let proof_c = G1Affine::wires_set_montgomery(proof.c);
    let (result, gate_count) =
        groth16_verifier_evaluate_montgomery(public, proof_a, proof_b, proof_c, vk, false);

    if json_output {
        let and_variants = gate_count.nonfree_gate_count();
        let xor_variants = gate_count.0[8] + gate_count.0[9];
        let not_gates = gate_count.0[10];
        let total_gates = gate_count.total_gate_count();

        let output = json!({
            "circuit_size": {
                "k": K,
                "constraints": 1 << K
            },
            "gate_count": {
                "and_variants": and_variants,
                "and_variants_formatted": format_number(and_variants),
                "xor_variants": xor_variants,
                "xor_variants_formatted": format_number(xor_variants),
                "not": not_gates,
                "not_formatted": format_number(not_gates),
                "total": total_gates,
                "total_formatted": format_number(total_gates),
                "breakdown": gate_count.0
            },
            "verification_result": result.borrow().get_value()
        });
        println!("{}", serde_json::to_string_pretty(&output).unwrap());
    } else {
        println!("\n=== GATE COUNT ===");
        gate_count.print();
        println!("Verification result: {}", result.borrow().get_value());
    }
}
