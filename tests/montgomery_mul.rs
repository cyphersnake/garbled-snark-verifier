use ark_ff::Field;
use garbled_snark_verifier::Fp254Impl;
use garbled_snark_verifier::Fq;
use garbled_snark_verifier::*;
use rand::{RngCore, SeedableRng};

fn rnd() -> ark_bn254::Fq {
    let mut rng = rand::rngs::SmallRng::seed_from_u64(42);
    loop {
        let mut bytes = [0u8; 32];
        rng.fill_bytes(&mut bytes);
        if let Some(bn) = ark_bn254::Fq::from_random_bytes(&bytes) {
            return bn;
        }
    }
}

#[test]
fn test_montgomery_mul_consistency() {
    let mut circuit = Circuit::default();
    let a = Fq::new_bn(&mut circuit, true, false);
    let b = Fq::new_bn(&mut circuit, true, false);
    let c = Fq::mul_montgomery(&mut circuit, &a, &b);
    c.mark_as_output(&mut circuit);

    let a_val = Fq::as_montgomery(rnd());
    let b_val = Fq::as_montgomery(rnd());
    let expected = Fq::as_montgomery(Fq::from_montgomery(a_val) * Fq::from_montgomery(b_val));

    let a_input = Fq::get_wire_bits_fn(&a, &a_val).unwrap();
    let b_input = Fq::get_wire_bits_fn(&b, &b_val).unwrap();
    let c_output = Fq::get_wire_bits_fn(&c, &expected).unwrap();

    circuit
        .simple_evaluate(|w| a_input(w).or_else(|| b_input(w)))
        .unwrap()
        .for_each(|(wire_id, value)| {
            assert_eq!(c_output(wire_id), Some(value));
        });
}
