use crate::bag::*;
use crate::circuits::bn254::finalexp::final_exponentiation_circuit_montgomery_fast;
use crate::circuits::bn254::fq::Fq;
use crate::circuits::bn254::fq12::Fq12;
use crate::circuits::bn254::fq2::Fq2;
use crate::circuits::bn254::fp254impl::Fp254Impl;
use crate::circuits::bn254::g1::{G1Projective, projective_to_affine_montgomery};
use crate::circuits::bn254::pairing::{
    deserialize_compressed_g1_circuit,
    deserialize_compressed_g2_circuit,
    multi_miller_loop_groth16_evaluate_montgomery_fast,
};
use ark_ec::{AffineRepr, pairing::Pairing};
use ark_ff::Field;
use crate::core::topology::append_gates_to_file;
use std::fs;
use std::io;
use std::path::Path;

/// Save Groth16 verifier subcircuits sequentially into `dir`.
pub fn save_subcircuits<P: AsRef<Path>>(
    dir: P,
    public: Wires,
    mut proof_a: Wires,
    mut proof_b: Wires,
    mut proof_c: Wires,
    vk: ark_groth16::VerifyingKey<ark_bn254::Bn254>,
    compressed: bool,
) -> io::Result<()> {
    let dir = dir.as_ref();
    fs::create_dir_all(dir)?;

    if compressed {
        let circuit = deserialize_compressed_g1_circuit(
            proof_a[..Fq::N_BITS].to_vec(),
            proof_a[Fq::N_BITS].clone(),
        );
        append_gates_to_file(dir.join("01_proof_a.bin"), &circuit.1)?;
        proof_a = circuit.0;

        let circuit = deserialize_compressed_g2_circuit(
            proof_b[..Fq2::N_BITS].to_vec(),
            proof_b[Fq2::N_BITS].clone(),
        );
        append_gates_to_file(dir.join("02_proof_b.bin"), &circuit.1)?;
        proof_b = circuit.0;

        let circuit = deserialize_compressed_g1_circuit(
            proof_c[..Fq::N_BITS].to_vec(),
            proof_c[Fq::N_BITS].clone(),
        );
        append_gates_to_file(dir.join("03_proof_c.bin"), &circuit.1)?;
        proof_c = circuit.0;
    }

    let circuit = G1Projective::scalar_mul_by_constant_base::<10>(
        public.clone(),
        vk.gamma_abc_g1[1].into_group(),
    );
    append_gates_to_file(dir.join("04_msm.bin"), &circuit.1)?;
    let msm_temp = circuit.0;

    let circuit = G1Projective::add_montgomery(
        msm_temp,
        G1Projective::wires_set_montgomery(vk.gamma_abc_g1[0].into_group()),
    );
    append_gates_to_file(dir.join("05_add.bin"), &circuit.1)?;
    let msm = circuit.0;

    let circuit = projective_to_affine_montgomery(msm);
    append_gates_to_file(dir.join("06_affine.bin"), &circuit.1)?;
    let msm_affine = circuit.0;

    let (f, _) = multi_miller_loop_groth16_evaluate_montgomery_fast(
        msm_affine,
        proof_c,
        proof_a,
        -vk.gamma_g2,
        -vk.delta_g2,
        proof_b,
    );

    let circuit = final_exponentiation_circuit_montgomery_fast(f);
    append_gates_to_file(dir.join("07_final_exp.bin"), &circuit.1)?;
    let f = circuit.0;

    let alpha_beta = ark_bn254::Bn254::final_exponentiation(ark_bn254::Bn254::multi_miller_loop(
        [vk.alpha_g1.into_group()],
        [-vk.beta_g2],
    ))
    .unwrap()
    .0
    .inverse()
    .unwrap();
    let circuit = Fq12::equal_constant(f, Fq12::as_montgomery(alpha_beta));
    append_gates_to_file(dir.join("08_equal.bin"), &circuit.1)?;

    Ok(())
}
