use garbled_snark_verifier::*;
use rand::{RngCore, SeedableRng};
use std::sync::mpsc::channel;
use std::thread;

fn trng() -> rand::rngs::SmallRng {
    rand::rngs::SmallRng::seed_from_u64(0)
}

fn simple_and() -> Circuit {
    let mut c = Circuit::default();
    let a = c.issue_input_wire();
    let b = c.issue_input_wire();
    let out = c.issue_wire();
    c.add_gate(Gate::new(GateType::And, a, b, out));
    c.make_wire_output(out);
    c
}

#[test]
fn test_seeded_garbling_deterministic() {
    let circuit = simple_and();
    let seed = [42u8; 32];
    let g1 = circuit.garble_from_seed(seed).unwrap();
    let g2 = circuit.garble_from_seed(seed).unwrap();
    assert_eq!(g1.delta, g2.delta);
    assert_eq!(g1.garbled_table, g2.garbled_table);
    assert_eq!(
        g1.wires.get(WireId(2)).unwrap(),
        g2.wires.get(WireId(2)).unwrap()
    );
}

#[test]
fn test_verifier_detects_wrong_seed() {
    let circuit = simple_and();
    let mut rng = trng();
    let mut seed = [0u8; 32];
    rng.fill_bytes(&mut seed);
    let mut copy = {
        let (g, hashes) = circuit.garble_from_seed_with_commit(seed).unwrap();
        let table_hash = hashes.table_hash;
        GarbledCopy {
            seed,
            hashes,
            ciphertext_hash: table_hash,
            ciphertexts: Some(g.garbled_table.clone()),
        }
    };
    // corrupt seed
    copy.seed[0] ^= 1;
    let mut verifier = VerifierState::new(1, 0, &mut rng);
    let res = verifier.receive_copy(&circuit, 0, copy);
    assert!(res.is_err());
}

#[test]
fn test_full_protocol_honest() {
    let circuit = simple_and();
    let num = 3;
    let (tx, rx) = channel();
    thread::spawn({
        let circuit = circuit.clone();
        move || {
            let mut rng = trng();
            for i in 0..num {
                let mut seed = [0u8; 32];
                rng.fill_bytes(&mut seed);
                let (gc, hashes) = circuit.garble_from_seed_with_commit(seed).unwrap();
                let copy = GarbledCopy {
                    seed,
                    hashes: hashes.clone(),
                    ciphertext_hash: hashes.table_hash,
                    ciphertexts: Some(gc.garbled_table.clone()),
                };
                tx.send((i, copy)).unwrap();
            }
        }
    });

    let mut rng = trng();
    let mut verifier = VerifierState::new(num as usize, 1, &mut rng);
    for _ in 0..num {
        let (idx, copy) = rx.recv().unwrap();
        verifier.receive_copy(&circuit, idx, copy).unwrap();
    }
}
