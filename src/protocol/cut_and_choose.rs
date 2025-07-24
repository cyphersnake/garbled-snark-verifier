use blake3;
use rand::Rng;
use std::collections::{HashMap, HashSet};

use crate::{Circuit, S, circuit::garbling::GarbledCircuitHashes};

#[derive(Debug, Clone)]
pub struct GarbledCopy {
    pub seed: [u8; 32],
    pub hashes: GarbledCircuitHashes,
    pub ciphertext_hash: S,
    pub ciphertexts: Option<Vec<S>>,
}

#[derive(Debug)]
pub struct VerifierState {
    pub eval_indices: HashSet<usize>,
    pub stored_ciphertexts: HashMap<usize, Vec<S>>, // evaluation circuits
}

impl VerifierState {
    pub fn new(num_copies: usize, eval_count: usize, rng: &mut impl Rng) -> Self {
        let mut eval_indices = HashSet::new();
        while eval_indices.len() < eval_count {
            let idx = rng.random_range(0..num_copies);
            eval_indices.insert(idx);
        }
        Self {
            eval_indices,
            stored_ciphertexts: HashMap::new(),
        }
    }

    pub fn receive_copy(
        &mut self,
        circuit: &Circuit,
        index: usize,
        copy: GarbledCopy,
    ) -> Result<(), String> {
        if self.eval_indices.contains(&index) {
            let cts = copy.ciphertexts.ok_or("missing ciphertexts")?;
            let mut h = blake3::Hasher::new();
            for ct in &cts {
                h.update(&ct.0);
            }
            if S(*h.finalize().as_bytes()) != copy.ciphertext_hash {
                return Err("table hash mismatch".into());
            }
            self.stored_ciphertexts.insert(index, cts);
            Ok(())
        } else {
            let (recomputed, hashes) = circuit
                .garble_from_seed_with_commit(copy.seed)
                .map_err(|e| format!("garbling failed: {e:?}"))?;
            if hashes != copy.hashes || hashes.table_hash != copy.ciphertext_hash {
                return Err("hash mismatch".into());
            }
            drop(recomputed);
            Ok(())
        }
    }
}
