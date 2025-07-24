use rand::Rng;
use std::collections::{HashMap, HashSet};

use crate::{Circuit, S, circuit::garbling::GarbledCircuitHashes};

#[derive(Debug, Clone)]
pub struct GarbledCopy {
    pub seed: [u8; 32],
    pub hashes: GarbledCircuitHashes,
    pub ciphertexts: Vec<S>,
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
            self.stored_ciphertexts.insert(index, copy.ciphertexts);
            Ok(())
        } else {
            let recomputed = circuit
                .garble_from_seed(copy.seed)
                .map_err(|e| format!("garbling failed: {e:?}"))?;
            if recomputed.garbled_table != copy.ciphertexts {
                return Err("ciphertext mismatch".into());
            }
            if recomputed.hashes() != copy.hashes {
                return Err("hash mismatch".into());
            }
            Ok(())
        }
    }
}
