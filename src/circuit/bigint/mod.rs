#![allow(dead_code)]

use std::{collections::HashMap, iter};

use bitvec::prelude::*;
pub use num_bigint::BigUint;

use super::Circuit;
use crate::WireId;

mod add;
mod cmp;
mod mul;
pub use add::*;

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("BigUint overflow: value requires {actual} bits, limit is {limit}")]
    TooBigUint { limit: usize, actual: usize },
}
pub type BigUintError = Error;

pub fn bits_from_biguint(u: &BigUint) -> BitVec<u8> {
    let mut bytes = u.to_bytes_le();
    if bytes.len() < 32 {
        bytes.resize(32, 0);
    }
    BitVec::from_vec(bytes)
}

pub fn bits_from_biguint_with_len(u: &BigUint, bit_count: usize) -> Result<BitVec<u8>, Error> {
    if u.bits() as usize > bit_count {
        return Err(Error::TooBigUint {
            limit: bit_count,
            actual: u.bits() as usize,
        });
    }

    let mut bytes = u.to_bytes_le();
    //let byte_count = (bit_count + 7) / 8;
    let byte_count = bit_count.div_ceil(8);
    bytes.resize(byte_count, 0);
    Ok(BitVec::from_vec(bytes))
}

#[derive(Debug)]
pub struct BigIntWires {
    bits: Vec<WireId>,
}

impl BigIntWires {
    pub fn new(circuit: &mut Circuit, len: usize, is_input: bool, is_output: bool) -> Self {
        Self {
            bits: iter::repeat_with(|| {
                let w = circuit.issue_wire();
                if is_input {
                    circuit.make_wire_input(w);
                }
                if is_output {
                    circuit.make_wire_output(w);
                }
                w
            })
            .take(len)
            .collect(),
        }
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.bits.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn iter(&self) -> impl Iterator<Item = &WireId> {
        self.bits.iter()
    }

    pub fn get_wire_bits_fn(&self, u: &BigUint) -> Result<impl Fn(WireId) -> Option<bool>, Error> {
        let bits = bits_from_biguint_with_len(u, self.bits.len())?;

        let mapping = (0..self.bits.len())
            .map(|i| (self.bits[i], *bits.get(i).unwrap()))
            .collect::<HashMap<WireId, bool>>();

        Ok(move |wire_id| mapping.get(&wire_id).copied())
    }
}
