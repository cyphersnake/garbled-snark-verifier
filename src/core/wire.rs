use std::cell::RefCell;
use std::rc::Rc;

use crate::core::s::S;
use crate::core::utils::{convert_between_blake3_and_normal_form, LIMB_LEN, N_LIMBS};
use bitvm::{bigint::U256, hash::blake3::blake3_compute_script_with_limb, treepp::*};

pub type WireId = usize;

#[derive(Clone, Debug)]
pub struct Wire {
    pub label0: S,
    pub label1: S,
    pub hash0: S,
    pub hash1: S,
    pub value: Option<bool>,
    pub label: Option<S>,
}

#[derive(Default, Clone, Debug)]
pub struct Wires(Vec<Wire>);

impl Wires {
    pub fn get(&self, index: usize) -> Option<&Wire> {
        self.0.get(index)
    }

    pub fn get_mut(&mut self, index: usize) -> Option<&mut Wire> {
        self.0.get_mut(index)
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn issue(&mut self) -> WireId {
        self.0.push(Wire::new());
        self.0.len() - 1
    }
}

impl Default for Wire {
    fn default() -> Self {
        Self::new()
    }
}

impl Wire {
    pub fn new() -> Self {
        let label0 = S::random();
        let label1 = S::random();
        let hash0 = label0.hash();
        let hash1 = label1.hash();
        Self {
            label0,
            label1,
            hash0,
            hash1,
            value: None,
            label: None,
        }
    }

    pub fn select(&self, selector: bool) -> S {
        if selector {
            self.label1
        } else {
            self.label0
        }
    }

    pub fn select_hash(&self, selector: bool) -> S {
        if selector {
            self.hash1
        } else {
            self.hash0
        }
    }

    pub fn get_value(&self) -> bool {
        assert!(self.value.is_some());
        self.value.unwrap()
    }

    pub fn get_label(&self) -> S {
        assert!(self.value.is_some());
        self.label.unwrap()
    }

    pub fn set(&mut self, bit: bool) {
        assert!(self.value.is_none());
        self.value = Some(bit);
        self.label = Some(self.select(bit));
    }

    pub fn set2(&mut self, bit: bool, label: S) {
        assert!(self.value.is_none());
        self.value = Some(bit);
        self.label = Some(label);
    }

    pub fn commitment_script(&self) -> Script {
        script! {                                                  // x bit_x
            OP_TOALTSTACK                                          // x | bit_x
            { convert_between_blake3_and_normal_form() }
            for _ in 0..N_LIMBS {0}                                // x'0 | bit_x
            { blake3_compute_script_with_limb(32, LIMB_LEN) }
            { U256::transform_limbsize(4, LIMB_LEN.into()) }       // hx | bit_x
            OP_FROMALTSTACK                                        // hx bit_x
            OP_IF
                { U256::push_hex(&hex::encode(self.hash1.0)) }
            OP_ELSE
                { U256::push_hex(&hex::encode(self.hash0.0)) }
            OP_ENDIF                                               // hx hash
            { U256::equal(0, 1) }
        }
    }
}
