use crate::core::s::S;
use crate::core::utils::{LIMB_LEN, N_LIMBS, convert_between_blake3_and_normal_form};
use bitvm::{bigint::U256, hash::blake3::blake3_compute_script_with_limb, treepp::*};
use once_cell::sync::Lazy;
use std::sync::Mutex;

pub type WireId = usize;
pub type Wires = Vec<WireId>;

pub static ARENA: Lazy<Mutex<Vec<Wire>>> = Lazy::new(|| Mutex::new(Vec::new()));

pub fn new_wirex() -> WireId {
    let mut arena = ARENA.lock().unwrap();
    let id = arena.len();
    arena.push(Wire::new());
    id
}

pub(crate) fn with_arena<F, R>(mut f: F) -> R
where
    F: FnMut(&mut Vec<Wire>) -> R,
{
    let mut arena = ARENA.lock().unwrap();
    f(&mut arena)
}

pub trait WireOps {
    fn set(self, bit: bool);
    fn set2(self, bit: bool, label: S);
    fn get_value(self) -> bool;
    fn get_label(self) -> S;
    fn select(self, selector: bool) -> S;
    fn select_hash(self, selector: bool) -> S;
    fn commitment_script(self) -> Script;
}

impl WireOps for WireId {
    fn set(self, bit: bool) {
        with_arena(|wires| wires[self].set(bit));
    }

    fn set2(self, bit: bool, label: S) {
        with_arena(|wires| wires[self].set2(bit, label));
    }

    fn get_value(self) -> bool {
        with_arena(|wires| wires[self].get_value())
    }

    fn get_label(self) -> S {
        with_arena(|wires| wires[self].get_label())
    }

    fn select(self, selector: bool) -> S {
        with_arena(|wires| wires[self].select(selector))
    }

    fn select_hash(self, selector: bool) -> S {
        with_arena(|wires| wires[self].select_hash(selector))
    }

    fn commitment_script(self) -> Script {
        with_arena(|wires| wires[self].commitment_script())
    }
}

#[derive(Clone, Debug)]
pub struct Wire {
    pub label0: S,
    pub label1: S,
    pub hash0: S,
    pub hash1: S,
    pub value: Option<bool>,
    pub label: Option<S>,
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
        if selector { self.label1 } else { self.label0 }
    }

    pub fn select_hash(&self, selector: bool) -> S {
        if selector { self.hash1 } else { self.hash0 }
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
