#![allow(dead_code)]

use std::ops::BitXor;

pub mod commitment;
pub mod protocol;
pub mod soldering;

use commitment::XorHomomorphic;

use crate::bag::{Circuit as SubCircuit, S, Wirex};

pub type Id = u128;

#[derive(Clone, Debug)]
pub struct Component {
    id: Id,
    inputs: Vec<WireId>,
    outputs: Vec<WireId>,
    sub_circuit: SubCircuit,
    delta: S,
}

impl Component {
    pub fn garble(&self) -> GarbledComponent {
        let garbled_table = self.sub_circuit.garbled_gates();

        GarbledComponent {
            inner: self.clone(),
            garbled_table,
            wire_key_commitments: self
                .get_wire_keys()
                .map(|label0| XorHomomorphic::commit(&label0))
                .collect(),
        }
    }

    pub fn wires_count(&self) -> usize {
        self.sub_circuit.0.len()
    }

    pub fn get_wire_keys(&self) -> impl Iterator<Item = S> {
        self.sub_circuit.0.iter().map(|wire| wire.borrow().label0)
    }

    pub fn get_input_wire(&self, wire_id: usize) -> Option<&Wirex> {
        self.inputs
            .get(wire_id)
            .and(self.sub_circuit.0.get(wire_id))
    }

    pub fn get_output_wire(&self, wire_id: usize) -> Option<&Wirex> {
        self.outputs
            .get(wire_id)
            .and(self.sub_circuit.0.get(wire_id))
    }

    pub fn inputs(&self) -> impl Iterator<Item = &Wirex> {
        self.inputs
            .iter()
            .filter_map(|index| self.sub_circuit.0.get(*index))
    }

    pub fn outputs(&self) -> impl Iterator<Item = &Wirex> {
        self.outputs
            .iter()
            .filter_map(|index| self.sub_circuit.0.get(*index))
    }
}

#[derive(Debug)]
pub struct GarbledComponent {
    /// Structural template (meta-information about components and relationships)
    ///
    pub inner: Component,

    /// Garbling table
    pub garbled_table: Vec<Vec<S>>,

    /// Indicator bits σ
    //pub sigma_bits: Vec<bool>,

    /// XOR-homomomorphic commits for A⁰
    pub wire_key_commitments: Vec<commitment::XorHomomorphic>,
    ///// XOR-homomomorphic commits for σ
    //pub sigma_commitments: Vec<commitment::XorHomomorphic>,

    ///// Value ∆
    //pub delta: S,
    //
    ///// Pedersen-коммитмент к ∆
    //pub delta_commitment: commitment::Pedersen,
    //
    ///// Opening ∆ for Pedersen (needed to prove knowledge of ∆)
    //pub delta_opening: Option<commitment::Pedersen>,
}

impl GarbledComponent {
    pub fn get_wire_zero_keys(&self) -> Vec<S> {
        todo!()
    }
}

pub struct Circuit {
    components: Vec<Component>,
}

pub fn run_duplo_protocol(circuit: Circuit, bucket_size: usize) -> Vec<bool> {
    protocol::run_duplo_protocol(circuit, bucket_size)
}
