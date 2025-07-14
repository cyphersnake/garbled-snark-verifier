use std::{iter, ops::Not};

use crate::{
    core::gate::CorrectnessError, Delta, EvaluatedWire, GarbledWires, Gate, GateError, WireError,
    WireId, S,
};

mod basic;
mod u256;

pub use u256::BigIntWires;

/// Errors that can occur during circuit operations
#[derive(Debug, Clone, thiserror::Error)]
pub enum CircuitError {
    /// Gate-related error
    #[error("Gate error: {0}")]
    Gate(#[from] GateError),
    /// Circuit garbling failed
    #[error("Garbling failed: {0}")]
    GarblingFailed(String),
}

#[derive(Clone, Default)]
pub struct Circuit {
    pub num_wire: usize,
    pub input_wires: Vec<WireId>,
    pub output_wires: Vec<WireId>,
    pub gates: Vec<Gate>,
}

impl Circuit {
    pub fn issue_wire(&mut self) -> WireId {
        let new = WireId(self.num_wire);
        self.num_wire += 1;
        new
    }

    pub fn issue_input_wire(&mut self) -> WireId {
        let wire_id = self.issue_wire();
        self.make_wire_input(wire_id);
        wire_id
    }

    pub fn issue_output_wire(&mut self) -> WireId {
        let wire_id = self.issue_wire();
        self.make_wire_output(wire_id);
        wire_id
    }

    pub fn make_wire_input(&mut self, w: WireId) {
        match self.input_wires.binary_search(&w) {
            Ok(_) => {}
            Err(pos) => self.input_wires.insert(pos, w),
        }
    }

    pub fn make_wire_output(&mut self, w: WireId) {
        match self.output_wires.binary_search(&w) {
            Ok(_) => {}
            Err(pos) => self.output_wires.insert(pos, w),
        }
    }

    pub fn add_gate(&mut self, gate: Gate) {
        self.gates.push(gate);
    }

    pub fn garble(&self) -> Result<GarbledCircuit, CircuitError> {
        log::debug!(
            "garble: start wires={} gates={}",
            self.num_wire,
            self.gates.len()
        );
        let mut wires = GarbledWires::new(self.num_wire);
        let delta = Delta::generate();
        log::debug!("garble: delta={delta:?}");

        let garbled_table = self
            .gates
            .iter()
            .enumerate()
            .filter_map(|(i, g)| {
                log::debug!(
                    "garble: gate[{}] {:?} {}+{}->{}",
                    i,
                    g.gate_type,
                    g.wire_a,
                    g.wire_b,
                    g.wire_c
                );
                match g.garble(&mut wires, &delta) {
                    Ok(row) if row.is_empty().not() => {
                        log::debug!("garble: gate[{}] table_entries={}", i, row.len());
                        Some(Ok(row))
                    }
                    Ok(_) => {
                        log::debug!("garble: gate[{i}] free");
                        None
                    }
                    Err(err) => {
                        log::error!("garble: gate[{i}] error={err:?}");
                        Some(Err(err))
                    }
                }
            })
            .collect::<Result<Vec<Vec<_>>, _>>()?;

        log::debug!("garble: complete table_size={}", garbled_table.len());
        Ok(GarbledCircuit {
            structure: self.clone(),
            wires,
            delta,
            garbled_table,
        })
    }
}

#[derive(Debug, Clone, thiserror::Error)]
pub enum Error {
    #[error("TODO")]
    InputSizeNotConsistent { expected: usize, actual: usize },
    #[error("TODO")]
    WhileGetWire(#[from] WireError),
    #[error("TODO")]
    LostInput(WireId),
    #[error("TODO")]
    WrongGateOrder { gate: Gate, wire_id: WireId },
    #[error("TODO")]
    OutputWireNotEval(WireId),
}

pub struct GarbledCircuit {
    pub structure: Circuit,
    pub wires: GarbledWires,
    pub delta: Delta,
    pub garbled_table: Vec<Vec<S>>,
}

pub struct EvaluatedCircuit {
    pub structure: Circuit,
    wires: Vec<EvaluatedWire>,
    pub garbled_table: Vec<Vec<S>>,
}

impl EvaluatedCircuit {
    pub fn iter_output<'s>(&'s self) -> impl 's + Iterator<Item = (WireId, bool)> {
        self.structure
            .output_wires
            .iter()
            .map(move |wire_id| (*wire_id, self.wires.get(wire_id.0).unwrap().value))
    }

    fn get_evaluated_wire(&self, wire_id: WireId) -> Option<&EvaluatedWire> {
        self.wires.get(wire_id.0)
    }

    pub fn check_correctness(self) -> Result<Self, Vec<(Gate, CorrectnessError)>> {
        let mut table_gate_index = 0;
        let errors = self
            .structure
            .gates
            .iter()
            .flat_map(|gate| {
                match gate.check_correctness(
                    |wire_id| self.get_evaluated_wire(wire_id),
                    &self.garbled_table,
                    &mut table_gate_index,
                ) {
                    Err(errors) if errors.is_empty() => {
                        unreachable!("This function should not return an empty error set")
                    }
                    Err(errors) => Some(iter::repeat(gate.clone()).zip(errors).collect::<Vec<_>>()),
                    Ok(()) => None,
                }
            })
            .flatten()
            .collect::<Vec<_>>();

        if errors.is_empty() {
            Ok(self)
        } else {
            Err(errors)
        }
    }
}

impl GarbledCircuit {
    pub fn evaluate(
        &self,
        get_input: impl Fn(WireId) -> Option<bool>,
    ) -> Result<EvaluatedCircuit, Error> {
        log::debug!(
            "evaluate: start wires={} gates={} table_entries={}",
            self.structure.num_wire,
            self.structure.gates.len(),
            self.garbled_table.len()
        );
        let mut evaluated = vec![Option::<EvaluatedWire>::None; self.structure.num_wire];

        self.structure.input_wires.iter().try_for_each(|wire_id| {
            let value = (get_input)(*wire_id).ok_or(Error::LostInput(*wire_id))?;
            let wire = self.wires.get(*wire_id)?;
            let active_label = wire.select(value);

            log::debug!("evaluate: input {wire_id}={value} label={active_label:?}");

            evaluated[wire_id.0] = Some(EvaluatedWire {
                active_label,
                value,
            });
            Result::<_, Error>::Ok(())
        })?;

        for gate in self.structure.gates.iter() {
            let a = evaluated
                .get(gate.wire_a.0)
                .and_then(|eg| eg.as_ref())
                .ok_or(Error::WrongGateOrder {
                    gate: gate.clone(),
                    wire_id: gate.wire_a,
                })?;
            let b = evaluated
                .get(gate.wire_b.0)
                .and_then(|eg| eg.as_ref())
                .ok_or(Error::WrongGateOrder {
                    gate: gate.clone(),
                    wire_id: gate.wire_b,
                })?;
            let c = self.wires.get(gate.wire_c).unwrap();

            evaluated[gate.wire_c.0] = Some(gate.evaluate(a, b, c));
        }

        Ok(EvaluatedCircuit {
            // TODO Migrate to ununit unsafe logic
            wires: evaluated.into_iter().map(Option::unwrap).collect(),
            structure: self.structure.clone(),
            garbled_table: self.garbled_table.clone(),
        })
    }
}
