use std::ops::Not;

use crate::{Delta, GarbledWires, Gate, GateError, WireError, WireId, S};

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
        let mut wires = GarbledWires::new(self.num_wire);
        let delta = Delta::generate();

        let garbled_table = self
            .gates
            .iter()
            .filter_map(|g| match g.garble(&mut wires, &delta) {
                Ok(row) if row.is_empty().not() => Some(Ok(row)),
                Ok(_) => None,
                Err(err) => Some(Err(err)),
            })
            .collect::<Result<Vec<Vec<_>>, _>>()?;

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

impl GarbledCircuit {
    pub fn evaluate(
        &self,
        get_input: impl Fn(WireId) -> Option<bool>,
    ) -> Result<impl Iterator<Item = Result<(WireId, bool), Error>>, Error> {
        let mut evaluated = vec![None; self.structure.num_wire];

        self.structure.input_wires.iter().try_for_each(|wire_id| {
            let value = (get_input)(*wire_id).ok_or(Error::LostInput(*wire_id))?;

            evaluated[wire_id.0] = Some(self.wires.get(*wire_id)?.select(value));

            Result::<_, Error>::Ok(())
        })?;

        let mut non_free_gate_index = 0;
        for gate in self.structure.gates.iter() {
            let a = evaluated[gate.wire_a.0].ok_or(Error::WrongGateOrder {
                gate: gate.clone(),
                wire_id: gate.wire_a,
            })?;
            let b = evaluated[gate.wire_b.0].ok_or(Error::WrongGateOrder {
                gate: gate.clone(),
                wire_id: gate.wire_b,
            })?;

            let evaluated_label = gate.evaluate(
                a,
                b,
                &self.delta,
                &self.garbled_table,
                &mut non_free_gate_index,
            );
            evaluated[gate.wire_c.0] = Some(evaluated_label);

            #[cfg(test)]
            {
                let evaluated_label = evaluated[gate.wire_c.0].unwrap();
                let wire = self.wires.get(gate.wire_c).unwrap();

                match evaluated_label {
                    l if l.eq(&wire.label1) | l.eq(&wire.label0) => (),
                    l => panic!(
                        "test-check: logic is broken, at wire_id {} with {l:?}",
                        gate.wire_c
                    ),
                }
            }
        }

        Ok(self.structure.output_wires.iter().map(move |&wire_id| {
            let label = evaluated[wire_id.0].ok_or(Error::OutputWireNotEval(wire_id))?;
            let wire = self.wires.get(wire_id)?;

            match label {
                l if l.eq(&wire.label0) => Ok((wire_id, false)),
                l if l.eq(&wire.label1) => Ok((wire_id, true)),
                _l => panic!("logic is broken, at wire_id {wire_id}"),
            }
        }))
    }
}
