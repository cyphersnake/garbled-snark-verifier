use std::ops::Not;

use crate::{Delta, GarbledWires, Gate, GateError, S, WireError, WireId};

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

impl GarbledCircuit {
    pub fn evaluate(
        &self,
        get_input: impl Fn(WireId) -> Option<bool>,
    ) -> Result<impl Iterator<Item = Result<(WireId, bool), Error>>, Error> {
        log::debug!(
            "evaluate: start wires={} gates={} table_entries={}",
            self.structure.num_wire,
            self.structure.gates.len(),
            self.garbled_table.len()
        );
        let mut evaluated: Vec<Option<(S, bool)>> = vec![None; self.structure.num_wire];

        self.structure.input_wires.iter().try_for_each(|wire_id| {
            let value = (get_input)(*wire_id).ok_or(Error::LostInput(*wire_id))?;
            let label = self.wires.get(*wire_id)?.select(value);
            log::debug!("evaluate: input {wire_id}={value} label={label:?}");
            evaluated[wire_id.0] = Some((label, value));
            Result::<_, Error>::Ok(())
        })?;

        let mut non_free_gate_index = 0;
        for (i, gate) in self.structure.gates.iter().enumerate() {
            let a = match evaluated[gate.wire_a.0] {
                Some(v) => v,
                None => {
                    if let Some(val) = (get_input)(gate.wire_a) {
                        let label = self.wires.get(gate.wire_a)?.select(val);
                        evaluated[gate.wire_a.0] = Some((label, val));
                        (label, val)
                    } else {
                        return Err(Error::WrongGateOrder {
                            gate: gate.clone(),
                            wire_id: gate.wire_a,
                        });
                    }
                }
            };
            let b = match evaluated[gate.wire_b.0] {
                Some(v) => v,
                None => {
                    if let Some(val) = (get_input)(gate.wire_b) {
                        let label = self.wires.get(gate.wire_b)?.select(val);
                        evaluated[gate.wire_b.0] = Some((label, val));
                        (label, val)
                    } else {
                        return Err(Error::WrongGateOrder {
                            gate: gate.clone(),
                            wire_id: gate.wire_b,
                        });
                    }
                }
            };
            log::debug!(
                "evaluate: gate[{}] {:?} a={:?} b={:?}",
                i,
                gate.gate_type,
                a,
                b
            );

            let table_idx_before = non_free_gate_index;
            let c_wire = self.wires.get(gate.wire_c)?;
            let evaluated_label = gate.evaluate(
                a,
                b,
                (c_wire.label0, c_wire.label1),
                &self.delta,
                &self.garbled_table,
                &mut non_free_gate_index,
            );
            let used_table = non_free_gate_index > table_idx_before;
            log::debug!("evaluate: gate[{i}] out={evaluated_label:?} table_used={used_table}");
            evaluated[gate.wire_c.0] = Some(evaluated_label);

            #[cfg(test)]
            {
                let (label, bit) = evaluated[gate.wire_c.0].unwrap();
                let wire = self.wires.get(gate.wire_c).unwrap();

                match label {
                    l if l.eq(&wire.label0) && !bit => (),
                    l if l.eq(&wire.label1) && bit => (),
                    l if l.eq(&wire.label0) || l.eq(&wire.label1) => panic!(
                        "test-check: label-bit mismatch at wire_id {} with {l:?} and bit {bit}",
                        gate.wire_c
                    ),
                    l => panic!(
                        "test-check: logic is broken, at wire_id {} with {l:?}",
                        gate.wire_c
                    ),
                }
            }
        }

        log::debug!("evaluate: complete used_table_entries={non_free_gate_index}");
        Ok(self.structure.output_wires.iter().map(move |&wire_id| {
            let (label, bit) = evaluated[wire_id.0].ok_or(Error::OutputWireNotEval(wire_id))?;
            let wire = self.wires.get(wire_id)?;
            let result = match label {
                l if l.eq(&wire.label0) && !bit => Ok((wire_id, false)),
                l if l.eq(&wire.label1) && bit => Ok((wire_id, true)),
                l if l.eq(&wire.label0) || l.eq(&wire.label1) => panic!(
                    "logic mismatch: label {l:?} does not match bit {bit} for wire_id {wire_id}",
                ),
                _l => panic!("logic is broken, at wire_id {wire_id}"),
            };
            if let Ok((id, val)) = &result {
                log::debug!("evaluate: output {id}={val}");
            }
            result
        }))
    }
}
