use std::iter;

use crate::{
    core::{gate::CorrectnessError, gate_type::GateCount},
    Delta, EvaluatedWire, GarbledWire, GarbledWires, Gate, GateError, WireError, WireId, S,
};

/// Errors that can occur during circuit operations
#[derive(Debug, Clone, thiserror::Error, PartialEq, Eq)]
pub enum CircuitError {
    /// Gate-related error
    #[error("Gate error: {0}")]
    Gate(#[from] GateError),
    /// Circuit garbling failed
    #[error("Garbling failed: {0}")]
    GarblingFailed(String),
}

#[derive(Clone, Debug)]
pub struct Circuit {
    pub num_wire: usize,
    pub input_wires: Vec<WireId>,
    pub output_wires: Vec<WireId>,
    pub gates: Vec<Gate>,
    pub gate_count: GateCount,
}

impl Default for Circuit {
    fn default() -> Self {
        Self {
            num_wire: 2,
            input_wires: Default::default(),
            output_wires: Default::default(),
            gates: Default::default(),
            gate_count: GateCount::default(),
        }
    }
}

impl Circuit {
    pub fn get_false_wire_constant(&self) -> WireId {
        WireId(0)
    }

    pub fn get_true_wire_constant(&self) -> WireId {
        WireId(1)
    }

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
        self.gate_count.handle(gate.gate_type);
        self.gates.push(gate);
    }

    pub fn garble(&self) -> Result<GarbledCircuit, CircuitError> {
        log::debug!(
            "garble: start wires={} gates={}",
            self.num_wire,
            self.gates.len()
        );

        let delta = Delta::generate();

        let mut wires = GarbledWires::new(self.num_wire);
        wires
            .get_or_init(self.get_true_wire_constant(), || {
                GarbledWire::random(&delta)
            })
            .unwrap();

        wires
            .get_or_init(self.get_false_wire_constant(), || {
                GarbledWire::random(&delta)
            })
            .unwrap();

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
                match g.garble(i, &mut wires, &delta) {
                    Ok(Some(row)) => {
                        log::debug!("garble: gate[{i}] table_entries={row:?}");
                        Some(Ok(row))
                    }
                    Ok(None) => {
                        log::debug!("garble: gate[{i}] free");
                        None
                    }
                    Err(err) => {
                        log::error!("garble: gate[{i}] error={err:?}");
                        Some(Err(err))
                    }
                }
            })
            .collect::<Result<Vec<_>, _>>()?;

        log::debug!("garble: complete table_size={}", garbled_table.len());
        Ok(GarbledCircuit {
            structure: self.clone(),
            wires,
            delta,
            garbled_table,
        })
    }

    #[cfg(test)]
    pub fn full_cycle_test(
        &self,
        get_input: impl Fn(WireId) -> Option<bool>,
        get_expected_output: impl Fn(WireId) -> Option<bool>,
    ) {
        self.garble()
            .unwrap_or_else(|err| panic!("Can't garble with {err:#?}"))
            .evaluate(get_input)
            .unwrap_or_else(|err| panic!("Can't eval with {err:#?}"))
            .check_correctness()
            .unwrap_or_else(|err| panic!("Circuit not correct with {err:#?}"))
            .iter_output()
            .for_each(|(wire_id, res)| assert!(get_expected_output(wire_id) == Some(res)));
    }
}

#[derive(Debug, Clone, thiserror::Error, PartialEq, Eq)]
pub enum Error {
    #[error("Wire access failed: {0}")]
    WhileGetWire(#[from] WireError),
    #[error("Circuit input missing: wire {0} value not provided")]
    LostInput(WireId),
    #[error("Gate evaluation failed: {gate:?} requires unevaluated wire {wire_id}")]
    WrongGateOrder { gate: Gate, wire_id: WireId },
}

#[derive(Debug)]
pub struct GarbledCircuit {
    pub structure: Circuit,
    pub wires: GarbledWires,
    pub delta: Delta,
    pub garbled_table: Vec<S>,
}

#[derive(Debug)]
pub struct EvaluatedCircuit {
    pub structure: Circuit,
    wires: Vec<EvaluatedWire>,
    pub garbled_table: Vec<S>,
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
            .enumerate()
            .flat_map(|(gate_id, gate)| {
                match gate.check_correctness(
                    gate_id,
                    &|wire_id| self.get_evaluated_wire(wire_id),
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

        let true_wire = self.structure.get_true_wire_constant();
        let false_wire = self.structure.get_false_wire_constant();

        [true_wire, false_wire]
            .iter()
            .chain(self.structure.input_wires.iter())
            .copied()
            .try_for_each(|wire_id| {
                let value = match wire_id {
                    w if w.eq(&true_wire) => true,
                    w if w.eq(&false_wire) => false,
                    w => (get_input)(w).ok_or(Error::LostInput(wire_id))?,
                };
                let wire = self.wires.get(wire_id)?;
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

#[cfg(test)]
mod failure_tests {
    use std::collections::HashMap;

    use super::{Circuit, Error};
    use crate::{core::gate::CorrectnessError, CircuitError, Gate, GateError, GateType};

    #[test]
    fn test_missing_input_failure() {
        let mut circuit = Circuit::default();

        let a_wire = circuit.issue_input_wire();
        let b_wire = circuit.issue_input_wire();
        let out_wire = circuit.issue_wire();

        circuit.add_gate(Gate::new(GateType::And, a_wire, b_wire, out_wire));
        circuit.make_wire_output(out_wire);

        let garbled = circuit.garble().expect("Garbling should succeed");

        let result = garbled.evaluate(|wire_id| if wire_id == a_wire { Some(true) } else { None });

        match result {
            Err(Error::LostInput(wire)) => assert_eq!(wire, b_wire),
            Ok(_) => panic!("Expected LostInput error, got success"),
            Err(other) => panic!("Expected LostInput error, got: {other:?}"),
        }
    }

    #[test]
    fn test_wrong_gate_order_failure() {
        let mut circuit = Circuit::default();

        let input_a = circuit.issue_input_wire();
        let input_b = circuit.issue_input_wire();
        let intermediate_wire = circuit.issue_wire();
        let output_wire = circuit.issue_wire();

        // Create gates in correct wire ID order but wrong evaluation order
        // Gate 1: XOR input_a, input_b -> intermediate_wire
        // Gate 2: AND intermediate_wire, input_a -> output_wire
        // But we'll add them in reverse order so gate 2 evaluates before gate 1
        circuit.add_gate(Gate::new(
            GateType::And,
            intermediate_wire,
            input_a,
            output_wire,
        ));
        circuit.add_gate(Gate::new(
            GateType::Xor,
            input_a,
            input_b,
            intermediate_wire,
        ));
        circuit.make_wire_output(output_wire);

        assert_eq!(
            circuit.garble().err(),
            Some(CircuitError::Gate(GateError::InitWire {
                wire: "c",
                err: crate::WireError::InvalidWireIndex(intermediate_wire)
            }))
        );
    }

    #[test]
    fn test_garbling_with_invalid_wire_reference() {
        let mut circuit = Circuit::default();

        let a_wire = circuit.issue_input_wire();
        let invalid_wire = crate::WireId(999);
        let out_wire = circuit.issue_wire();

        circuit.add_gate(Gate::new(GateType::And, a_wire, invalid_wire, out_wire));
        circuit.make_wire_output(out_wire);

        let result = circuit.garble();

        assert!(
            result.is_err(),
            "Garbling should fail with invalid wire reference"
        );
    }

    #[test]
    fn test_correctness_check_failure() {
        let mut circuit = Circuit::default();

        let a_wire = circuit.issue_input_wire();
        let b_wire = circuit.issue_input_wire();
        let out_wire = circuit.issue_wire();

        circuit.add_gate(Gate::new(GateType::And, a_wire, b_wire, out_wire));
        circuit.make_wire_output(out_wire);

        let input_map = [(a_wire, true), (b_wire, false)]
            .into_iter()
            .collect::<HashMap<_, _>>();

        let mut garbled = circuit.garble().expect("Garbling should succeed");

        // Corrupt the entire first row of the garbled table
        for entry in &mut garbled.garbled_table {
            *entry = crate::S::random();
        }

        let evaluated = garbled
            .evaluate(|id| input_map.get(&id).copied())
            .expect("Evaluation should succeed");

        let result = evaluated.check_correctness();

        assert!(
            matches!(result, Err(ref errors) if errors.iter().any(|(_, error)| matches!(error, CorrectnessError::TableMismatch { .. }))),
            "Expected TableMismatch error from corrupted table"
        );
    }

    #[test]
    fn test_evaluation_all_inputs_missing() {
        let mut circuit = Circuit::default();

        let a_wire = circuit.issue_input_wire();
        let b_wire = circuit.issue_input_wire();
        let out_wire = circuit.issue_wire();

        circuit.add_gate(Gate::new(GateType::And, a_wire, b_wire, out_wire));
        circuit.make_wire_output(out_wire);

        let garbled = circuit.garble().expect("Garbling should succeed");

        let result = garbled.evaluate(|_| None);

        match result {
            Err(Error::LostInput(wire)) => {
                assert!(
                    wire == a_wire || wire == b_wire,
                    "Should fail on first missing input"
                );
            }
            Ok(_) => panic!("Expected LostInput error, got success"),
            Err(other) => panic!("Expected LostInput error, got: {other:?}"),
        }
    }
}
