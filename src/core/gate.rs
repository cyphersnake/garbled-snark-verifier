use log::debug;

pub use crate::GateType;
use crate::{Delta, EvaluatedWire, GarbledWire, GarbledWires, S, WireError, WireId};

#[allow(clippy::enum_variant_names)]
#[derive(Clone, Debug, thiserror::Error, PartialEq, Eq)]
pub enum Error {
    #[error("Error while get wire {wire}: {err:?}")]
    GetWire { wire: &'static str, err: WireError },
    #[error("Error while init wire {wire}: {err:?}")]
    InitWire { wire: &'static str, err: WireError },
    #[error("Error while get_or_init wire {wire}: {err:?}")]
    GetOrInitWire { wire: &'static str, err: WireError },
}
pub type GateError = Error;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Gate {
    pub wire_a: WireId,
    pub wire_b: WireId,
    pub wire_c: WireId,
    pub gate_type: GateType,
}

impl Gate {
    #[must_use]
    pub fn new(t: GateType, a: WireId, b: WireId, c: WireId) -> Self {
        Self {
            wire_a: a,
            wire_b: b,
            wire_c: c,
            gate_type: t,
        }
    }

    #[must_use]
    pub fn and(wire_a: WireId, wire_b: WireId, wire_c: WireId) -> Self {
        Self {
            wire_a,
            wire_b,
            wire_c,
            gate_type: GateType::And,
        }
    }

    #[must_use]
    pub fn nand(wire_a: WireId, wire_b: WireId, wire_c: WireId) -> Self {
        Self {
            wire_a,
            wire_b,
            wire_c,
            gate_type: GateType::Nand,
        }
    }

    #[must_use]
    pub fn nimp(wire_a: WireId, wire_b: WireId, wire_c: WireId) -> Self {
        Self {
            wire_a,
            wire_b,
            wire_c,
            gate_type: GateType::Nimp,
        }
    }

    #[must_use]
    pub fn imp(wire_a: WireId, wire_b: WireId, wire_c: WireId) -> Self {
        Self {
            wire_a,
            wire_b,
            wire_c,
            gate_type: GateType::Imp,
        }
    }

    #[must_use]
    pub fn ncimp(wire_a: WireId, wire_b: WireId, wire_c: WireId) -> Self {
        Self {
            wire_a,
            wire_b,
            wire_c,
            gate_type: GateType::Ncimp,
        }
    }

    #[must_use]
    pub fn cimp(wire_a: WireId, wire_b: WireId, wire_c: WireId) -> Self {
        Self {
            wire_a,
            wire_b,
            wire_c,
            gate_type: GateType::Cimp,
        }
    }

    #[must_use]
    pub fn nor(wire_a: WireId, wire_b: WireId, wire_c: WireId) -> Self {
        Self {
            wire_a,
            wire_b,
            wire_c,
            gate_type: GateType::Nor,
        }
    }

    #[must_use]
    pub fn or(wire_a: WireId, wire_b: WireId, wire_c: WireId) -> Self {
        Self {
            wire_a,
            wire_b,
            wire_c,
            gate_type: GateType::Or,
        }
    }

    #[must_use]
    pub fn xor(wire_a: WireId, wire_b: WireId, wire_c: WireId) -> Self {
        Self {
            wire_a,
            wire_b,
            wire_c,
            gate_type: GateType::Xor,
        }
    }

    #[must_use]
    pub fn xnor(wire_a: WireId, wire_b: WireId, wire_c: WireId) -> Self {
        Self {
            wire_a,
            wire_b,
            wire_c,
            gate_type: GateType::Xnor,
        }
    }

    #[must_use]
    pub fn not(wire_a: WireId) -> Self {
        Self {
            wire_a,
            wire_b: wire_a,
            wire_c: wire_a,
            gate_type: GateType::Not,
        }
    }

    /// Creates an AND-variant gate with configurable boolean function.                                                                                      │ │
    ///                                                                                                                                                      │ │
    /// This function implements the formula: `((a XOR f[0]) AND (b XOR f[1])) XOR f[2]`                                                                     │ │
    /// where the 3-bit encoding `f` determines which of the 8 AND-variant gate types to create.                                                             │ │
    ///                                                                                                                                                      │ │
    /// # Arguments                                                                                                                                          │ │
    ///                                                                                                                                                      │ │
    /// * `wire_a` - First input wire                                                                                                                        │ │
    /// * `wire_b` - Second input wire                                                                                                                       │ │
    /// * `wire_c` - Output wire                                                                                                                             │ │
    /// * `f` - 3-bit encoding array `[f0, f1, f2]` that determines the gate type:                                                                           │ │
    ///   - `[0,0,0]` → AND gate                                                                                                                             │ │
    ///   - `[0,0,1]` → NAND gate                                                                                                                            │ │
    ///   - `[0,1,0]` → NIMP gate (A AND NOT B)                                                                                                              │ │
    ///   - `[0,1,1]` → IMP gate (A implies B)                                                                                                               │ │
    ///   - `[1,0,0]` → NCIMP gate (NOT A AND B)                                                                                                             │ │
    ///   - `[1,0,1]` → CIMP gate (B implies A)                                                                                                              │ │
    ///   - `[1,1,0]` → NOR gate                                                                                                                             │ │
    ///   - `[1,1,1]` → OR gate                                                                                                                              │ │
    ///
    /// # Returns                                                                                                                                            │ │
    ///                                                                                                                                                      │ │
    /// A new `Gate` instance with the specified wires and gate type.                                                                                        │ │
    #[must_use]
    pub fn and_variant(a: WireId, b: WireId, c: WireId, f: [bool; 3]) -> Self {
        Self::new(
            match f {
                [false, false, false] => GateType::And,
                [false, false, true] => GateType::Nand,
                [false, true, false] => GateType::Nimp,
                [false, true, true] => GateType::Imp,
                [true, false, false] => GateType::Ncimp,
                [true, false, true] => GateType::Cimp,
                [true, true, false] => GateType::Nor,
                [true, true, true] => GateType::Or,
            },
            a,
            b,
            c,
        )
    }

    pub fn is_free(&self) -> bool {
        self.gate_type.is_free()
    }

    fn wire_a<'w>(
        &self,
        wires: &'w mut GarbledWires,
        delta: &Delta,
    ) -> Result<&'w GarbledWire, Error> {
        wires
            .get_or_init(self.wire_a, || GarbledWire::random(delta))
            .map_err(|err| Error::GetWire { wire: "a", err })
    }

    fn wire_b<'w>(
        &self,
        wires: &'w mut GarbledWires,
        delta: &Delta,
    ) -> Result<&'w GarbledWire, Error> {
        wires
            .get_or_init(self.wire_b, || GarbledWire::random(delta))
            .map_err(|err| Error::GetWire { wire: "b", err })
    }

    fn init_wire_c(&self, wires: &mut GarbledWires, label0: S, label1: S) -> Result<(), Error> {
        wires
            .init(self.wire_c, GarbledWire::new(label0, label1))
            .map_err(|err| Error::InitWire { wire: "c", err })
            .map(|_| ())
    }

    pub fn garble(&self, wires: &mut GarbledWires, delta: &Delta) -> Result<Vec<S>, Error> {
        debug!(
            "gate_garble: {:?} {}+{}->{}",
            self.gate_type, self.wire_a, self.wire_b, self.wire_c
        );
        match self.gate_type {
            GateType::Xor => {
                let a_label0 = self.wire_a(wires, delta)?.select(false);
                let b_label0 = self.wire_b(wires, delta)?.select(false);

                let c_label0 = a_label0 ^ &b_label0;
                let c_label1 = c_label0 ^ delta;

                self.init_wire_c(wires, c_label0, c_label1)?;

                Ok(vec![])
            }
            GateType::Xnor => {
                let a_label0 = self.wire_a(wires, delta)?.select(false);
                let b_label0 = self.wire_b(wires, delta)?.select(false);

                let c_label0 = a_label0 ^ &b_label0 ^ delta;
                let c_label1 = c_label0 ^ delta;

                self.init_wire_c(wires, c_label0, c_label1)?;

                Ok(vec![])
            }
            GateType::Not => {
                assert_eq!(self.wire_a, self.wire_b);
                assert_eq!(self.wire_b, self.wire_c);

                self.wire_a(wires, delta)?;

                wires
                    .toggle_wire_not_mark(self.wire_c)
                    .map_err(|err| Error::InitWire { wire: "c", err })?;

                Ok(vec![])
            }
            _gt => {
                let gate_f = self.gate_type.f();
                let c = wires
                    .init(self.wire_c, GarbledWire::random(delta))
                    .map_err(|err| Error::GetOrInitWire { wire: "c", err })?
                    .clone();

                let a = self.wire_a(wires, delta)?.clone();
                let b = self.wire_b(wires, delta)?;

                let table = [(false, false), (false, true), (true, false), (true, true)]
                    .iter()
                    .enumerate()
                    .map(|(idx, (i, j))| {
                        let k = (gate_f)(*i, *j);
                        let a_label = a.select(*i);
                        let b_label = b.select(*j);
                        let c_label = c.select(k);
                        let ab_hash = S::hash_together(a_label, b_label);
                        let table_value = c_label.neg() + ab_hash;

                        debug!(
                            "gate_garble[{idx}]: {a_label:?} {:?} {b_label:?} = {c_label:?} ({ab_hash:?} -> {table_value:?})",
                            self.gate_type
                        );

                        table_value
                    })
                    .collect();

                Ok(table)
            }
        }
    }

    pub fn evaluate(&self, a: &EvaluatedWire, b: &EvaluatedWire, c: &GarbledWire) -> EvaluatedWire {
        let evaluated_value = (self.gate_type.f())(a.value, b.value);

        EvaluatedWire {
            active_label: c.select(evaluated_value),
            value: evaluated_value,
        }
    }
}

#[derive(thiserror::Error, Debug, PartialEq)]
pub enum CorrectnessError {
    #[error("Gate verification failed: computed {calculated}, expected {actual}")]
    Value { calculated: bool, actual: bool },
    #[error("XOR gate label mismatch: computed {calculated:?}, expected {actual:?}")]
    XorLabel { calculated: S, actual: S },
    #[error("XNOR gate label mismatch: computed {calculated:?}, expected {actual:?}")]
    XnorLabel { calculated: S, actual: S },

    #[error("NOT gate label verification failed: wires A={a:?}, B={b:?}, C={c:?}")]
    NotLabel {
        a: EvaluatedWire,
        b: EvaluatedWire,
        c: EvaluatedWire,
    },

    #[error(
        "Garbled table mismatch at row {table_index}: expected {evaluated_c_label:?}, got table entry"
    )]
    TableMismatch {
        table_row: Vec<S>,
        a: EvaluatedWire,
        b: EvaluatedWire,
        c: EvaluatedWire,
        table_index: usize,
        ab_hash: S,
        evaluated_c_label: S,
    },
}

impl Gate {
    pub fn check_correctness<'s, 'w>(
        &'s self,
        get_evaluated: impl Fn(WireId) -> Option<&'w EvaluatedWire>,
        table: &[Vec<S>],
        table_gate_index: &mut usize,
    ) -> Result<(), Vec<CorrectnessError>> {
        let a = get_evaluated(self.wire_a).unwrap();
        let b = get_evaluated(self.wire_b).unwrap();
        let c = get_evaluated(self.wire_c).unwrap();

        let mut errors = vec![];
        log::debug!("gate_eval: {:?} a={:?} b={:?}", self.gate_type, a, b);

        // We can't check `EvaluatedWire` for Not Gate,
        // because it is closed to itself (a == b == c)
        if GateType::Not != self.gate_type {
            let expected_c_value = (self.gate_type.f())(a.value, b.value);

            if expected_c_value != c.value {
                errors.push(CorrectnessError::Value {
                    calculated: expected_c_value,
                    actual: c.value,
                })
            }
        }

        match self.gate_type {
            GateType::Xor => {
                let res = a.active_label ^ &b.active_label;

                log::debug!("gate_eval: XOR result={res:?}");

                if res != c.active_label {
                    errors.push(CorrectnessError::XorLabel {
                        calculated: res,
                        actual: c.active_label,
                    })
                }
            }
            GateType::Xnor => {
                let calculated_label = a.active_label ^ &b.active_label;

                if calculated_label != c.active_label {
                    errors.push(CorrectnessError::XnorLabel {
                        calculated: calculated_label,
                        actual: c.active_label,
                    })
                }
            }
            GateType::Not => {
                if a != b || b != c {
                    errors.push(CorrectnessError::NotLabel {
                        a: a.clone(),
                        b: b.clone(),
                        c: c.clone(),
                    })
                }
            }
            _gt => {
                let i = a.value() as usize;
                let j = b.value() as usize;
                let table_index = (i << 1) | j;

                let table_value = &table[*table_gate_index][table_index];
                *table_gate_index += 1;
                let ab_hash = S::hash_together(a.active_label, b.active_label);

                let c_label = table_value.neg() + ab_hash;

                if c_label != c.active_label {
                    errors.push(CorrectnessError::TableMismatch {
                        table_row: table[*table_gate_index - 1].clone(),
                        table_index,
                        a: a.clone(),
                        b: b.clone(),
                        c: c.clone(),
                        ab_hash,
                        evaluated_c_label: c_label,
                    })
                }
            }
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::*;

    fn create_test_delta() -> Delta {
        Delta::generate()
    }

    fn issue_test_wire() -> GarbledWires {
        GarbledWires::new(1000)
    }

    fn create_test_wire_ids() -> (WireId, WireId, WireId) {
        (WireId(0), WireId(1), WireId(2))
    }

    fn test_gate_e2e(gate: Gate, expected_fn: fn(bool, bool) -> bool, gate_name: &str) {
        let delta = create_test_delta();
        let mut wires = issue_test_wire();

        let table = gate
            .garble(&mut wires, &delta)
            .expect("Garbling should succeed");

        let wire_a_garbled = wires.get(gate.wire_a).expect("Wire A should exist");
        let wire_b_garbled = wires.get(gate.wire_b).expect("Wire B should exist");
        let wire_c_garbled = wires.get(gate.wire_c).expect("Wire C should exist");

        let test_cases = [(false, false), (false, true), (true, false), (true, true)];

        for (input_a, input_b) in test_cases {
            let eval_a = EvaluatedWire {
                active_label: wire_a_garbled.select(input_a),
                value: input_a,
            };
            let eval_b = EvaluatedWire {
                active_label: wire_b_garbled.select(input_b),
                value: input_b,
            };

            let eval_c = gate.evaluate(&eval_a, &eval_b, wire_c_garbled);

            let expected_output = expected_fn(input_a, input_b);
            assert_eq!(
                eval_c.value, expected_output,
                "Evaluation should be correct for {gate_name}({input_a}, {input_b})"
            );

            let mut evaluations = HashMap::new();
            evaluations.insert(gate.wire_a, eval_a);
            evaluations.insert(gate.wire_b, eval_b);
            evaluations.insert(gate.wire_c, eval_c);

            let mut table_index = 0;

            let correctness_result = gate.check_correctness(
                |wire_id: WireId| evaluations.get(&wire_id),
                &[table.clone()],
                &mut table_index,
            );

            assert_eq!(
                correctness_result,
                Ok(()),
                "Correctness check should pass for {gate_name}({input_a}, {input_b})"
            );
        }
    }

    fn test_not_gate_e2e(gate: Gate) {
        let delta = create_test_delta();
        let mut wires = issue_test_wire();

        let table = gate
            .garble(&mut wires, &delta)
            .expect("Garbling should succeed");

        let wire_garbled = wires.get(gate.wire_a).expect("Wire should exist");

        for input in [false, true] {
            let eval_wire = EvaluatedWire {
                active_label: wire_garbled.select(input),
                value: input,
            };

            let eval_c = gate.evaluate(&eval_wire, &eval_wire, wire_garbled);

            let expected_output = !input;
            assert_eq!(
                eval_c.value, expected_output,
                "Evaluation should be correct for NOT({input})"
            );

            let mut evaluations = HashMap::new();
            evaluations.insert(gate.wire_a, eval_wire.clone());
            evaluations.insert(gate.wire_b, eval_wire.clone());
            evaluations.insert(gate.wire_c, eval_wire);

            let mut table_index = 0;

            let correctness_result = gate.check_correctness(
                |wire_id: WireId| evaluations.get(&wire_id),
                &[table.clone()],
                &mut table_index,
            );

            assert_eq!(
                correctness_result,
                Ok(()),
                "Correctness check should pass for NOT({input})"
            );
        }
    }

    #[test]
    fn test_and_gate() {
        let (wire_a, wire_b, wire_c) = create_test_wire_ids();
        let gate = Gate::and(wire_a, wire_b, wire_c);
        test_gate_e2e(gate, |a, b| a && b, "AND");
    }

    #[test]
    fn test_nand_gate() {
        let (wire_a, wire_b, wire_c) = create_test_wire_ids();
        let gate = Gate::nand(wire_a, wire_b, wire_c);
        test_gate_e2e(gate, |a, b| !(a && b), "NAND");
    }

    #[test]
    fn test_nimp_gate() {
        let (wire_a, wire_b, wire_c) = create_test_wire_ids();
        let gate = Gate::nimp(wire_a, wire_b, wire_c);
        test_gate_e2e(gate, |a, b| a && !b, "NIMP");
    }

    #[test]
    fn test_imp_gate() {
        let (wire_a, wire_b, wire_c) = create_test_wire_ids();
        let gate = Gate::imp(wire_a, wire_b, wire_c);
        test_gate_e2e(gate, |a, b| !a || b, "IMP");
    }

    #[test]
    fn test_ncimp_gate() {
        let (wire_a, wire_b, wire_c) = create_test_wire_ids();
        let gate = Gate::ncimp(wire_a, wire_b, wire_c);
        test_gate_e2e(gate, |a, b| !a && b, "NCIMP");
    }

    #[test]
    fn test_cimp_gate() {
        let (wire_a, wire_b, wire_c) = create_test_wire_ids();
        let gate = Gate::cimp(wire_a, wire_b, wire_c);
        test_gate_e2e(gate, |a, b| !b || a, "CIMP");
    }

    #[test]
    fn test_nor_gate() {
        let (wire_a, wire_b, wire_c) = create_test_wire_ids();
        let gate = Gate::nor(wire_a, wire_b, wire_c);
        test_gate_e2e(gate, |a, b| !(a || b), "NOR");
    }

    #[test]
    fn test_or_gate() {
        let (wire_a, wire_b, wire_c) = create_test_wire_ids();
        let gate = Gate::or(wire_a, wire_b, wire_c);
        test_gate_e2e(gate, |a, b| a || b, "OR");
    }

    #[test]
    fn test_xor_gate() {
        let (wire_a, wire_b, wire_c) = create_test_wire_ids();
        let gate = Gate::xor(wire_a, wire_b, wire_c);
        test_gate_e2e(gate, |a, b| a ^ b, "XOR");
    }

    #[test]
    fn test_xnor_gate() {
        let (wire_a, wire_b, wire_c) = create_test_wire_ids();
        let gate = Gate::xnor(wire_a, wire_b, wire_c);
        test_gate_e2e(gate, |a, b| !(a ^ b), "XNOR");
    }

    #[test]
    fn test_not_gate() {
        let wire_a = WireId(0);
        let gate = Gate::not(wire_a);
        test_not_gate_e2e(gate);
    }
}
