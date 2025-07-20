use log::debug;

pub use crate::GateType;
use crate::{Delta, EvaluatedWire, GarbledWire, GarbledWires, WireError, WireId, S};

pub type GateId = usize;

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
    pub fn not(wire_a: &mut WireId) -> Self {
        let wire_a = *wire_a;
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

    /// Return ciphertext for garble table if presented
    pub fn garble(
        &self,
        gate_id: GateId,
        wires: &mut GarbledWires,
        delta: &Delta,
    ) -> Result<Option<S>, Error> {
        debug!(
            "gate_garble: {:?} {}+{}->{} gid={}",
            self.gate_type, self.wire_a, self.wire_b, self.wire_c, gate_id
        );
        match self.gate_type {
            GateType::Xor => {
                let a_label0 = self.wire_a(wires, delta)?.select(false);
                let b_label0 = self.wire_b(wires, delta)?.select(false);

                let c_label0 = a_label0 ^ &b_label0;
                let c_label1 = c_label0 ^ delta;

                self.init_wire_c(wires, c_label0, c_label1)?;

                Ok(None)
            }
            GateType::Xnor => {
                let a_label0 = self.wire_a(wires, delta)?.select(false);
                let b_label0 = self.wire_b(wires, delta)?.select(false);

                let c_label0 = a_label0 ^ &b_label0 ^ delta;
                let c_label1 = c_label0 ^ delta;

                self.init_wire_c(wires, c_label0, c_label1)?;

                Ok(None)
            }
            GateType::Not => {
                assert_eq!(self.wire_a, self.wire_b);
                assert_eq!(self.wire_b, self.wire_c);

                self.wire_a(wires, delta)?;

                wires
                    .toggle_wire_not_mark(self.wire_c)
                    .map_err(|err| Error::InitWire { wire: "c", err })?;

                Ok(None)
            }
            _ => {
                let a = self.wire_a(wires, delta)?.clone();
                let b = self.wire_b(wires, delta)?;

                let (ciphertext, w0) = garble(gate_id, self.gate_type, &a, b, delta);

                self.init_wire_c(wires, w0, w0 ^ delta)?;

                Ok(Some(ciphertext))
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
    #[error("Gate {0} is not calculated but already requested")]
    NotEvaluated(WireId),
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
        "Garbled table mismatch at row {table_row:#?}: expected {evaluated_c_label:?}, got table entry {c:#?}"
    )]
    TableMismatch {
        table_row: S,
        a: EvaluatedWire,
        b: EvaluatedWire,
        c: EvaluatedWire,
        evaluated_c_label: S,
    },
}

impl Gate {
    /// Calculate the expected output value and label for this gate
    pub fn calculate_output(
        &self,
        gate_id: GateId,
        a: &EvaluatedWire,
        b: &EvaluatedWire,
        garble_table: &[S],
        table_gate_index: &mut usize,
    ) -> EvaluatedWire {
        let expected_value = (self.gate_type.f())(a.value, b.value);

        let expected_label = match self.gate_type {
            GateType::Xor => a.active_label ^ &b.active_label,
            GateType::Xnor => a.active_label ^ &b.active_label,
            GateType::Not => {
                // For NOT gates, all wires are the same, so return the input
                a.active_label
            }
            _ => {
                let ct = garble_table[*table_gate_index];
                *table_gate_index += 1;
                degarble(gate_id, self.gate_type, &ct, a, b)
            }
        };

        EvaluatedWire {
            active_label: expected_label,
            value: expected_value,
        }
    }

    pub fn check_correctness<'s, 'w>(
        &'s self,
        gate_id: GateId,
        get_evaluated: &impl Fn(WireId) -> Option<&'w EvaluatedWire>,
        garble_table: &[S],
        table_gate_index: &mut usize,
    ) -> Result<(), Vec<CorrectnessError>> {
        let a = get_evaluated(self.wire_a);
        let b = get_evaluated(self.wire_b);
        let c = get_evaluated(self.wire_c);

        let mut errors = vec![];

        let (a, b, c) = match (a, b, c) {
            (Some(a), Some(b), Some(c)) => (a, b, c),
            (a, b, c) => {
                if a.is_none() {
                    errors.push(CorrectnessError::NotEvaluated(self.wire_a));
                }

                if b.is_none() {
                    errors.push(CorrectnessError::NotEvaluated(self.wire_b));
                }

                if c.is_none() {
                    errors.push(CorrectnessError::NotEvaluated(self.wire_c));
                }

                return Err(errors);
            }
        };

        log::debug!("gate_eval: {:?} a={:?} b={:?}", self.gate_type, a, b);

        let expected_output = self.calculate_output(gate_id, a, b, garble_table, table_gate_index);

        // Check value correctness (skip for NOT gates as they're self-referential)
        if GateType::Not != self.gate_type && expected_output.value != c.value {
            errors.push(CorrectnessError::Value {
                calculated: expected_output.value,
                actual: c.value,
            })
        }

        // Check label correctness based on gate type
        match self.gate_type {
            GateType::Xor => {
                log::debug!("gate_eval: XOR result={:?}", expected_output.active_label);

                if expected_output.active_label != c.active_label {
                    errors.push(CorrectnessError::XorLabel {
                        calculated: expected_output.active_label,
                        actual: c.active_label,
                    })
                }
            }
            GateType::Xnor => {
                if expected_output.active_label != c.active_label {
                    errors.push(CorrectnessError::XnorLabel {
                        calculated: expected_output.active_label,
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
            _ => {
                if expected_output.active_label != c.active_label {
                    errors.push(CorrectnessError::TableMismatch {
                        table_row: garble_table[*table_gate_index - 1],
                        a: a.clone(),
                        b: b.clone(),
                        c: c.clone(),
                        evaluated_c_label: expected_output.active_label,
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

mod garbling {
    use super::{GateId, GateType};
    use crate::{Delta, EvaluatedWire, GarbledWire, S};

    /// Get permute bit (LSB) from S
    const fn perm_bit(s: &S) -> bool {
        (s.0[31] & 1) != 0
    }

    /// Fixed-key AES hash with unique tweak per gate
    fn aes_hash(x: &S, tweak: GateId) -> S {
        // Using Blake3 as AES substitute for now - in production should use AES
        S(*blake3::Hasher::new()
            .update(&x.0)
            .update(&tweak.to_le_bytes())
            .finalize()
            .as_bytes())
    }

    pub(super) fn garble(
        gate_id: GateId,
        gate_type: GateType,
        a: &GarbledWire,
        b: &GarbledWire,
        delta: &Delta,
    ) -> (S, S) {
        let (alpha_a, alpha_b, alpha_c) = gate_type.alphas();

        // pre-compute both right-hashes
        let h_b0 = aes_hash(&b.select(false), gate_id);
        let h_b1 = aes_hash(&b.select(true), gate_id);

        // Wa^{αa}
        let w_a_alpha = a.select(alpha_a);

        let ciphertext = h_b0 ^ &h_b1 ^ &w_a_alpha; // TE

        let pb = perm_bit(&b.select(false));
        let mut w0 = if pb { h_b1 } else { h_b0 };
        if alpha_c {
            w0 ^= delta;
        }

        (ciphertext, w0)
    }

    pub(super) fn degarble(
        gate_id: GateId,
        gate_type: GateType,
        ciphertext: &S,
        a: &EvaluatedWire,
        b: &EvaluatedWire,
    ) -> S {
        let h_b = aes_hash(&b.active_label, gate_id);

        let result = (gate_type.f())(a.value(), b.value());
        let p_b = perm_bit(&b.active_label);

        match p_b {
            true => h_b ^ ciphertext ^ &a.active_label,
            false => h_b,
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use crate::{core::gate::GateId, Delta, GarbledWire, GateType, S};

        const GATE_ID: GateId = 0;

        const TEST_CASES: [(bool, bool); 4] =
            [(false, false), (false, true), (true, false), (true, true)];

        fn garble_consistency(gt: GateType) {
            let delta = Delta::generate();

            #[derive(Debug, PartialEq, Eq)]
            struct FailedCase {
                wire_a_lsb0: bool,
                wire_b_lsb0: bool,
                a_value: bool,
                b_value: bool,
                c_value: bool,
                c: GarbledWire,
                evaluated: S,
                expected: S,
            }
            let mut failed_cases = Vec::new();

            // Create wires with specific LSB patterns
            let a_label0 = S::random();
            let b_label0 = S::random();
            let mut a = GarbledWire::new(a_label0, a_label0 ^ &delta);
            let mut b = GarbledWire::new(b_label0, b_label0 ^ &delta);

            // Test all combinations of LSB patterns for label0
            for wire_a_lsb0 in [false, true] {
                for wire_b_lsb0 in [false, true] {
                    // Set LSB of label0 to desired values
                    a.label0.0[31] = (a.label0.0[31] & 0xFE) | (wire_a_lsb0 as u8);
                    b.label0.0[31] = (b.label0.0[31] & 0xFE) | (wire_b_lsb0 as u8);

                    a.label1 = a.label0 ^ &delta;
                    b.label1 = b.label0 ^ &delta;

                    assert_eq!(perm_bit(&a.label0), wire_a_lsb0);
                    assert_eq!(perm_bit(&b.label0), wire_b_lsb0);

                    assert_eq!(perm_bit(&a.label1), !wire_a_lsb0);
                    assert_eq!(perm_bit(&b.label1), !wire_b_lsb0);

                    let (ct, c) = garble(GATE_ID, gt, &a, &b, &delta);
                    let c = GarbledWire::new(c, c ^ &delta);

                    for (a_vl, b_vl) in TEST_CASES {
                        let evaluated = degarble(
                            GATE_ID,
                            gt,
                            &ct,
                            &EvaluatedWire::new_from_garbled(&a, a_vl),
                            &EvaluatedWire::new_from_garbled(&b, b_vl),
                        );

                        let expected =
                            EvaluatedWire::new_from_garbled(&c, (gt.f())(a_vl, b_vl)).active_label;

                        if evaluated != expected {
                            failed_cases.push(FailedCase {
                                wire_a_lsb0,
                                wire_b_lsb0,
                                c: c.clone(),
                                a_value: a_vl,
                                b_value: b_vl,
                                c_value: (gt.f())(a_vl, b_vl),
                                evaluated,
                                expected,
                            });
                        }
                    }
                }
            }

            // Create bitmask visualization (16 cases total: 2×2×4)
            let mut bitmask = String::with_capacity(16);

            for wire_a_lsb0 in [false, true] {
                for wire_b_lsb0 in [false, true] {
                    for (a_vl, b_vl) in TEST_CASES {
                        let failed = failed_cases.iter().any(|fc| {
                            fc.wire_a_lsb0 == wire_a_lsb0
                                && fc.wire_b_lsb0 == wire_b_lsb0
                                && fc.a_value == a_vl
                                && fc.b_value == b_vl
                        });
                        bitmask.push(if failed { '0' } else { '1' });
                    }
                }
            }

            let mut error = String::new();
            error.push_str(&format!("{:?}\n", gt.alphas()));
            error.push_str(&format!(
                "Bitmask: {} ({}/16 failed)\n",
                bitmask,
                failed_cases.len()
            ));
            error.push_str("Order: wire_a_lsb0,wire_b_lsb0,a_value,b_value\n");
            for case in failed_cases.iter() {
                error.push_str(&format!("{case:#?}\n"));
            }

            assert_eq!(&failed_cases, &[], "{error}");
        }

        macro_rules! garble_consistency_tests {
        ($($gate_type:ident => $test_name:ident),*) => {
            $(
                #[test]
                fn $test_name() {
                    garble_consistency(GateType::$gate_type);
                }
            )*
        };
    }

        garble_consistency_tests!(
            And => garble_consistency_and,
            Nand => garble_consistency_nand,
            Nimp => garble_consistency_nimp,
            Imp => garble_consistency_imp,
            Ncimp => garble_consistency_ncimp,
            Cimp => garble_consistency_cimp,
            Nor => garble_consistency_nor,
            Or => garble_consistency_or
        );
    }
}
use garbling::{degarble, garble};

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::*;

    const GATE_ID: GateId = 0;

    const TEST_CASES: [(bool, bool); 4] =
        [(false, false), (false, true), (true, false), (true, true)];

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
            .garble(GATE_ID, &mut wires, &delta)
            .expect("Garbling should succeed")
            .map(|row| vec![row])
            .unwrap_or_default();

        let wire_a_garbled = wires.get(gate.wire_a).expect("Wire A should exist");
        let wire_b_garbled = wires.get(gate.wire_b).expect("Wire B should exist");
        let wire_c_garbled = wires.get(gate.wire_c).expect("Wire C should exist");

        for (input_a, input_b) in TEST_CASES {
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
                GATE_ID,
                &|wire_id: WireId| evaluations.get(&wire_id),
                &table,
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
            .garble(GATE_ID, &mut wires, &delta)
            .expect("Garbling should succeed")
            .map(|row| vec![row])
            .unwrap_or_default();

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
                GATE_ID,
                &|wire_id: WireId| evaluations.get(&wire_id),
                &table,
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
        let mut wire_a = WireId(0);
        let gate = Gate::not(&mut wire_a);
        test_not_gate_e2e(gate);
    }
}
