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

    let pb = perm_bit(&b.select(false));
    let pa = perm_bit(&a.select(false));

    // pre-compute both right-hashes
    let (ciphertext_evaluator, c_label_evaluator) = {
        let h_b0 = aes_hash(&b.select(false), gate_id);
        let h_b1 = aes_hash(&b.select(true), gate_id);

        // Wa^{αa}
        let w_a_alpha = a.select(alpha_a);

        let ct = h_b0 ^ &h_b1 ^ &w_a_alpha;

        let mut w = if pb { h_b1 } else { h_b0 };
        if (gate_type.f())(pa, pb) {
            w ^= delta;
        };

        (ct, w)
    };

    //let (ciphertext_garbler, c_label_garbler) = {
    //    let h_a0 = aes_hash(&a.select(false), gate_id);
    //    let h_a1 = aes_hash(&a.select(true), gate_id);
    //    let ct = if pb ^ alpha_a {
    //        h_a0 ^ &h_a1 ^ delta
    //    } else {
    //        h_a0 ^ &h_a1
    //    };
    //    let h_a = if pa { h_a1 } else { h_a0 };
    //    let w = match (gate_type.f())(pa, pb) {
    //        true => h_a ^ delta,
    //        false => h_a,
    //    };
    //    (ct, w)
    //};

    (ciphertext_evaluator, c_label_evaluator)
}

pub(super) fn degarble(
    gate_id: GateId,
    gate_type: GateType,
    ciphertext: &S,
    a: &EvaluatedWire,
    b: &EvaluatedWire,
) -> S {
    let h_b = aes_hash(&b.active_label, gate_id);

    let (alpha_a, alpha_b, alpha_c) = gate_type.alphas();

    if perm_bit(&b.active_label) {
        h_b ^ ciphertext ^ &a.active_label
    } else {
        h_b
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

        // Create bitmask visualization (16 cases total: 2×2×4)
        let mut bitmask = String::with_capacity(16);

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
                        bitmask.push('0');
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
                    } else {
                        bitmask.push('1');
                    }
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
