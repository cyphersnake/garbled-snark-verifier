use super::{GateId, GateType};
use crate::{Delta, EvaluatedWire, GarbledWire, S};

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

    let h_a0 = aes_hash(&a.select(alpha_a), gate_id);
    let h_a1 = aes_hash(&a.select(!alpha_a), gate_id);

    let ct = h_a0 ^ &h_a1 ^ &b.select(alpha_b);

    let w = if alpha_c { h_a0 ^ delta } else { h_a0 };

    (ct, w)
}

pub(super) fn degarble(
    gate_id: GateId,
    gate_type: GateType,
    ciphertext: &S,
    a: &EvaluatedWire,
    b: &EvaluatedWire,
) -> S {
    let h_a = aes_hash(&a.active_label, gate_id);

    let (alpha_a, _alpha_b, _alpha_c) = gate_type.alphas();

    if a.value() != alpha_a {
        ciphertext ^ &h_a ^ &b.active_label
    } else {
        h_a // h_a0
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
        let a = GarbledWire::new(a_label0, a_label0 ^ &delta);
        let b = GarbledWire::new(b_label0, b_label0 ^ &delta);

        // Test all combinations of LSB patterns for label0

        // Create bitmask visualization (16 cases total: 2×2×4)
        let mut bitmask = String::with_capacity(16);

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

            let expected = EvaluatedWire::new_from_garbled(&c, (gt.f())(a_vl, b_vl)).active_label;

            if evaluated != expected {
                bitmask.push('0');
                failed_cases.push(FailedCase {
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

        let mut error = String::new();
        error.push_str(&format!("{:?}\n", gt.alphas()));
        error.push_str(&format!(
            "Bitmask: {} ({}/4 failed)\n",
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
