use num_bigint::BigUint;

use super::BigIntWires;
use crate::{circuit::u256::bits_from_biguint_with_len, Circuit, Gate, WireId};

pub fn self_or_zero_generic(circuit: &mut Circuit, a: &[WireId], s: WireId) -> Vec<WireId> {
    a.iter()
        .map(|a_i| {
            let w = circuit.issue_wire();
            circuit.add_gate(Gate::and(*a_i, s, w));
            w
        })
        .collect()
}

//s is inverted
pub fn self_or_zero_inv_generic(circuit: &mut Circuit, a: &[WireId], s: WireId) -> Vec<WireId> {
    a.iter()
        .map(|a_i| {
            let w = circuit.issue_wire();
            circuit.add_gate(Gate::and_variant(*a_i, s, w, [false, true, false]));
            w
        })
        .collect()
}

pub fn equal(circuit: &mut Circuit, a: &BigIntWires, b: &BigIntWires) -> WireId {
    assert_eq!(a.len(), b.len());

    let xor_bits = a
        .iter()
        .zip(b.iter())
        .map(|(a_i, b_i)| {
            let c_i = circuit.issue_wire();
            circuit.add_gate(Gate::xor(*a_i, *b_i, c_i));
            c_i
        })
        .collect::<Vec<_>>();

    equal_constant(circuit, &BigIntWires { bits: xor_bits }, &BigUint::ZERO)
}

pub fn equal_constant(circuit: &mut Circuit, a: &BigIntWires, b: &BigUint) -> WireId {
    if b == &BigUint::ZERO {
        return equal_zero(circuit, a);
    }

    let b_bits = bits_from_biguint_with_len(b, a.len()).unwrap();
    let one_ind = b_bits.first_one().unwrap();

    let mut res = a.bits[one_ind];
    a.iter().enumerate().for_each(|(i, a_i)| {
        if i == one_ind {
            return;
        }
        let new_res = circuit.issue_wire();
        circuit.add_gate(Gate::and_variant(
            *a_i,
            res,
            new_res,
            [!b_bits[i], false, false],
        ));
        res = new_res;
    });

    res
}

pub fn equal_zero(circuit: &mut Circuit, a: &BigIntWires) -> WireId {
    if a.len() == 1 {
        let is_bit_zero = circuit.issue_wire();
        circuit.add_gate(Gate::not(a.bits[0], is_bit_zero));
        return is_bit_zero;
    }

    let mut res = circuit.issue_wire();
    circuit.add_gate(Gate::xnor(a.bits[0], a.bits[1], res));

    a.iter().skip(1).for_each(|a_i| {
        let next_res = circuit.issue_wire();
        circuit.add_gate(Gate::and_variant(*a_i, res, next_res, [true, false, false]));
        res = next_res;
    });
    res
}

pub fn greater_than(circuit: &mut Circuit, a: &BigIntWires, b: &BigIntWires) -> WireId {
    let not_b = BigIntWires {
        bits: b
            .iter()
            .map(|b_i| {
                let not_b_i = circuit.issue_wire();
                circuit.add_gate(Gate::not(*b_i, not_b_i));
                not_b_i
            })
            .collect(),
    };

    let sum = super::add_generic(circuit, a, &not_b);
    sum.bits.last().copied().unwrap()
}

pub fn less_than_constant(circuit: &mut Circuit, a: &BigIntWires, b: &BigUint) -> WireId {
    let not_a = BigIntWires {
        bits: a
            .iter()
            .map(|a_i| {
                let not_a_i = circuit.issue_wire();
                circuit.add_gate(Gate::not(*a_i, not_a_i));
                not_a_i
            })
            .collect(),
    };

    let sum = super::add_constant_generic(circuit, &not_a, b);
    sum.bits.last().copied().unwrap()
}

pub fn select(circuit: &mut Circuit, a: &BigIntWires, b: &BigIntWires, s: WireId) -> BigIntWires {
    assert_eq!(a.len(), b.len());

    BigIntWires {
        bits: a
            .iter()
            .zip(b.iter())
            .map(|(a_i, b_i)| circuit.selector(*a_i, *b_i, s))
            .collect(),
    }
}

pub fn multiplexer(
    circuit: &mut Circuit,
    a: Vec<BigIntWires>,
    s: Vec<WireId>,
    w: usize,
) -> BigIntWires {
    let n = 2_usize.pow(w as u32);
    assert_eq!(a.len(), n);
    let n_bits = a.first().map(|a_i| a_i.len()).unwrap();
    assert!(
        a.iter().skip(1).all(|a_i| a_i.len() == n_bits),
        "not all a consisten: {a:?}"
    );

    BigIntWires {
        bits: (0..n_bits)
            .map(|i| {
                let ith_wires = a.iter().map(|a_i| a_i.bits[i]).collect::<Vec<_>>();
                circuit.multiplexer(&ith_wires, &s, w)
            })
            .collect(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_comparison_operation(
        n_bits: usize,
        a_val: u64,
        b_val: u64,
        expected: bool,
        operation: impl FnOnce(&mut Circuit, &BigIntWires, &BigIntWires) -> WireId,
    ) {
        let mut circuit = Circuit::default();
        let a = BigIntWires::new(&mut circuit, n_bits, true, false);
        let b = BigIntWires::new(&mut circuit, n_bits, true, false);
        let result = operation(&mut circuit, &a, &b);

        circuit.make_wire_output(result);

        let a_big = BigUint::from(a_val);
        let b_big = BigUint::from(b_val);

        let a_input = a.get_wire_bits_fn(&a_big).unwrap();
        let b_input = b.get_wire_bits_fn(&b_big).unwrap();

        let output = circuit
            .garble()
            .unwrap()
            .evaluate(|id| a_input(id).or_else(|| b_input(id)))
            .unwrap()
            .find(|r| r.as_ref().unwrap().0 == result)
            .unwrap()
            .unwrap()
            .1;

        assert_eq!(output, expected);
    }

    fn test_constant_comparison_operation(
        n_bits: usize,
        a_val: u64,
        b_val: u64,
        expected: bool,
        operation: impl FnOnce(&mut Circuit, &BigIntWires, &BigUint) -> WireId,
    ) {
        let mut circuit = Circuit::default();
        let a = BigIntWires::new(&mut circuit, n_bits, true, false);
        let b_big = BigUint::from(b_val);
        let result = operation(&mut circuit, &a, &b_big);

        circuit.make_wire_output(result);

        let a_big = BigUint::from(a_val);
        let a_input = a.get_wire_bits_fn(&a_big).unwrap();

        let output = circuit
            .garble()
            .unwrap()
            .evaluate(a_input)
            .unwrap()
            .find(|r| r.as_ref().unwrap().0 == result)
            .unwrap()
            .unwrap()
            .1;

        assert_eq!(output, expected);
    }

    fn test_select_operation(n_bits: usize, a_val: u64, b_val: u64, selector: bool, expected: u64) {
        let mut circuit = Circuit::default();

        let a = BigIntWires::new(&mut circuit, n_bits, true, false);
        let b = BigIntWires::new(&mut circuit, n_bits, true, false);

        let s = circuit.issue_wire();

        let a_big = BigUint::from(a_val);
        let b_big = BigUint::from(b_val);
        let expected_bn = BigUint::from(expected);

        let result = select(&mut circuit, &a, &b, s);

        let a_input = a.get_wire_bits_fn(&a_big).unwrap();
        let b_input = b.get_wire_bits_fn(&b_big).unwrap();
        let result_output = result.get_wire_bits_fn(&expected_bn).unwrap();

        result.bits.iter().for_each(|bit| {
            circuit.make_wire_output(*bit);
        });

        let (actual, expected): (Vec<_>, Vec<_>) = circuit
            .garble()
            .unwrap()
            .evaluate(|id| {
                if id == s {
                    Some(selector)
                } else {
                    a_input(id).or_else(|| b_input(id))
                }
            })
            .unwrap()
            .map(|r| r.unwrap())
            .filter(|(wire_id, _)| result.bits.contains(wire_id))
            .map(|(wire_id, actual)| (actual, result_output(wire_id).unwrap()))
            .unzip();

        assert_eq!(actual, expected);
    }

    const NUM_BITS: usize = 4;

    #[test]
    fn test_equal_same_values() {
        test_comparison_operation(NUM_BITS, 5, 5, true, equal);
    }

    #[test]
    fn test_equal_different_values() {
        test_comparison_operation(NUM_BITS, 5, 3, false, equal);
    }

    #[test]
    fn test_equal_zero_zero() {
        test_comparison_operation(NUM_BITS, 0, 0, true, equal);
    }

    #[test]
    fn test_equal_constant_same() {
        test_constant_comparison_operation(NUM_BITS, 5, 5, true, equal_constant);
    }

    #[test]
    fn test_equal_constant_different() {
        test_constant_comparison_operation(NUM_BITS, 5, 3, false, equal_constant);
    }

    #[test]
    fn test_equal_constant_zero() {
        test_constant_comparison_operation(NUM_BITS, 0, 0, true, equal_constant);
    }

    fn test_greater_than_operation(n_bits: usize, a_val: u64, b_val: u64, expected: bool) {
        let mut circuit = Circuit::default();
        let a = BigIntWires::new(&mut circuit, n_bits, true, false);
        let b = BigIntWires::new(&mut circuit, n_bits, true, false);

        let a_big = BigUint::from(a_val);
        let b_big = BigUint::from(b_val);

        let a_input = a.get_wire_bits_fn(&a_big).unwrap();
        let b_input = b.get_wire_bits_fn(&b_big).unwrap();

        let result = greater_than(&mut circuit, &a, &b);

        circuit.make_wire_output(result);

        let output = circuit
            .garble()
            .unwrap()
            .evaluate(|id| a_input(id).or_else(|| b_input(id)))
            .unwrap()
            .find(|r| r.as_ref().unwrap().0 == result)
            .unwrap()
            .unwrap()
            .1;

        assert_eq!(output, expected);
    }

    #[test]
    fn test_greater_than_true() {
        test_greater_than_operation(NUM_BITS, 8, 3, true);
    }

    #[test]
    fn test_greater_than_false() {
        test_greater_than_operation(NUM_BITS, 3, 8, false);
    }

    #[test]
    fn test_greater_than_equal() {
        test_greater_than_operation(NUM_BITS, 5, 5, false);
    }

    #[test]
    fn test_less_than_constant_true() {
        test_constant_comparison_operation(NUM_BITS, 3, 8, true, less_than_constant);
    }

    #[test]
    fn test_less_than_constant_false() {
        test_constant_comparison_operation(NUM_BITS, 8, 3, false, less_than_constant);
    }

    #[test]
    fn test_less_than_constant_equal() {
        test_constant_comparison_operation(NUM_BITS, 5, 5, false, less_than_constant);
    }

    #[test]
    fn test_select_first() {
        test_select_operation(NUM_BITS, 5, 3, true, 5);
    }

    #[test]
    fn test_select_second() {
        test_select_operation(NUM_BITS, 5, 3, false, 3);
    }

    #[test]
    fn test_select_zero() {
        test_select_operation(NUM_BITS, 0, 7, true, 0);
    }
}
