use std::array;

use super::Circuit;
use crate::{Gate, GateType, WireId};

impl Circuit {
    pub fn half_adder(&mut self, a: WireId, b: WireId) -> (WireId, WireId) {
        let result = self.issue_wire();
        let carry = self.issue_wire();

        self.add_gate(Gate::new(GateType::Xor, a, b, result));
        self.add_gate(Gate::new(GateType::And, a, b, carry));

        (result, carry)
    }

    pub fn full_adder(&mut self, a: WireId, b: WireId, c: WireId) -> (WireId, WireId) {
        let [axc, bxc, result, t, carry] = array::from_fn(|_| self.issue_wire());

        self.add_gate(Gate::new(GateType::Xor, a, c, axc));
        self.add_gate(Gate::new(GateType::Xor, b, c, bxc));
        self.add_gate(Gate::new(GateType::Xor, a, bxc, result));
        self.add_gate(Gate::new(GateType::And, axc, bxc, t));
        self.add_gate(Gate::new(GateType::Xor, c, t, carry));

        (result, carry)
    }

    pub fn half_subtracter(&mut self, a: WireId, b: WireId) -> (WireId, WireId) {
        let result = self.issue_wire();
        let borrow = self.issue_wire();

        self.add_gate(Gate::new(GateType::Xor, a, b, result));
        self.add_gate(Gate::and_variant(a, b, borrow, [true, false, false]));

        (result, borrow)
    }

    pub fn full_subtracter(&mut self, a: WireId, b: WireId, c: WireId) -> (WireId, WireId) {
        let [bxa, bxc, result, t, carry] = array::from_fn(|_| self.issue_wire());

        self.add_gate(Gate::new(GateType::Xor, a, b, bxa));
        self.add_gate(Gate::new(GateType::Xor, b, c, bxc));
        self.add_gate(Gate::new(GateType::Xor, bxa, c, result));
        self.add_gate(Gate::new(GateType::And, bxa, bxc, t));
        self.add_gate(Gate::new(GateType::Xor, c, t, carry));

        (result, carry)
    }

    pub fn selector(&mut self, a: WireId, b: WireId, c: WireId) -> WireId {
        let [d, f, g] = array::from_fn(|_| self.issue_wire());

        self.add_gate(Gate::new(GateType::Nand, a, c, d));
        self.add_gate(Gate::and_variant(c, b, f, [true, false, true]));
        self.add_gate(Gate::new(GateType::Nand, d, f, g));

        g
    }

    pub fn multiplexer(&mut self, a: &[WireId], s: &[WireId], w: usize) -> WireId {
        let n = 2_usize.pow(w.try_into().unwrap());
        assert_eq!(a.len(), n);
        assert_eq!(s.len(), w);

        if w == 1 {
            return self.selector(a[1], a[0], s[0]);
        }

        let a1 = &a[0..(n / 2)];
        let a2 = &a[(n / 2)..n];
        let su = &s[0..w - 1];
        let sv = s[w - 1];

        let b1 = self.multiplexer(a1, su, w - 1);
        let b2 = self.multiplexer(a2, su, w - 1);

        self.selector(b2, b1, sv)
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::*;
    use log::debug;

    #[test]
    fn test_half_adder() {
        let result = [
            ((false, false), (false, false)),
            ((false, true), (true, false)),
            ((true, false), (true, false)),
            ((true, true), (false, true)),
        ];

        for ((a, b), (c, d)) in result {
            let mut circuit = Circuit::default();

            let a_wire = circuit.issue_input_wire();
            let b_wire = circuit.issue_input_wire();

            let (result_wire, carry_wire) = circuit.half_adder(a_wire, b_wire);
            circuit.make_wire_output(result_wire);
            circuit.make_wire_output(carry_wire);

            circuit
                .garble()
                .unwrap()
                .evaluate(|id| {
                    if id == a_wire {
                        Some(a)
                    } else if id == b_wire {
                        Some(b)
                    } else {
                        None
                    }
                })
                .unwrap()
                .for_each(|res| {
                    let (wire_id, value) = res.unwrap();
                    if wire_id == result_wire {
                        assert_eq!(value, c);
                    } else if wire_id == carry_wire {
                        assert_eq!(value, d);
                    } else {
                        unreachable!("no output Wire like that {wire_id}")
                    }
                });
        }
    }

    #[test]
    fn test_full_adder() {
        let result = [
            ((false, false, false), (false, false)),
            ((false, false, true), (true, false)),
            ((false, true, false), (true, false)),
            ((false, true, true), (false, true)),
            ((true, false, false), (true, false)),
            ((true, false, true), (false, true)),
            ((true, true, false), (false, true)),
            ((true, true, true), (true, true)),
        ];

        for ((a, b, c), (d, e)) in result {
            let mut circuit = Circuit::default();

            let a_wire = circuit.issue_input_wire();
            let b_wire = circuit.issue_input_wire();
            let c_wire = circuit.issue_input_wire();

            let (result_wire, carry_wire) = circuit.full_adder(a_wire, b_wire, c_wire);
            circuit.make_wire_output(result_wire);
            circuit.make_wire_output(carry_wire);

            let input = [(a_wire, a), (b_wire, b), (c_wire, c)]
                .into_iter()
                .collect::<HashMap<WireId, bool>>();
            circuit
                .garble()
                .unwrap()
                .evaluate(|id| input.get(&id).copied())
                .unwrap()
                .for_each(|res| {
                    let (wire_id, value) = res.unwrap();
                    if wire_id == result_wire {
                        assert_eq!(value, d);
                    } else if wire_id == carry_wire {
                        assert_eq!(value, e);
                    } else {
                        unreachable!("no output Wire like that {wire_id}")
                    }
                });
        }
    }

    #[test]
    fn test_half_subtracter() {
        let result = [
            ((false, false), (false, false)),
            ((false, true), (true, true)),
            ((true, false), (true, false)),
            ((true, true), (false, false)),
        ];

        for ((a, b), (c, d)) in result {
            let mut circuit = Circuit::default();

            let a_wire = circuit.issue_input_wire();
            let b_wire = circuit.issue_input_wire();

            let (result_wire, borrow_wire) = circuit.half_subtracter(a_wire, b_wire);
            circuit.make_wire_output(result_wire);
            circuit.make_wire_output(borrow_wire);

            circuit
                .garble()
                .unwrap()
                .evaluate(|id| id.eq(&a_wire).then_some(a).or(id.eq(&b_wire).then_some(b)))
                .unwrap()
                .for_each(|res| {
                    let (wire_id, value) = res.unwrap();
                    if wire_id == result_wire {
                        assert_eq!(value, c);
                    } else if wire_id == borrow_wire {
                        assert_eq!(value, d);
                    } else {
                        unreachable!("no output Wire like that {wire_id}")
                    }
                });
        }
    }

    #[test]
    fn test_full_subtracter() {
        let result = [
            ((false, false, false), (false, false)),
            ((false, false, true), (true, true)),
            ((false, true, false), (true, true)),
            ((false, true, true), (false, true)),
            ((true, false, false), (true, false)),
            ((true, false, true), (false, false)),
            ((true, true, false), (false, false)),
            ((true, true, true), (true, true)),
        ];

        for ((a, b, c), (d, e)) in result {
            let mut circuit = Circuit::default();

            let a_wire = circuit.issue_input_wire();
            let b_wire = circuit.issue_input_wire();
            let c_wire = circuit.issue_input_wire();

            let (result_wire, carry_wire) = circuit.full_subtracter(a_wire, b_wire, c_wire);
            circuit.make_wire_output(result_wire);
            circuit.make_wire_output(carry_wire);

            let input = [(a_wire, a), (b_wire, b), (c_wire, c)]
                .into_iter()
                .collect::<HashMap<WireId, bool>>();
            circuit
                .garble()
                .unwrap()
                .evaluate(|id| input.get(&id).copied())
                .unwrap()
                .for_each(|res| {
                    let (wire_id, value) = res.unwrap();
                    if wire_id == result_wire {
                        assert_eq!(value, d);
                    } else if wire_id == carry_wire {
                        assert_eq!(value, e);
                    } else {
                        unreachable!("no output Wire like that {wire_id}")
                    }
                });
        }
    }

    #[test]
    fn test_selector() {
        let result = [
            ((false, false, false), false),
            ((false, false, true), false),
            ((false, true, false), true),
            ((false, true, true), false),
            ((true, false, false), false),
            ((true, false, true), true),
            ((true, true, false), true),
            ((true, true, true), true),
        ];

        for ((a, b, c), d) in result {
            let mut circuit = Circuit::default();

            let a_wire = circuit.issue_input_wire();
            let b_wire = circuit.issue_input_wire();
            let c_wire = circuit.issue_input_wire();

            let result_wire = circuit.selector(a_wire, b_wire, c_wire);
            circuit.make_wire_output(result_wire);

            let input = [(a_wire, a), (b_wire, b), (c_wire, c)]
                .into_iter()
                .collect::<HashMap<WireId, bool>>();
            circuit
                .garble()
                .unwrap()
                .evaluate(|id| input.get(&id).copied())
                .unwrap()
                .for_each(|res| {
                    let (wire_id, value) = res.unwrap();
                    if wire_id == result_wire {
                        assert_eq!(value, d);
                    } else {
                        unreachable!("no output Wire like that {wire_id}")
                    }
                });
        }
    }

    #[test]
    fn test_multiplexer() {
        use rand::Rng;
        let mut rng = rand::rng();

        let w = 3;
        let n = 2_usize.pow(w as u32);

        let mut circuit = Circuit::default();

        let a: Vec<WireId> = (0..n).map(|_| circuit.issue_input_wire()).collect();
        let s: Vec<WireId> = (0..w).map(|_| circuit.issue_input_wire()).collect();

        let a_values: Vec<bool> = (0..n).map(|_| rng.random()).collect();
        let s_values: Vec<bool> = (0..w).map(|_| rng.random()).collect();

        let mut u = 0;
        for &value in s_values.iter().rev() {
            u = u * 2 + if value { 1 } else { 0 };
        }

        let result_wire = circuit.multiplexer(&a, &s, w);
        circuit.make_wire_output(result_wire);

        let mut input = HashMap::new();
        for (i, &wire) in a.iter().enumerate() {
            input.insert(wire, a_values[i]);
        }
        for (i, &wire) in s.iter().enumerate() {
            input.insert(wire, s_values[i]);
        }

        circuit
            .garble()
            .unwrap()
            .evaluate(|id| input.get(&id).copied())
            .unwrap()
            .for_each(|res| {
                let (wire_id, value) = res.unwrap();
                if wire_id == result_wire {
                    assert_eq!(value, a_values[u]);
                } else {
                    unreachable!("no output Wire like that {wire_id}")
                }
            });
    }

    #[test]
    fn xnor_connection_test() {
        let mut circuit = Circuit::default();

        let a_wire = circuit.issue_input_wire();
        let b_wire = circuit.issue_input_wire();

        let not_a_wire = circuit.issue_wire();
        let not_a_and_b = circuit.issue_wire();
        debug!(
            "\n            a_wire = {a_wire:?},\n            b_wire = {b_wire:?},\n            not_a_wire = {not_a_wire:?},\n            not_a_and_b = {not_a_and_b:?}\n        "
        );

        circuit.add_gate(Gate::not(a_wire, not_a_wire));
        circuit.add_gate(Gate::and(not_a_wire, b_wire, not_a_and_b));

        circuit.make_wire_output(not_a_wire);
        circuit.make_wire_output(not_a_and_b);

        circuit
            .garble()
            .unwrap()
            .evaluate(|id| {
                if id == a_wire {
                    Some(true)
                } else if id == b_wire {
                    Some(false)
                } else {
                    None
                }
            })
            .unwrap()
            .for_each(|res| debug!("{:?}", res));
    }
}
