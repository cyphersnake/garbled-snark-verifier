use crate::bag::*;

impl Circuit {
    /// TODO Normal Doc
    /// Return (result, carry)
    pub fn half_adder(&mut self, a: WireId, b: WireId) -> (WireId, WireId) {
        let result = self.add_wire();
        let carry = self.add_wire();

        self.add(Gate::xor(a.clone(), b.clone(), result.clone()));
        self.add(Gate::and(a.clone(), b.clone(), carry.clone()));

        (result, carry)
    }

    pub fn full_adder(&mut self, a: WireId, b: WireId, c: WireId) -> (WireId, WireId) {
        let ab_xor = self.add_wire(); // d = a ⊕ b
        let ab_and = self.add_wire(); // e = a ∧ b
        let sum = self.add_wire(); // result = (a ⊕ b) ⊕ c
        let d_c_and = self.add_wire(); // f = (a ⊕ b) ∧ c
        let carry = self.add_wire(); // carry = (a ∧ b) ∨ ((a ⊕ b) ∧ c)

        // Gates
        self.add(Gate::xor(a.clone(), b.clone(), ab_xor.clone())); // a ⊕ b
        self.add(Gate::and(a.clone(), b.clone(), ab_and.clone())); // a ∧ b
        self.add(Gate::xor(ab_xor.clone(), c.clone(), sum.clone())); // (a ⊕ b) ⊕ c
        self.add(Gate::and(ab_xor.clone(), c.clone(), d_c_and.clone())); // (a ⊕ b) ∧ c
        self.add(Gate::xor(ab_and.clone(), d_c_and.clone(), carry.clone())); // carry = e ⊕ f (use XOR instead of OR)

        (sum, carry)
    }

    pub fn half_subtracter(&mut self, a: WireId, b: WireId) -> WireId {
        let result = self.add_wire();
        let borrow = self.add_wire();
        let not_a = self.add_wire();

        let gate_not_a = Gate::not(a.clone(), not_a.clone());
        let gate_result = Gate::xor(a.clone(), b.clone(), result.clone());
        let gate_borrow = Gate::and(not_a.clone(), b.clone(), borrow.clone());

        self.add(gate_not_a);
        self.add(gate_result);
        self.add(gate_borrow);

        result
    }

    pub fn full_subtracter(&mut self, a: WireId, b: WireId, c: WireId) {
        let d = self.add_wire();
        let e = self.add_wire();
        let f = self.add_wire();
        let g = self.add_wire();
        let h = self.add_wire();
        let result = self.add_wire();
        let borrow = self.add_wire();

        self.add(Gate::xor(a.clone(), b.clone(), d.clone()));
        self.add(Gate::xor(c.clone(), d.clone(), result.clone()));
        self.add(Gate::not(d.clone(), e.clone()));
        self.add(Gate::and(c.clone(), e.clone(), f.clone()));
        self.add(Gate::not(a.clone(), g.clone()));
        self.add(Gate::and(b.clone(), g.clone(), h.clone()));
        self.add(Gate::xor(f.clone(), h.clone(), borrow.clone()));
    }

    pub fn selector(&mut self, a: WireId, b: WireId, c: WireId) -> WireId {
        let d = self.add_wire();
        let e = self.add_wire();
        let f = self.add_wire();
        let g = self.add_wire();

        self.add(Gate::not(c.clone(), e.clone()));
        self.add(Gate::nand(a.clone(), c.clone(), d.clone()));
        self.add(Gate::nand(e.clone(), b.clone(), f.clone()));
        self.add(Gate::nand(d.clone(), f.clone(), g.clone()));

        g
    }

    pub fn multiplexer(&mut self, a: &[WireId], s: &[WireId], w: usize) -> Vec<WireId> {
        let n = 2_usize.pow(w.try_into().unwrap());
        assert_eq!(a.len(), n);
        assert_eq!(s.len(), w);

        if w == 1 {
            return vec![self.selector(a[1], a[0], s[0])];
        }

        let mut circuit = Circuit::default();

        let a1 = &a[0..(n / 2)];
        let a2 = &a[(n / 2)..n];
        let su = &s[0..w - 1];
        let sv = s[w - 1].clone();

        let b1 = self.multiplexer(a1, su, w - 1)[0].clone();
        let b2 = self.multiplexer(a2, su, w - 1)[0].clone();

        let b = self.selector(b2, b1, sv).clone();

        vec![b]
    }
}

#[cfg(test)]
mod tests {
    use rand::{rng, Rng};

    use crate::{
        bag::*,
        circuits::basic::{
            full_adder, full_subtracter, half_adder, half_subtracter, multiplexer, selector,
        },
    };

    #[test]
    fn test_half_adder() {
        let result = [
            ((false, false), (false, false)),
            ((false, true), (true, false)),
            ((true, false), (true, false)),
            ((true, true), (false, true)),
        ];

        for ((a, b), (c, d)) in result {
            let a_wire = self.add_wire_with(a);

            let b_wire = self.add_wire_with(b);

            let circuit = half_adder(a_wire, b_wire);

            for mut gate in circuit.1 {
                gate.evaluate();
            }

            let (c_wire, d_wire) = (circuit.0[0].clone(), circuit.0[1].clone());

            assert_eq!(c_wire.borrow().get_value(), c);
            assert_eq!(d_wire.borrow().get_value(), d);
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
            let a_wire = self.add_wire_with(a);

            let b_wire = self.add_wire_with(b);

            let c_wire = self.add_wire_with(c);

            let circuit = full_adder(a_wire, b_wire, c_wire);

            for mut gate in circuit.1 {
                gate.evaluate();
            }

            let (d_wire, e_wire) = (circuit.0[0].clone(), circuit.0[1].clone());

            assert_eq!(d_wire.borrow().get_value(), d);
            assert_eq!(e_wire.borrow().get_value(), e);
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
            let a_wire = self.add_wire_with(a);

            let b_wire = self.add_wire_with(b);

            let circuit = half_subtracter(a_wire, b_wire);

            for mut gate in circuit.1 {
                gate.evaluate();
            }

            let (c_wire, d_wire) = (circuit.0[0].clone(), circuit.0[1].clone());

            assert_eq!(c_wire.borrow().get_value(), c);
            assert_eq!(d_wire.borrow().get_value(), d);
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
            let a_wire = self.add_wire_with(a);

            let b_wire = self.add_wire_with(b);

            let c_wire = self.add_wire_with(c);

            let circuit = full_subtracter(a_wire, b_wire, c_wire);

            for mut gate in circuit.1 {
                gate.evaluate();
            }

            let (d_wire, e_wire) = (circuit.0[0].clone(), circuit.0[1].clone());

            assert_eq!(d_wire.borrow().get_value(), d);
            assert_eq!(e_wire.borrow().get_value(), e);
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
            let a_wire = self.add_wire_with(a);

            let b_wire = self.add_wire_with(b);

            let c_wire = self.add_wire_with(c);

            let circuit = selector(a_wire, b_wire, c_wire);

            for mut gate in circuit.1 {
                gate.evaluate();
            }

            let d_wire = circuit.0[0].clone();

            assert_eq!(d_wire.borrow().get_value(), d);
        }
    }

    #[test]
    fn test_multiplexer() {
        let w = 5;
        let n = 2_usize.pow(w as u32);
        let a: Wires = (0..n).map(|_| self.add_wire()).collect();
        let s: Wires = (0..w).map(|_| self.add_wire()).collect();

        for wire in a.iter() {
            wire.borrow_mut().set(rng().random());
        }

        let mut u = 0;
        for wire in s.iter().rev() {
            let x = rng().random();
            u = u + u + if x { 1 } else { 0 };
            wire.borrow_mut().set(x);
        }

        let circuit = multiplexer(a.clone(), s.clone(), w);
        circuit.gate_counts().print();

        for mut gate in circuit.1 {
            gate.evaluate();
        }

        let result = circuit.0[0].clone().borrow().get_value();
        let expected = a[u].clone().borrow().get_value();

        assert_eq!(result, expected);
    }
}
