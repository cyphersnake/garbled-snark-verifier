use std::iter;

use crate::{
    bag::*,
    core::gate::{GateCount, GateType},
};

#[derive(Clone, Debug, Default)]
pub struct Circuit {
    pub wires: Wires,
    pub gates: Vec<Gate>,
    pub gate_counts: GateCount,
}

impl Circuit {
    pub fn new(wires: Wires, gates: Vec<Gate>) -> Self {
        let mut gate_counts = GateCount::default();

        for gate in gates.iter() {
            match gate.gate_type {
                GateType::And => gate_counts.and += 1,
                GateType::Or => gate_counts.or += 1,
                GateType::Xor => gate_counts.xor += 1,
                GateType::Nand => gate_counts.nand += 1,
                GateType::Not => gate_counts.not += 1,
                GateType::Xnor => gate_counts.xnor += 1,
                GateType::Nimp => gate_counts.nimp += 1,
                GateType::Nsor => gate_counts.nsor += 1,
            }
        }

        Self {
            wires,
            gates,
            gate_counts,
        }
    }

    pub fn garbled_gates(&self) -> Vec<Vec<S>> {
        self.gates
            .iter()
            .map(|gate| gate.garbled(&self.wires))
            .collect()
    }

    pub fn extend(&mut self, circuit: Self) -> Wires {
        todo!("understand logic")
        //self.gates.extend(circuit.gates);
        //circuit.wires
    }

    pub fn add(&mut self, gate: Gate) {
        let gc = &mut self.gate_counts;
        match gate.gate_type {
            GateType::And => gc.and += 1,
            GateType::Or => gc.or += 1,
            GateType::Xor => gc.xor += 1,
            GateType::Nand => gc.nand += 1,
            GateType::Not => gc.not += 1,
            GateType::Xnor => gc.xnor += 1,
            GateType::Nimp => gc.nimp += 1,
            GateType::Nsor => gc.nsor += 1,
        }

        self.gates.push(gate);
    }

    pub fn add_wire(&mut self) -> WireId {
        self.wires.issue()
    }

    pub fn add_wires(&mut self, count: usize) -> Vec<WireId> {
        iter::repeat_with(|| self.wires.issue())
            .take(count)
            .collect()
    }

    pub fn gate_count(&self) -> usize {
        self.gates.len()
    }

    pub fn gate_counts(&self) -> &GateCount {
        &self.gate_counts
    }

    pub fn evaluate(&mut self) {
        for gate in self.gates.iter() {
            gate.evaluate(&mut self.wires);
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::core::{bristol::parser, s::S};
    use bitvm::bigint::U256;
    use bitvm::treepp::*;
    use rand::{rng, Rng};
    use serial_test::serial;
    use std::iter::zip;

    fn test_circuit(circuit_filename: &str, correct: bool) {
        println!("testing {:?}", circuit_filename);
        let (circuit, inputs, _outputs) = parser(circuit_filename);

        let mut garbled_gates = circuit.garbled_gates();
        let n = garbled_gates.len();

        if !correct {
            let u: u32 = rng().random();
            garbled_gates[(u as usize) % n] =
                vec![S::random(), S::random(), S::random(), S::random()];
        }

        for input in inputs {
            for input_wire in input {
                input_wire.borrow_mut().set(rng().random());
            }
        }

        println!(
            "testing {:?} garble",
            if correct { "correct" } else { "incorrect" }
        );

        for (i, (gate, garble)) in zip(circuit.1.clone(), garbled_gates).enumerate() {
            let a = gate.wire_a.borrow().get_label();
            let b = gate.wire_b.borrow().get_label();
            let bit_a = gate.wire_a.borrow().get_value();
            let bit_b = gate.wire_b.borrow().get_value();
            let bit_c = (gate.f())(bit_a, bit_b);
            let (garble_check, c) = gate.check_garble(garble.clone(), bit_c);
            let gate_script = gate.script(garble, garble_check);

            println!(
                "testing gate[{:?}], garble is {:?}",
                i,
                if garble_check { "correct" } else { "incorrect" }
            );

            let script = script! {
                { U256::push_hex(&hex::encode(a.0)) }
                { if bit_a {1} else {0} }
                { U256::push_hex(&hex::encode(b.0)) }
                { if bit_b {1} else {0} }
                { gate_script }
            };
            let result = execute_script(script);
            assert!(result.success);

            if garble_check {
                gate.wire_c.borrow_mut().set2(bit_c, c);
            } else {
                assert!(!correct);
                break;
            }
        }
    }

    fn test_circuit_find_incorrect(circuit_filename: &str, correct: bool) {
        println!("testing {:?}", circuit_filename);
        let (circuit, inputs, _outputs) = parser(circuit_filename);

        let mut garbled_gates = circuit.garbled_gates();
        let n = garbled_gates.len();

        if !correct {
            let u: u32 = rng().random();
            garbled_gates[(u as usize) % n] =
                vec![S::random(), S::random(), S::random(), S::random()];
        }

        for input in inputs {
            for input_wire in input {
                input_wire.borrow_mut().set(rng().random());
            }
        }

        println!(
            "testing {:?} garble",
            if correct { "correct" } else { "incorrect" }
        );

        for (i, (gate, garble)) in zip(circuit.1.clone(), garbled_gates).enumerate() {
            let a = gate.wire_a.borrow().get_label();
            let b = gate.wire_b.borrow().get_label();
            let bit_a = gate.wire_a.borrow().get_value();
            let bit_b = gate.wire_b.borrow().get_value();
            let bit_c = (gate.f())(bit_a, bit_b);
            let (garble_check, c) = gate.check_garble(garble.clone(), bit_c);

            println!(
                "testing gate[{:?}], garble is {:?}",
                i,
                if garble_check { "correct" } else { "incorrect" }
            );

            if garble_check {
                gate.wire_c.borrow_mut().set2(bit_c, c);
                continue;
            }
            assert!(!correct);

            let gate_script = gate.script(garble, garble_check);

            let script = script! {
                { U256::push_hex(&hex::encode(a.0)) }
                { if bit_a {1} else {0} }
                { U256::push_hex(&hex::encode(b.0)) }
                { if bit_b {1} else {0} }
                { gate_script }
            };
            let result = execute_script(script);
            assert!(result.success);

            break;
        }
    }

    #[test]
    #[serial]
    fn test_circuit_adder() {
        test_circuit("src/core/bristol-examples/adder64.txt", true);
        test_circuit("src/core/bristol-examples/adder64.txt", false);
    }

    #[test]
    #[serial]
    fn test_circuit_adder_find_incorrect() {
        test_circuit_find_incorrect("src/core/bristol-examples/adder64.txt", true);
        test_circuit_find_incorrect("src/core/bristol-examples/adder64.txt", false);
    }

    #[test]
    #[serial]
    #[ignore]
    fn test_circuit_subtracter() {
        test_circuit("src/core/bristol-examples/subtracter64.txt", true);
        test_circuit("src/core/bristol-examples/subtracter64.txt", false);
    }

    #[test]
    #[serial]
    #[ignore]
    fn test_circuit_subtracter_find_incorrect() {
        test_circuit_find_incorrect("src/core/bristol-examples/subtracter64.txt", true);
        test_circuit_find_incorrect("src/core/bristol-examples/subtracter64.txt", false);
    }

    #[test]
    #[serial]
    #[ignore]
    fn test_circuit_multiplier() {
        test_circuit("src/core/bristol-examples/multiplier64.txt", true);
        test_circuit("src/core/bristol-examples/multiplier64.txt", false);
    }

    #[test]
    #[serial]
    #[ignore]
    fn test_circuit_multiplier_find_incorrect() {
        test_circuit_find_incorrect("src/core/bristol-examples/multiplier64.txt", true);
        test_circuit_find_incorrect("src/core/bristol-examples/multiplier64.txt", false);
    }
}
