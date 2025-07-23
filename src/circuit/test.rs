#[cfg(test)]
mod finalization_consistency_tests {
    use std::collections::HashMap;

    use rand::SeedableRng;

    use crate::{Circuit, WireId};

    fn test_rng() -> rand::rngs::StdRng {
        rand::rngs::StdRng::from_seed([42u8; 32])
    }

    /// Creates a simple circuit with ~10 gates using basic operations
    /// Circuit: ((A & B) | (C ^ D)) & !(A | C)
    fn create_simple_10_gate_circuit() -> (Circuit, Vec<WireId>) {
        let mut circuit = Circuit::default();

        // 4 input wires
        let input_a = circuit.issue_input_wire(); // WireId(2)
        let input_b = circuit.issue_input_wire(); // WireId(3)
        let input_c = circuit.issue_input_wire(); // WireId(4)
        let input_d = circuit.issue_input_wire(); // WireId(5)

        // Intermediate wires for computation
        let and_ab = circuit.issue_wire(); // WireId(6) = A & B
        let xor_cd = circuit.issue_wire(); // WireId(7) = C ^ D
        let or_temp = circuit.issue_wire(); // WireId(8) = (A & B) | (C ^ D)
        let or_ac = circuit.issue_wire(); // WireId(9) = A | C
        let not_or_ac = circuit.issue_wire(); // WireId(10) = !(A | C)
        let final_out = circuit.issue_wire(); // WireId(11) = ((A & B) | (C ^ D)) & !(A | C)

        // Build the circuit: ((A & B) | (C ^ D)) & !(A | C)
        // Gate 1: A & B
        circuit.add_gate(crate::Gate::new(
            crate::GateType::And,
            input_a,
            input_b,
            and_ab,
        ));

        // Gate 2: C ^ D
        circuit.add_gate(crate::Gate::new(
            crate::GateType::Xor,
            input_c,
            input_d,
            xor_cd,
        ));

        // Gate 3: (A & B) | (C ^ D)
        circuit.add_gate(crate::Gate::new(
            crate::GateType::Or,
            and_ab,
            xor_cd,
            or_temp,
        ));

        // Gate 4: A | C
        circuit.add_gate(crate::Gate::new(
            crate::GateType::Or,
            input_a,
            input_c,
            or_ac,
        ));

        // Gate 5: !(A | C)
        circuit.add_gate(crate::Gate::new(
            crate::GateType::Nor,
            or_ac,
            or_ac,
            not_or_ac,
        ));

        // Gate 6: Final AND
        circuit.add_gate(crate::Gate::new(
            crate::GateType::And,
            or_temp,
            not_or_ac,
            final_out,
        ));

        // Make final output
        circuit.make_wire_output(final_out);

        (circuit, vec![input_a, input_b, input_c, input_d])
    }

    #[test]
    fn test_finalization_flow_consistency_simple_circuit() {
        let (circuit, inputs) = create_simple_10_gate_circuit();

        // Test all 16 combinations of 4 boolean inputs
        for a in [false, true] {
            for b in [false, true] {
                for c in [false, true] {
                    for d in [false, true] {
                        // Create input mapping
                        let input_map = [
                            (inputs[0], a), // input_a
                            (inputs[1], b), // input_b
                            (inputs[2], c), // input_c
                            (inputs[3], d), // input_d
                        ]
                        .into_iter()
                        .collect::<HashMap<_, _>>();

                        let get_input = |wire_id: WireId| input_map.get(&wire_id).copied();

                        // Create single garbled circuit to use for both flows
                        let garbled = circuit
                            .garble(&mut test_rng())
                            .expect("Garbling should succeed");

                        // Flow 1: Garbled -> Evaluated -> Finalized
                        let evaluated = garbled
                            .evaluate(get_input)
                            .expect("Evaluation should succeed");
                        let finalized_flow1 = evaluated.finalize();

                        // Flow 2: Garbled -> Finalized (direct) - using same garbled circuit
                        let finalized_flow2 = garbled
                            .finalize(get_input)
                            .expect("Direct finalization should succeed");

                        // Both flows should produce identical output commits
                        assert_eq!(
                            finalized_flow1.output_wires_commit,
                            finalized_flow2.output_wires_commit,
                            "Output commits should match for inputs a={a}, b={b}, c={c}, d={d}"
                        );

                        // Input wires should be identical
                        assert_eq!(
                            finalized_flow1.input_wires.len(),
                            finalized_flow2.input_wires.len(),
                            "Input wire counts should match for inputs a={a}, b={b}, c={c}, d={d}"
                        );

                        // Check each input wire matches exactly
                        let mut flow1_inputs = finalized_flow1.input_wires.clone();
                        let mut flow2_inputs = finalized_flow2.input_wires.clone();

                        // Sort by wire ID for consistent comparison
                        flow1_inputs.sort_by_key(|(wire_id, _)| wire_id.0);
                        flow2_inputs.sort_by_key(|(wire_id, _)| wire_id.0);

                        for ((wire_id1, eval_wire1), (wire_id2, eval_wire2)) in
                            flow1_inputs.iter().zip(flow2_inputs.iter())
                        {
                            assert_eq!(wire_id1, wire_id2, "Input wire IDs should match");
                            assert_eq!(
                                eval_wire1.value, eval_wire2.value,
                                "Input wire values should match for wire {wire_id1:?}"
                            );
                            assert_eq!(
                                eval_wire1.active_label, eval_wire2.active_label,
                                "Input wire labels should match for wire {wire_id1:?}"
                            );
                        }

                        // Garbled tables should be identical (same circuit, same randomness)
                        assert_eq!(
                            finalized_flow1.garbled_table, finalized_flow2.garbled_table,
                            "Garbled tables should be identical for inputs a={a}, b={b}, c={c}, d={d}"
                        );

                        // Both finalized circuits should pass verification
                        assert!(
                            finalized_flow1.check().is_ok(),
                            "Flow 1 finalized circuit should pass check for inputs a={a}, b={b}, c={c}, d={d}"
                        );

                        assert!(
                            finalized_flow2.check().is_ok(),
                            "Flow 2 finalized circuit should pass check for inputs a={a}, b={b}, c={c}, d={d}"
                        );

                        // Verify the computation is correct: ((A & B) | (C ^ D)) & !(A | C)
                        let expected = !a && (c ^ d) && !c;

                        let simple_outputs: Vec<_> = circuit
                            .simple_evaluate(get_input)
                            .expect("Simple evaluation should succeed")
                            .collect();

                        assert_eq!(simple_outputs.len(), 1, "Should have exactly one output");
                        assert_eq!(
                            simple_outputs[0].1, expected,
                            "Circuit output should match expected value for inputs a={a}, b={b}, c={c}, d={d}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn test_finalization_flow_consistency_multiplexer() {
        let mut circuit = Circuit::default();

        // Create a 2-to-1 multiplexer using basic gadgets
        let input_a = circuit.issue_input_wire();
        let input_b = circuit.issue_input_wire();
        let selector = circuit.issue_input_wire();

        // Build: selector ? input_a : input_b using selector gadget
        let output = circuit.selector(input_a, input_b, selector);
        circuit.make_wire_output(output);

        // Test all combinations
        for a in [false, true] {
            for b in [false, true] {
                for sel in [false, true] {
                    let input_map = [(input_a, a), (input_b, b), (selector, sel)]
                        .into_iter()
                        .collect::<HashMap<_, _>>();

                    let get_input = |wire_id: WireId| input_map.get(&wire_id).copied();

                    // Create single garbled circuit to use for both flows
                    let garbled = circuit
                        .garble(&mut test_rng())
                        .expect("Garbling should succeed");

                    // Flow 1: Garbled -> Evaluated -> Finalized
                    let evaluated = garbled
                        .evaluate(get_input)
                        .expect("Evaluation should succeed");
                    let finalized_flow1 = evaluated.finalize();

                    // Flow 2: Garbled -> Finalized (direct) - using same garbled circuit
                    let finalized_flow2 = garbled
                        .finalize(get_input)
                        .expect("Direct finalization should succeed");

                    // Verify consistency
                    assert_eq!(
                        finalized_flow1.output_wires_commit, finalized_flow2.output_wires_commit,
                        "Output commits should match for selector({a}, {b}, {sel})"
                    );

                    // Both should pass verification
                    assert!(finalized_flow1.check().is_ok());
                    assert!(finalized_flow2.check().is_ok());

                    // Verify correct computation: selector ? a : b
                    let expected = if sel { a } else { b };
                    let actual_outputs: Vec<_> = circuit
                        .simple_evaluate(get_input)
                        .expect("Simple evaluation should succeed")
                        .collect();

                    assert_eq!(actual_outputs.len(), 1);
                    assert_eq!(
                        actual_outputs[0].1, expected,
                        "Selector output should be {expected} for inputs a={a}, b={b}, sel={sel}"
                    );
                }
            }
        }
    }
}
