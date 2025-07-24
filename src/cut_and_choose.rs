use rand::prelude::SliceRandom;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use std::sync::mpsc::{self, Receiver, Sender};

use crate::{Circuit, FinalizedCircuit};

/// Seeds for circuits that were not opened by Bob.
/// These will be used in the evaluation step (not implemented yet).
#[derive(Debug, Clone)]
pub struct EvalSeed {
    pub index: usize,
    pub seed: [u8; 32],
}

enum Message {
    Commits(Vec<Vec<u8>>),
    EvalIndices(Vec<usize>),
    Seeds(Vec<(usize, [u8; 32])>),
}

fn finalize_commit(gc: &FinalizedCircuit) -> Vec<u8> {
    gc.output_wires_commit.clone()
}

fn alice_party(
    circuit: Circuit,
    tx: Sender<Message>,
    rx: Receiver<Message>,
    total: usize,
    _eval: usize,
) -> Result<Vec<EvalSeed>, String> {
    let mut rng = StdRng::from_os_rng();
    let mut seeds = Vec::with_capacity(total);
    let mut commits = Vec::with_capacity(total);

    for _ in 0..total {
        let seed: [u8; 32] = rng.r#gen();
        seeds.push(seed);
        let mut srng = StdRng::from_seed(seed);
        let garbled = circuit
            .garble(&mut srng)
            .map_err(|e| format!("{e:?}"))?;
        let finalized = garbled
            .finalize(|_| Some(false))
            .map_err(|e| format!("{e:?}"))?;
        commits.push(finalize_commit(&finalized));
    }

    tx.send(Message::Commits(commits))
        .map_err(|e| e.to_string())?;

    let eval_indices = match rx.recv().map_err(|e| e.to_string())? {
        Message::EvalIndices(v) => v,
        _ => return Err("unexpected message".into()),
    };

    let seeds_to_send: Vec<(usize, [u8; 32])> = seeds
        .iter()
        .copied()
        .enumerate()
        .filter(|(i, _)| !eval_indices.contains(i))
        .collect();

    tx.send(Message::Seeds(seeds_to_send))
        .map_err(|e| e.to_string())?;

    let eval_seeds = seeds
        .into_iter()
        .enumerate()
        .filter(|(i, _)| eval_indices.contains(i))
        .map(|(i, s)| EvalSeed { index: i, seed: s })
        .collect();

    Ok(eval_seeds)
}

fn bob_party(
    circuit: Circuit,
    tx: Sender<Message>,
    rx: Receiver<Message>,
    total: usize,
    eval: usize,
) -> Result<(), String> {
    let commits = match rx.recv().map_err(|e| e.to_string())? {
        Message::Commits(c) => c,
        _ => return Err("unexpected message".into()),
    };

    if commits.len() != total {
        return Err("commit count mismatch".into());
    }

    let mut rng = StdRng::from_os_rng();
    let mut eval_indices: Vec<usize> = (0..total).collect();
    eval_indices.shuffle(&mut rng);
    eval_indices.truncate(eval);
    eval_indices.sort_unstable();

    tx.send(Message::EvalIndices(eval_indices.clone()))
        .map_err(|e| e.to_string())?;

    let seeds = match rx.recv().map_err(|e| e.to_string())? {
        Message::Seeds(s) => s,
        _ => return Err("unexpected message".into()),
    };

    for (i, seed) in seeds {
        let mut srng = StdRng::from_seed(seed);
        let garbled = circuit
            .garble(&mut srng)
            .map_err(|e| format!("{e:?}"))?;
        let finalized = garbled
            .finalize(|_| Some(false))
            .map_err(|e| format!("{e:?}"))?;
        if finalize_commit(&finalized) != commits[i] {
            return Err("commit mismatch".into());
        }
    }

    // Evaluation step will use the remaining seeds. Not implemented yet.
    Ok(())
}

/// Runs a simple cut-and-choose where Alice generates all circuits and Bob
/// checks a random subset. Returns the seeds of the unchecked circuits.
pub fn run_cut_and_choose(
    alice: Circuit,
    bob: Circuit,
    total: usize,
    eval: usize,
) -> Result<Vec<EvalSeed>, String> {
    let (tx_ab, rx_ab) = mpsc::channel();
    let (tx_ba, rx_ba) = mpsc::channel();

    let alice_handle = std::thread::spawn(move || alice_party(alice, tx_ab, rx_ba, total, eval));
    let bob_handle = std::thread::spawn(move || bob_party(bob, tx_ba, rx_ab, total, eval));

    let seeds = alice_handle.join().unwrap()?;
    bob_handle.join().unwrap()?;

    Ok(seeds)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Gate, GateType};

    fn simple_circuit() -> Circuit {
        let mut circuit = Circuit::default();
        let a = circuit.issue_input_wire();
        let b = circuit.issue_input_wire();
        let out = circuit.issue_wire();
        circuit.add_gate(Gate::new(GateType::Xor, a, b, out));
        circuit.make_wire_output(out);
        circuit
    }

    #[test]
    fn test_cut_and_choose_success() {
        let alice = simple_circuit();
        let bob = simple_circuit();
        let seeds = run_cut_and_choose(alice, bob, 7, 5).expect("protocol should succeed");
        assert_eq!(seeds.len(), 5);
    }

    #[test]
    fn test_cut_and_choose_mismatch() {
        let mut alice = simple_circuit();
        let bob = simple_circuit();
        let extra = alice.issue_wire();
        alice.add_gate(Gate::new(GateType::And, extra, extra, extra));

        let res = run_cut_and_choose(alice, bob, 7, 5);
        assert!(res.is_err());
    }
}

