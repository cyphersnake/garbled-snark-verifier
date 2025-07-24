use rand::prelude::SliceRandom;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use std::sync::mpsc::{self, Receiver, Sender};

use crate::Circuit;

/// Seeds for circuits that were not opened by the evaluator.
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

const GARBLER: &str = "[garbler]";
const EVALUATOR: &str = "[evaluator]";

fn garbler_party(
    circuit: Circuit,
    tx: Sender<Message>,
    rx: Receiver<Message>,
    total: usize,
    _eval: usize,
) -> Result<Vec<EvalSeed>, String> {
    log::info!("{GARBLER} generating {total} circuits");
    let mut rng = StdRng::from_os_rng();
    let mut seeds = Vec::with_capacity(total);
    let mut commits = Vec::with_capacity(total);

    for i in 0..total {
        let seed: [u8; 32] = rng.r#gen();
        seeds.push(seed);
        let mut srng = StdRng::from_seed(seed);
        let garbled = circuit
            .garble(&mut srng)
            .map_err(|e| format!("{e:?}"))?;
        let commit = garbled.commit_output_labels();
        log::debug!("{GARBLER} circuit {i} commit={:?}", commit);
        commits.push(commit);
    }

    log::info!("{GARBLER} sending commits");
    tx.send(Message::Commits(commits))
        .map_err(|e| e.to_string())?;

    let eval_indices = match rx.recv().map_err(|e| e.to_string())? {
        Message::EvalIndices(v) => v,
        _ => return Err("unexpected message".into()),
    };
    log::info!("{GARBLER} evaluator chose indices {eval_indices:?}");

    let seeds_to_send: Vec<(usize, [u8; 32])> = seeds
        .iter()
        .copied()
        .enumerate()
        .filter(|(i, _)| !eval_indices.contains(i))
        .collect();

    log::info!("{GARBLER} sending {} seeds", seeds_to_send.len());
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

fn evaluator_party(
    circuit: Circuit,
    tx: Sender<Message>,
    rx: Receiver<Message>,
    total: usize,
    eval: usize,
) -> Result<(), String> {
    log::info!("{EVALUATOR} waiting for commits");
    let commits = match rx.recv().map_err(|e| e.to_string())? {
        Message::Commits(c) => c,
        _ => return Err("unexpected message".into()),
    };
    log::info!("{EVALUATOR} received {} commits", commits.len());

    if commits.len() != total {
        return Err("commit count mismatch".into());
    }

    let mut rng = StdRng::from_os_rng();
    let mut eval_indices: Vec<usize> = (0..total).collect();
    eval_indices.shuffle(&mut rng);
    eval_indices.truncate(eval);
    eval_indices.sort_unstable();
    log::info!("{EVALUATOR} checking indices {eval_indices:?}");

    tx.send(Message::EvalIndices(eval_indices.clone()))
        .map_err(|e| e.to_string())?;

    let seeds = match rx.recv().map_err(|e| e.to_string())? {
        Message::Seeds(s) => s,
        _ => return Err("unexpected message".into()),
    };
    log::info!("{EVALUATOR} received {} seeds", seeds.len());

    for (i, seed) in seeds {
        let mut srng = StdRng::from_seed(seed);
        let garbled = circuit
            .garble(&mut srng)
            .map_err(|e| format!("{e:?}"))?;
        let commit = garbled.commit_output_labels();
        if commit != commits[i] {
            return Err("commit mismatch".into());
        }
    }

    // Evaluation step will use the remaining seeds. Not implemented yet.
    Ok(())
}

/// Runs a simple cut-and-choose where the garbler generates all circuits and
/// the evaluator checks a random subset. Returns the seeds of the unchecked
/// circuits.
pub fn run_cut_and_choose(
    garbler: Circuit,
    evaluator: Circuit,
    total: usize,
    eval: usize,
) -> Result<Vec<EvalSeed>, String> {
    let (tx_ab, rx_ab) = mpsc::channel();
    let (tx_ba, rx_ba) = mpsc::channel();

    let garbler_handle = std::thread::spawn(move || garbler_party(garbler, tx_ab, rx_ba, total, eval));
    let evaluator_handle = std::thread::spawn(move || evaluator_party(evaluator, tx_ba, rx_ab, total, eval));

    let seeds = garbler_handle.join().unwrap()?;
    evaluator_handle.join().unwrap()?;

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
        let garbler = simple_circuit();
        let evaluator = simple_circuit();
        let seeds = run_cut_and_choose(garbler, evaluator, 7, 5).expect("protocol should succeed");
        assert_eq!(seeds.len(), 5);
    }

    #[test]
    fn test_cut_and_choose_mismatch() {
        let mut garbler = simple_circuit();
        let evaluator = simple_circuit();
        let extra = garbler.issue_wire();
        garbler.add_gate(Gate::new(GateType::And, extra, extra, extra));

        let res = run_cut_and_choose(garbler, evaluator, 7, 5);
        assert!(res.is_err());
    }
}

