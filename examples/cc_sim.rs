//! Cut-and-Choose honest simulation loading artefacts from disk
//!
//! This example reads the files produced by `file_circuit_example.rs`
//! and runs a simplified cut-and-choose protocol between two threads.
//! Only hashes of the ciphertexts are used, matching the data saved by
//! the garbling example.

use std::{
    fs,
    path::PathBuf,
    sync::mpsc::{Receiver, Sender, channel},
    thread,
};

use anyhow::{Context, Result};
use bitcoin::hashes::{Hash, hash160, sha256};
use serde::Deserialize;

const CC_TOTAL: usize = 181;
const CC_EVAL: usize = 1; // only first circuit evaluated
const CC_CHECK: usize = CC_TOTAL - CC_EVAL;

type Label = [u8; 16];

#[derive(Clone, Debug)]
struct Commitment {
    input_label_hashes: Vec<hash160::Hash>,
    output_label_hash: hash160::Hash,
    ciphertext_hash: [u8; 32],
}

#[derive(Clone, Debug)]
struct CircuitPackage {
    ciphertext: Vec<u8>,
    input_labels: Vec<Label>,
    output_label_zero: Label,
}

#[derive(Debug)]
enum Message {
    Commit(Vec<Commitment>),
    RequestOpen { open_indices: Vec<usize> },
    Circuits(Vec<(usize, CircuitPackage)>),
    VerificationResult { ok: bool },
}

#[derive(Deserialize)]
struct Config {
    data_root: PathBuf,
}

fn main() -> Result<()> {
    let config_path = std::env::args()
        .nth(1)
        .expect("Usage: cargo run --example cc_sim -- <config.toml>");
    let config: Config = toml::from_str(&fs::read_to_string(config_path)?)?;

    let (tx_ab, rx_ab) = channel::<Message>();
    let (tx_ba, rx_ba) = channel::<Message>();

    // spawn Alice
    let alice_handle = {
        let root = config.data_root.clone();
        thread::spawn(move || alice(root, tx_ab, rx_ba).expect("alice failed"))
    };

    // spawn Bob
    let bob_handle = thread::spawn(move || bob(tx_ba, rx_ab).expect("bob failed"));

    alice_handle.join().unwrap();
    bob_handle.join().unwrap();

    Ok(())
}

fn alice(root: PathBuf, tx: Sender<Message>, rx: Receiver<Message>) -> Result<()> {
    let mut commitments = Vec::with_capacity(CC_TOTAL);
    for idx in 0..CC_TOTAL {
        let commit = commit_for_circuit(&root, idx)?;
        commitments.push(commit);
    }
    tx.send(Message::Commit(commitments))?;

    loop {
        match rx.recv()? {
            Message::RequestOpen { open_indices } => {
                let eval_indices: Vec<usize> = (0..CC_TOTAL)
                    .filter(|idx| !open_indices.contains(idx))
                    .collect();
                let mut pkgs = Vec::with_capacity(eval_indices.len());
                for &idx in &eval_indices {
                    let pkg = materialise_circuit(&root, idx)?;
                    pkgs.push((idx, pkg));
                }
                tx.send(Message::Circuits(pkgs))?;
            }
            Message::VerificationResult { ok } => {
                println!("✔ Alice received Bob's verdict — protocol ok = {ok}");
                break;
            }
            other => eprintln!("unexpected message: {other:?}"),
        }
    }
    Ok(())
}

fn bob(tx: Sender<Message>, rx: Receiver<Message>) -> Result<()> {
    let mut commitments: Option<Vec<Commitment>> = None;
    let mut circuit_pkgs: Option<Vec<(usize, CircuitPackage)>> = None;

    loop {
        match rx.recv()? {
            Message::Commit(comms) => {
                commitments = Some(comms);
                let eval_indices = vec![0usize];
                let open_indices: Vec<usize> = (0..CC_TOTAL)
                    .filter(|idx| !eval_indices.contains(idx))
                    .collect();
                tx.send(Message::RequestOpen { open_indices })?;
            }
            Message::Circuits(list) => {
                circuit_pkgs = Some(list);
            }
            _ => {}
        }

        if commitments.is_some() && circuit_pkgs.is_some() {
            let ok = verify(
                commitments.as_ref().unwrap(),
                circuit_pkgs.as_ref().unwrap(),
            )?;
            tx.send(Message::VerificationResult { ok })?;
            println!("✔ Bob finished verification — protocol ok = {ok}");
            break;
        }
    }
    Ok(())
}

fn verify(commits: &[Commitment], pkgs: &[(usize, CircuitPackage)]) -> Result<bool> {
    for (idx, pkg) in pkgs {
        let commit = &commits[*idx];
        if commit.output_label_hash != hash160::Hash::hash(&pkg.output_label_zero)
            || commit.ciphertext_hash != sha256::Hash::hash(&pkg.ciphertext).to_byte_array()
        {
            return Ok(false);
        }
        let hashes: Vec<hash160::Hash> = pkg
            .input_labels
            .iter()
            .map(|l| hash160::Hash::hash(l))
            .collect();
        if hashes != commit.input_label_hashes {
            return Ok(false);
        }
    }
    Ok(true)
}

fn commit_for_circuit(root: &PathBuf, idx: usize) -> Result<Commitment> {
    let dir = root.join(idx.to_string());
    let inputs: Vec<Label> = load_label_pairs(&dir.join("inputs_labels.json"))?;
    let outputs: Vec<Label> = load_label_pairs(&dir.join("output_labels.json"))?;
    let output_label_zero = outputs.first().cloned().unwrap_or([0u8; 16]);
    let ct = fs::read(&dir.join("ciphertext_hash.bin"))?;

    let input_hashes = inputs.iter().map(|l| hash160::Hash::hash(l)).collect();
    let output_hash = hash160::Hash::hash(&output_label_zero);
    let ciphertext_hash = sha256::Hash::hash(&ct).to_byte_array();
    Ok(Commitment {
        input_label_hashes: input_hashes,
        output_label_hash: output_hash,
        ciphertext_hash,
    })
}

fn materialise_circuit(root: &PathBuf, idx: usize) -> Result<CircuitPackage> {
    let dir = root.join(idx.to_string());
    let input_labels = load_label_pairs(&dir.join("inputs_labels.json"))?;
    let outputs = load_label_pairs(&dir.join("output_labels.json"))?;
    let output_label_zero = outputs.first().cloned().unwrap_or([0u8; 16]);
    let ciphertext = fs::read(&dir.join("ciphertext_hash.bin"))?;
    Ok(CircuitPackage {
        ciphertext,
        input_labels,
        output_label_zero,
    })
}

fn load_label_pairs(path: &PathBuf) -> Result<Vec<Label>> {
    let contents = fs::read_to_string(path).with_context(|| format!("reading {path:?}"))?;
    let pairs: Vec<[Label; 2]> =
        serde_json::from_str(&contents).with_context(|| format!("parsing {path:?}"))?;
    let mut labels = Vec::with_capacity(pairs.len() * 2);
    for pair in pairs {
        labels.push(pair[0]);
        labels.push(pair[1]);
    }
    Ok(labels)
}
