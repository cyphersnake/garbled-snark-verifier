use std::collections::HashMap;
use std::sync::mpsc;

use super::soldering::SolderingEdge;
use super::{Circuit, GarbledComponent, WireId};
use crate::bag::S;

#[derive(Debug)]
pub enum Message {
    GarbledComponents(Vec<Vec<GarbledComponent>>),
    ChallengeSet(Vec<usize>),
    SelectedComponents(Vec<GarbledComponent>),
    SolderingEdges(Vec<SolderingEdge>),
    WireState(HashMap<WireId, S>),
    Result(Vec<bool>),
}

pub struct Garbler {
    tx: mpsc::Sender<Message>,
    rx: mpsc::Receiver<Message>,
}

pub struct Evaluator {
    tx: mpsc::Sender<Message>,
    rx: mpsc::Receiver<Message>,
}

impl Garbler {
    pub fn new() -> (Self, mpsc::Receiver<Message>, mpsc::Sender<Message>) {
        let (tx_to_eval, rx_from_garbler) = mpsc::channel();
        let (tx_to_garbler, rx_from_eval) = mpsc::channel();

        (
            Self {
                tx: tx_to_eval,
                rx: rx_from_eval,
            },
            rx_from_garbler,
            tx_to_garbler,
        )
    }

    pub fn garble_and_send(&self, circuit: &mut Circuit, bucket_size: usize) {
        println!("Garbler: Generating garbled components...");
        let garbled_buckets = garble_all_components(circuit, bucket_size);
        self.tx
            .send(Message::GarbledComponents(garbled_buckets))
            .unwrap();
    }

    pub fn handle_challenge(&self) -> Vec<GarbledComponent> {
        println!("Garbler: Waiting for challenge...");
        if let Ok(Message::ChallengeSet(_challenge)) = self.rx.recv() {
            println!("Garbler: Received challenge, performing cut-and-choose...");
            // Mock: just return empty for now
            vec![]
        } else {
            vec![]
        }
    }
}

impl Evaluator {
    pub fn new() -> (Self, mpsc::Receiver<Message>, mpsc::Sender<Message>) {
        let (tx_to_garbler, rx_from_eval) = mpsc::channel();
        let (tx_to_eval, rx_from_garbler) = mpsc::channel();

        (
            Self {
                tx: tx_to_garbler,
                rx: rx_from_garbler,
            },
            rx_from_eval,
            tx_to_eval,
        )
    }

    pub fn receive_and_challenge(&self) -> Vec<GarbledComponent> {
        println!("Evaluator: Waiting for garbled components...");
        if let Ok(Message::GarbledComponents(garbled_buckets)) = self.rx.recv() {
            println!(
                "Evaluator: Received {} buckets, sending challenge...",
                garbled_buckets.len()
            );

            // Send challenge
            let challenge = vec![0, 1]; // Mock challenge
            self.tx.send(Message::ChallengeSet(challenge)).unwrap();

            // Mock: perform cut-and-choose
            perform_cut_and_choose(garbled_buckets)
        } else {
            vec![]
        }
    }

    pub fn evaluate(&self, components: Vec<GarbledComponent>) -> Vec<bool> {
        println!("Evaluator: Building soldering and evaluating...");
        let soldering_edges = build_soldering(&components);
        let wire_state = evaluate_circuit(&components, &soldering_edges);
        decode_outputs(&wire_state)
    }
}

pub fn run_duplo_protocol(_circuit: Circuit, _bucket_size: usize) -> Vec<bool> {
    todo!()
    //println!("Starting DUPLO protocol with channel communication...");

    //// Create actors
    //let (garbler, rx_from_garbler, tx_to_garbler) = Garbler::new();
    //let (evaluator, rx_from_evaluator, tx_to_evaluator) = Evaluator::new();

    //// Connect channels (in real implementation, these would be network connections)
    //std::thread::spawn(move || {
    //    // Forward messages from garbler to evaluator
    //    while let Ok(msg) = rx_from_garbler.recv() {
    //        tx_to_evaluator.send(msg).unwrap();
    //    }
    //});

    //std::thread::spawn(move || {
    //    // Forward messages from evaluator to garbler
    //    while let Ok(msg) = rx_from_evaluator.recv() {
    //        tx_to_garbler.send(msg).unwrap();
    //    }
    //});

    //// Run protocol
    //let garbler_handle = std::thread::spawn(move || {
    //    garbler.garble_and_send(&mut circuit, bucket_size);
    //    garbler.handle_challenge()
    //});

    //let evaluator_handle = std::thread::spawn(move || {
    //    let selected_components = evaluator.receive_and_challenge();
    //    evaluator.evaluate(selected_components)
    //});

    //// Wait for completion
    //let _garbler_result = garbler_handle.join().unwrap();
    //let result = evaluator_handle.join().unwrap();

    //println!("DUPLO protocol completed!");
    //result
}

fn garble_all_components(circuit: &mut Circuit, bucket_size: usize) -> Vec<Vec<GarbledComponent>> {
    circuit
        .components
        .iter()
        .map(|component| {
            (0..bucket_size)
                .map(|_bucket_id| component.garble())
                .collect()
        })
        .collect()
}

fn perform_cut_and_choose(_garbled_buckets: Vec<Vec<GarbledComponent>>) -> Vec<GarbledComponent> {
    // Mock implementation
    vec![]
}

fn build_soldering(_selected_components: &[GarbledComponent]) -> Vec<SolderingEdge> {
    // Mock implementation
    vec![]
}

fn evaluate_circuit(
    _selected_components: &[GarbledComponent],
    _soldering_edges: &[SolderingEdge],
) -> HashMap<WireId, S> {
    // Mock implementation
    HashMap::new()
}

fn decode_outputs(_wire_state: &HashMap<WireId, S>) -> Vec<bool> {
    // Mock implementation
    vec![]
}
