use rand::Rng;
use std::{
    fs::File,
    io::{self, Write},
    sync::mpsc::Sender,
};

use super::{
    Error, FinalizedCircuit, errors::CircuitError, evaluation::EvaluatedCircuit, structure::Circuit,
};
use crate::{Delta, GarbledWire, GarbledWires, S, WireId};

type DefaultHasher = blake3::Hasher;

fn compute_label_hashes(
    circuit: &Circuit,
    wires: &GarbledWires,
) -> (Vec<(WireId, (S, S))>, Vec<(WireId, S)>) {
    fn hash_label<H: digest::Digest + Default>(label: &S) -> S {
        let mut out = [0u8; 32];
        out.copy_from_slice(&H::default().chain_update(label.0).finalize()[..32]);
        S(out)
    }

    let mut input_hashes = Vec::new();
    for &wire_id in [
        circuit.get_false_wire_constant(),
        circuit.get_true_wire_constant(),
    ]
    .iter()
    .chain(circuit.input_wires.iter())
    {
        let wire = wires.get(wire_id).unwrap();
        let h0 = hash_label::<DefaultHasher>(&wire.label0);
        let h1 = hash_label::<DefaultHasher>(&wire.label1);
        input_hashes.push((wire_id, (h0, h1)));
    }

    let mut output_hashes = Vec::new();
    for &wire_id in &circuit.output_wires {
        let wire = wires.get(wire_id).unwrap();
        let h1 = hash_label::<DefaultHasher>(&wire.label1);
        output_hashes.push((wire_id, h1));
    }

    (input_hashes, output_hashes)
}

pub trait CiphertextSink {
    fn push(&mut self, ct: S) -> io::Result<()>;
    fn finalize(&mut self) -> io::Result<S>;
}

#[derive(Default)]
pub struct VecSink {
    pub ciphertexts: Vec<S>,
    hasher: blake3::Hasher,
}

impl CiphertextSink for VecSink {
    fn push(&mut self, ct: S) -> io::Result<()> {
        self.hasher.update(&ct.0);
        self.ciphertexts.push(ct);
        Ok(())
    }

    fn finalize(&mut self) -> io::Result<S> {
        Ok(S(*self.hasher.finalize().as_bytes()))
    }
}

pub struct ChannelSink<'a> {
    pub sender: &'a Sender<S>,
    hasher: blake3::Hasher,
}

impl<'a> ChannelSink<'a> {
    pub fn new(sender: &'a Sender<S>) -> Self {
        Self {
            sender,
            hasher: blake3::Hasher::new(),
        }
    }
}

impl<'a> CiphertextSink for ChannelSink<'a> {
    fn push(&mut self, ct: S) -> io::Result<()> {
        self.hasher.update(&ct.0);
        self.sender
            .send(ct)
            .map_err(|e| io::Error::new(io::ErrorKind::Other, e))
    }

    fn finalize(&mut self) -> io::Result<S> {
        Ok(S(*self.hasher.finalize().as_bytes()))
    }
}

pub struct FileSink {
    file: File,
    hasher: blake3::Hasher,
}

impl FileSink {
    pub fn create(path: impl AsRef<std::path::Path>) -> io::Result<Self> {
        Ok(Self {
            file: File::create(path)?,
            hasher: blake3::Hasher::new(),
        })
    }
}

impl CiphertextSink for FileSink {
    fn push(&mut self, ct: S) -> io::Result<()> {
        self.hasher.update(&ct.0);
        self.file.write_all(&ct.0)
    }

    fn finalize(&mut self) -> io::Result<S> {
        self.file.sync_all()?;
        Ok(S(*self.hasher.finalize().as_bytes()))
    }
}

#[derive(Debug)]
pub struct GarbledCircuit {
    pub structure: Circuit,
    pub wires: GarbledWires,
    pub delta: Delta,
    pub garbled_table: Vec<S>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GarbledCircuitHashes {
    pub input_hashes: Vec<(WireId, (S, S))>,
    pub output_hashes: Vec<(WireId, S)>,
    pub table_hash: S,
}

impl Circuit {
    pub fn garble_into_with<H: digest::Digest + Default + Clone, SINK: CiphertextSink>(
        &self,
        rng: &mut impl Rng,
        sink: &mut SINK,
    ) -> Result<(GarbledCircuit, GarbledCircuitHashes), CircuitError> {
        log::debug!(
            "garble(stream): start wires={} gates={}",
            self.num_wire,
            self.gates.len()
        );

        let delta = Delta::generate_with(rng);

        let mut wires = GarbledWires::new(self.num_wire);
        let mut issue_fn = || GarbledWire::random(rng, &delta);

        [
            self.get_false_wire_constant(),
            self.get_true_wire_constant(),
        ]
        .iter()
        .chain(self.input_wires.iter())
        .for_each(|wire_id| {
            wires.get_or_init(*wire_id, &mut issue_fn).unwrap();
        });

        for (i, g) in self.gates.iter().enumerate() {
            match g.garble::<H>(i, &mut wires, &delta, rng) {
                Ok(Some(row)) => sink.push(row)?,
                Ok(None) => {}
                Err(err) => return Err(err.into()),
            }
        }

        let table_hash = sink.finalize()?;
        log::debug!("garble(stream): complete");

        let (input_hashes, output_hashes) = compute_label_hashes(self, &wires);
        let gc = GarbledCircuit {
            structure: self.clone(),
            wires,
            delta,
            garbled_table: Vec::new(),
        };

        Ok((
            gc,
            GarbledCircuitHashes {
                input_hashes,
                output_hashes,
                table_hash,
            },
        ))
    }

    pub fn garble_with_commit<H: digest::Digest + Default + Clone>(
        &self,
        rng: &mut impl Rng,
    ) -> Result<(GarbledCircuit, GarbledCircuitHashes), CircuitError> {
        let mut sink = VecSink::default();
        let (mut gc, hashes) = self.garble_into_with::<H, _>(rng, &mut sink)?;
        gc.garbled_table = sink.ciphertexts;
        Ok((gc, hashes))
    }

    pub fn garble_from_seed(&self, seed: [u8; 32]) -> Result<GarbledCircuit, CircuitError> {
        use rand_chacha::rand_core::SeedableRng;
        let mut rng = rand_chacha::ChaCha20Rng::from_seed(seed);
        Ok(self.garble_with_commit::<DefaultHasher>(&mut rng)?.0)
    }

    pub fn garble_from_seed_with_commit(
        &self,
        seed: [u8; 32],
    ) -> Result<(GarbledCircuit, GarbledCircuitHashes), CircuitError> {
        use rand_chacha::rand_core::SeedableRng;
        let mut rng = rand_chacha::ChaCha20Rng::from_seed(seed);
        self.garble_with_commit::<DefaultHasher>(&mut rng)
    }

    pub fn garble(&self, rng: &mut impl Rng) -> Result<GarbledCircuit, CircuitError> {
        Ok(self.garble_with_commit::<DefaultHasher>(rng)?.0)
    }

    pub fn garble_with<H: digest::Digest + Default + Clone>(
        &self,
        rng: &mut impl Rng,
    ) -> Result<GarbledCircuit, CircuitError> {
        Ok(self.garble_with_commit::<H>(rng)?.0)
    }
}

impl GarbledCircuit {
    pub fn hashes(&self) -> GarbledCircuitHashes {
        let (input_hashes, output_hashes) = compute_label_hashes(&self.structure, &self.wires);

        let mut th = DefaultHasher::default();
        for ct in &self.garbled_table {
            th.update(&ct.0);
        }
        let table_hash = S(*th.finalize().as_bytes());

        GarbledCircuitHashes {
            input_hashes,
            output_hashes,
            table_hash,
        }
    }
    pub fn evaluate(
        &self,
        get_input: impl Fn(WireId) -> Option<bool>,
    ) -> Result<EvaluatedCircuit, Error> {
        log::debug!(
            "evaluate: start wires={} gates={} table_entries={}",
            self.structure.num_wire,
            self.structure.gates.len(),
            self.garbled_table.len()
        );
        let mut evaluated = vec![Option::<crate::EvaluatedWire>::None; self.structure.num_wire];

        let true_wire = self.structure.get_true_wire_constant();
        let false_wire = self.structure.get_false_wire_constant();

        [true_wire, false_wire]
            .iter()
            .chain(self.structure.input_wires.iter())
            .copied()
            .try_for_each(|wire_id| {
                let value = match wire_id {
                    w if w.eq(&true_wire) => true,
                    w if w.eq(&false_wire) => false,
                    w => (get_input)(w).ok_or(Error::LostInput(wire_id))?,
                };
                let wire = self.wires.get(wire_id)?;
                let active_label = wire.select(value);

                log::debug!("evaluate: input {wire_id}={value} label={active_label:?}");

                evaluated[wire_id.0] = Some(crate::EvaluatedWire {
                    active_label,
                    value,
                });
                Result::<_, Error>::Ok(())
            })?;

        for gate in self.structure.gates.iter() {
            let a = evaluated
                .get(gate.wire_a.0)
                .and_then(|eg| eg.as_ref())
                .ok_or(Error::WrongGateOrder {
                    gate: gate.clone(),
                    wire_id: gate.wire_a,
                })?;
            let b = evaluated
                .get(gate.wire_b.0)
                .and_then(|eg| eg.as_ref())
                .ok_or(Error::WrongGateOrder {
                    gate: gate.clone(),
                    wire_id: gate.wire_b,
                })?;
            let c = self.wires.get(gate.wire_c).unwrap();

            evaluated[gate.wire_c.0] = Some(gate.evaluate(a, b, c));
        }

        Ok(EvaluatedCircuit {
            wires: evaluated.into_iter().map(Option::unwrap).collect(),
            structure: self.structure.clone(),
            garbled_table: self.garbled_table.clone(),
        })
    }

    pub fn finalize(
        &self,
        get_input: impl Fn(WireId) -> Option<bool>,
    ) -> Result<FinalizedCircuit, Error> {
        let outputs = self
            .structure
            .simple_evaluate(&get_input)?
            .collect::<std::collections::HashMap<_, _>>();

        // Collect input wires with their garbled wire labels
        let input_wires = [
            self.structure.get_false_wire_constant(),
            self.structure.get_true_wire_constant(),
        ]
        .iter()
        .chain(self.structure.input_wires.iter())
        .map(|&wire_id| {
            let value = match wire_id {
                w if w == self.structure.get_true_wire_constant() => true,
                w if w == self.structure.get_false_wire_constant() => false,
                w => get_input(w).ok_or(Error::LostInput(wire_id))?,
            };
            let wire = self.wires.get(wire_id)?;
            let active_label = wire.select(value);

            Ok((
                wire_id,
                crate::EvaluatedWire {
                    active_label,
                    value,
                },
            ))
        })
        .collect::<Result<Vec<_>, Error>>()?;

        // Create output wires iterator with their garbled wire labels
        let output_wires = outputs.into_iter().map(|(wire_id, value)| {
            let wire = self.wires.get(wire_id).unwrap();
            let active_label = wire.select(value);
            crate::EvaluatedWire {
                active_label,
                value,
            }
        });

        Ok(FinalizedCircuit::new(
            self.structure.clone(),
            input_wires,
            output_wires,
            self.garbled_table.clone(),
        ))
    }
}
