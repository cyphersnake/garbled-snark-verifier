# Garbled SNARK Verifier Circuit

## Gate Count Metrics

Gate counts are automatically measured for k=6 (64 constraints) on every push to `main` and published as dynamic badges.

![Total Gates](https://img.shields.io/endpoint?url=https://raw.githubusercontent.com/BitVM/garbled-snark-verifier/gh-badges/badge_data/total.json)
![Non-Free Gates](https://img.shields.io/endpoint?url=https://raw.githubusercontent.com/BitVM/garbled-snark-verifier/gh-badges/badge_data/nonfree.json)
![Free Gates](https://img.shields.io/endpoint?url=https://raw.githubusercontent.com/BitVM/garbled-snark-verifier/gh-badges/badge_data/free.json)

---

## Code Explanation

### Core Folder

**s.rs**: contains **S** struct which is a basic wrapper around the type [u8; 32].

**utils.rs**: contains a few utility functions.

**wire.rs**: contains **Wire** struct.

**gate.rs**: contains **Gate** struct which has three wires, and a gate type. It also has **GateCount** which keeps track of number of gates in circuits.

**circuit.rs**: contains **Circuit** struct which has the garbled gates and circuit wires.

### Circuits Folder

this folder contains all the circuits needed for Groth16 verifier circuit.

**basic.rs**: contains basic circuits like half adder etc.

**bigint**: contains u254 circuits.
**groth16.rs**: contains the Groth16 verifier circuit.
**bn254**: contains circuits related to bn254 curve such as field arithmetic circuits etc.

### Gate Serialization Format

The helper module `src/core/serialization.rs` allows dumping large
Groth16 circuits directly to disk. A binary file is written in the
following layout so that the whole circuit does not have to reside in
memory:

- **Header** – 4 bytes ASCII `GTV1` written once when the file is
  created.
- **Gate count** – 8 bytes little endian `u64` giving the total number of
  gate records stored in the file.
- **Gate records** – repeated for every gate in topological order:
  - 1 byte: operation (`GateType` as `u8`)
  - 5 bytes: little endian ID of `wire_a`
  - 5 bytes: little endian ID of `wire_b`
  - 5 bytes: little endian ID of `wire_c`

The fixed 5‑byte encoding efficiently covers `Wire.id` values up to
`11_000_000_000`. New gates can be appended to an existing file with
`append_gates`; the routine updates the stored gate count and then
appends the new records without rewriting earlier data.
