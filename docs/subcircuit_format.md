# Groth16 subcircuit folder

Each verifier stage is serialized as a separate file using the gate topology
layout described in `topology_format.md`. Files must be executed in
lexicographic order to reconstruct the full circuit.

| File name            | Description                                         |
|----------------------|-----------------------------------------------------|
| `01_proof_a.bin`     | Decompression of `proof.a` if compressed             |
| `02_proof_b.bin`     | Decompression of `proof.b` if compressed             |
| `03_proof_c.bin`     | Decompression of `proof.c` if compressed             |
| `04_msm.bin`         | Scalar multiplication of public inputs              |
| `05_add.bin`         | Addition with verification key point                |
| `06_affine.bin`      | Conversion of the accumulator to affine coordinates |
| `07_final_exp.bin`   | Final exponentiation of Miller loop result          |
| `08_equal.bin`       | Equality check against constant `alpha_beta`        |

Wires are identified globally and reused across files. Load the records from
each file sequentially to avoid keeping the entire circuit in memory.
