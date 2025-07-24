mod circuit;
mod core;
mod gadgets;
mod math;
mod protocol;

pub use core::{
    delta::Delta,
    gate::{Gate, GateError},
    gate_type::GateType,
    s::S,
    wire::{EvaluatedWire, GarbledWire, GarbledWires, WireError, WireId},
};

pub use circuit::{Circuit, CircuitError, EvaluatedCircuit, FinalizedCircuit, GarbledCircuit};
pub use gadgets::bn254::{Fq, fp254impl::Fp254Impl};
pub use math::*;
pub use protocol::cut_and_choose::{GarbledCopy, VerifierState};

#[cfg(test)]
pub mod test_utils {
    use rand::SeedableRng;

    pub fn trng() -> rand::rngs::SmallRng {
        rand::rngs::SmallRng::seed_from_u64(0)
    }
}
