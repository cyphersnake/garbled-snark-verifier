pub mod circuit;
mod core;
mod gadgets;
mod math;
pub mod process_monitor;
pub mod tui_monitor;

pub use core::{
    delta::Delta,
    gate::{Gate, GateError},
    gate_type::GateType,
    s::S,
    wire::{EvaluatedWire, GarbledWire, GarbledWires, WireError, WireId},
};

pub use circuit::{
    Circuit, CircuitError, EvaluatedCircuit, FinalizedCircuit, GarbledCircuit, GateProvider,
    GateRef,
};
pub use math::*;

#[cfg(test)]
pub mod test_utils {
    use rand::SeedableRng;

    pub fn trng() -> rand::rngs::SmallRng {
        rand::rngs::SmallRng::seed_from_u64(0)
    }
}
