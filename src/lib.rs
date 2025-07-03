pub mod circuits;
pub mod core;

pub mod bag {
    pub use crate::core::circuit::Circuit;
    pub use crate::core::gate::Gate;
    pub use crate::core::s::S;

    pub use crate::core::wire::{Wire, WireId, Wires};

    pub use crate::core::gate::GateCount;
}

pub mod duplo;
