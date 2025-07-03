pub mod circuits;
pub mod core;

pub mod bag {
    pub use crate::core::circuit::Circuit;
    pub use crate::core::gate::{Gate, GateCount};
    pub use crate::core::s::S;
    pub use crate::core::wire::{Wire, WireId, new_wirex};
    pub type Wirex = WireId;
    pub type Wires = Vec<Wirex>;
}
