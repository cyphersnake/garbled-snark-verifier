use crate::GateError;

#[derive(Debug, thiserror::Error)]
pub enum CircuitError {
    #[error("Gate error: {0}")]
    Gate(#[from] GateError),
    #[error("Garbling failed: {0}")]
    GarblingFailed(String),
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
}
