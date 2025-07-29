use crate::Gate;

/// Enum to handle both reference and owned gate scenarios
#[derive(Clone, Debug)]
pub enum GateRef<'a> {
    Borrowed(&'a Gate),
    Owned(Gate),
}

impl<'a> GateRef<'a> {
    pub fn wire_a(&self) -> crate::WireId {
        match self {
            GateRef::Borrowed(gate) => gate.wire_a,
            GateRef::Owned(gate) => gate.wire_a,
        }
    }

    pub fn wire_b(&self) -> crate::WireId {
        match self {
            GateRef::Borrowed(gate) => gate.wire_b,
            GateRef::Owned(gate) => gate.wire_b,
        }
    }

    pub fn wire_c(&self) -> crate::WireId {
        match self {
            GateRef::Borrowed(gate) => gate.wire_c,
            GateRef::Owned(gate) => gate.wire_c,
        }
    }

    pub fn gate_type(&self) -> crate::GateType {
        match self {
            GateRef::Borrowed(gate) => gate.gate_type,
            GateRef::Owned(gate) => gate.gate_type,
        }
    }
}

/// Trait for providing gates through iteration.
/// This allows for lazy loading of gates from files or other sources
/// while maintaining compatibility with Vec<Gate>.
pub trait GateProvider {
    type Iter<'a>: Iterator<Item = GateRef<'a>>
    where
        Self: 'a;

    /// Get an iterator over all gates
    fn gates(&self) -> Self::Iter<'_>;

    /// Get the total number of gates (if known)
    fn gate_count(&self) -> Option<usize>;

    /// Add a gate to the provider (for mutable providers)
    fn add_gate(&mut self, gate: Gate);
}

/// Iterator for Vec<Gate> that returns borrowed references
pub struct VecGateIterator<'a> {
    iter: std::slice::Iter<'a, Gate>,
}

impl<'a> Iterator for VecGateIterator<'a> {
    type Item = GateRef<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(GateRef::Borrowed)
    }
}

/// Default implementation for Vec<Gate>
impl GateProvider for Vec<Gate> {
    type Iter<'a> = VecGateIterator<'a>;

    fn gates(&self) -> Self::Iter<'_> {
        VecGateIterator { iter: self.iter() }
    }

    fn gate_count(&self) -> Option<usize> {
        Some(self.len())
    }

    fn add_gate(&mut self, gate: Gate) {
        self.push(gate);
    }
}

