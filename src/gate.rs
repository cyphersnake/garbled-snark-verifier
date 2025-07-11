pub use crate::gate_type::GateType;
use crate::{
    s::S,
    wire::{GarbledWire, GarbledWires, WireId},
    Delta, WireError,
};

#[derive(Clone, Debug, thiserror::Error)]
pub enum Error {
    #[error("Error while get wire {wire}: {err:?}")]
    GetWireError { wire: &'static str, err: WireError },
    #[error("Error while init wire {wire}: {err:?}")]
    InitWireError { wire: &'static str, err: WireError },
    #[error("Error while get_or_init wire {wire}: {err:?}")]
    GetOrInitWireError { wire: &'static str, err: WireError },
}
pub type GateError = Error;

#[derive(Clone, Debug)]
pub struct Gate {
    pub wire_a: WireId,
    pub wire_b: WireId,
    pub wire_c: WireId,
    pub gate_type: GateType,
}

impl Gate {
    #[must_use]
    pub fn new(t: GateType, a: WireId, b: WireId, c: WireId) -> Self {
        Self {
            wire_a: a,
            wire_b: b,
            wire_c: c,
            gate_type: t,
        }
    }

    #[must_use]
    pub fn and(wire_a: WireId, wire_b: WireId, wire_c: WireId) -> Self {
        Self {
            wire_a,
            wire_b,
            wire_c,
            gate_type: GateType::And,
        }
    }

    #[must_use]
    pub fn nand(wire_a: WireId, wire_b: WireId, wire_c: WireId) -> Self {
        Self {
            wire_a,
            wire_b,
            wire_c,
            gate_type: GateType::Nand,
        }
    }

    #[must_use]
    pub fn nimp(wire_a: WireId, wire_b: WireId, wire_c: WireId) -> Self {
        Self {
            wire_a,
            wire_b,
            wire_c,
            gate_type: GateType::Nimp,
        }
    }

    #[must_use]
    pub fn imp(wire_a: WireId, wire_b: WireId, wire_c: WireId) -> Self {
        Self {
            wire_a,
            wire_b,
            wire_c,
            gate_type: GateType::Imp,
        }
    }

    #[must_use]
    pub fn ncimp(wire_a: WireId, wire_b: WireId, wire_c: WireId) -> Self {
        Self {
            wire_a,
            wire_b,
            wire_c,
            gate_type: GateType::Ncimp,
        }
    }

    #[must_use]
    pub fn cimp(wire_a: WireId, wire_b: WireId, wire_c: WireId) -> Self {
        Self {
            wire_a,
            wire_b,
            wire_c,
            gate_type: GateType::Cimp,
        }
    }

    #[must_use]
    pub fn nor(wire_a: WireId, wire_b: WireId, wire_c: WireId) -> Self {
        Self {
            wire_a,
            wire_b,
            wire_c,
            gate_type: GateType::Nor,
        }
    }

    #[must_use]
    pub fn or(wire_a: WireId, wire_b: WireId, wire_c: WireId) -> Self {
        Self {
            wire_a,
            wire_b,
            wire_c,
            gate_type: GateType::Or,
        }
    }

    #[must_use]
    pub fn xor(wire_a: WireId, wire_b: WireId, wire_c: WireId) -> Self {
        Self {
            wire_a,
            wire_b,
            wire_c,
            gate_type: GateType::Xor,
        }
    }

    #[must_use]
    pub fn xnor(wire_a: WireId, wire_b: WireId, wire_c: WireId) -> Self {
        Self {
            wire_a,
            wire_b,
            wire_c,
            gate_type: GateType::Xnor,
        }
    }

    #[must_use]
    pub fn not(wire_a: WireId, wire_c: WireId) -> Self {
        Self {
            wire_a,
            wire_b: wire_a,
            wire_c,
            gate_type: GateType::Not,
        }
    }

    /// Creates an AND-variant gate with configurable boolean function.                                                                                      │ │
    ///                                                                                                                                                      │ │
    /// This function implements the formula: `((a XOR f[0]) AND (b XOR f[1])) XOR f[2]`                                                                     │ │
    /// where the 3-bit encoding `f` determines which of the 8 AND-variant gate types to create.                                                             │ │
    ///                                                                                                                                                      │ │
    /// # Arguments                                                                                                                                          │ │
    ///                                                                                                                                                      │ │
    /// * `wire_a` - First input wire                                                                                                                        │ │
    /// * `wire_b` - Second input wire                                                                                                                       │ │
    /// * `wire_c` - Output wire                                                                                                                             │ │
    /// * `f` - 3-bit encoding array `[f0, f1, f2]` that determines the gate type:                                                                           │ │
    ///   - `[0,0,0]` → AND gate                                                                                                                             │ │
    ///   - `[0,0,1]` → NAND gate                                                                                                                            │ │
    ///   - `[0,1,0]` → NIMP gate (A AND NOT B)                                                                                                              │ │
    ///   - `[0,1,1]` → IMP gate (A implies B)                                                                                                               │ │
    ///   - `[1,0,0]` → NCIMP gate (NOT A AND B)                                                                                                             │ │
    ///   - `[1,0,1]` → CIMP gate (B implies A)                                                                                                              │ │
    ///   - `[1,1,0]` → NOR gate                                                                                                                             │ │
    ///   - `[1,1,1]` → OR gate                                                                                                                              │ │
    ///
    /// # Returns                                                                                                                                            │ │
    ///                                                                                                                                                      │ │
    /// A new `Gate` instance with the specified wires and gate type.                                                                                        │ │
    #[must_use]
    pub fn and_variant(a: WireId, b: WireId, c: WireId, f: [bool; 3]) -> Self {
        Self::new(
            match f {
                [false, false, false] => GateType::And,
                [false, false, true] => GateType::Nand,
                [false, true, false] => GateType::Nimp,
                [false, true, true] => GateType::Imp,
                [true, false, false] => GateType::Ncimp,
                [true, false, true] => GateType::Cimp,
                [true, true, false] => GateType::Nor,
                [true, true, true] => GateType::Or,
            },
            a,
            b,
            c,
        )
    }

    fn wire_a<'w>(
        &self,
        wires: &'w mut GarbledWires,
        delta: &Delta,
    ) -> Result<&'w GarbledWire, Error> {
        wires
            .get_or_init(self.wire_a, || GarbledWire::random(delta))
            .map_err(|err| Error::GetWireError { wire: "a", err })
    }

    fn wire_b<'w>(
        &self,
        wires: &'w mut GarbledWires,
        delta: &Delta,
    ) -> Result<&'w GarbledWire, Error> {
        wires
            .get_or_init(self.wire_b, || GarbledWire::random(delta))
            .map_err(|err| Error::GetWireError { wire: "b", err })
    }

    fn init_wire_c(&self, wires: &mut GarbledWires, label0: S, label1: S) -> Result<(), Error> {
        wires
            .init(self.wire_c, GarbledWire::new(label0, label1))
            .map_err(|err| Error::InitWireError { wire: "c", err })
            .map(|_| ())
    }

    pub fn garble(&self, wires: &mut GarbledWires, delta: &Delta) -> Result<Vec<S>, Error> {
        match self.gate_type {
            GateType::Xor => {
                let a = self.wire_a(wires, delta)?.select(false);
                let b = self.wire_b(wires, delta)?.select(false);

                let c0 = a ^ &b;
                let c1 = c0 ^ delta;

                self.init_wire_c(wires, c0, c1)?;

                Ok(vec![])
            }

            GateType::Xnor => {
                let a = self.wire_a(wires, delta)?.select(false);
                let b = self.wire_b(wires, delta)?.select(false);

                let c1 = a ^ &b;
                let c0 = c1 ^ delta;

                self.init_wire_c(wires, c0, c1)?;

                Ok(vec![])
            }
            GateType::Not => {
                let a = self.wire_a(wires, delta)?;

                let c0 = a.select(true); // a₁
                let c1 = a.select(false); // a₀

                self.init_wire_c(wires, c0, c1)?;

                Ok(vec![])
            }
            _gt => {
                let gate_f = self.gate_type.f();

                let c = wires
                    .init(self.wire_c, GarbledWire::random(delta))
                    .map_err(|err| Error::GetOrInitWireError { wire: "c", err })?
                    .clone();

                let a = self.wire_a(wires, delta)?.clone();
                let b = self.wire_b(wires, delta)?;

                Ok({
                    [(false, false), (false, true), (true, false), (true, true)]
                        .iter()
                        .map(|(i, j)| {
                            let k = (gate_f)(*i, *j);
                            let a = a.select(*i);
                            let b = b.select(*j);
                            let c = c.select(k);
                            c + S::hash_together(a, b).neg()
                        })
                        .collect()
                })
            }
        }
    }

    pub fn evaluate(
        &self,
        a: S,
        b: S,
        delta: &Delta,
        table: &[Vec<S>],
        table_gate_index: &mut usize,
    ) -> S {
        match self.gate_type {
            GateType::Xor => a ^ &b,
            GateType::Xnor => (a ^ &b) ^ delta,
            GateType::Not => a ^ delta,
            _gt => {
                let i = a.0[31] & 1;
                let j = b.0[31] & 1;

                let idx = ((i << 1) | j) as usize;

                let ct = &table[*table_gate_index][idx];

                *table_gate_index += 1;

                let hash = S::hash_together(a, b);
                *ct + hash
            }
        }
    }
}
