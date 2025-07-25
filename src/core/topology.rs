use crate::bag::*;
use std::fs::OpenOptions;
use std::io::{self, Read, Write};
use std::path::Path;

#[derive(Clone, Debug, PartialEq)]
pub struct GateEntry {
    pub operation: u8,
    pub wire_a: u64,
    pub wire_b: u64,
    pub wire_c: u64,
}

impl From<&Gate> for GateEntry {
    fn from(g: &Gate) -> Self {
        Self {
            operation: g.gate_type as u8,
            wire_a: g.wire_a.borrow().id,
            wire_b: g.wire_b.borrow().id,
            wire_c: g.wire_c.borrow().id,
        }
    }
}

fn write_id(buf: &mut Vec<u8>, id: u64) {
    let bytes = id.to_le_bytes();
    buf.extend_from_slice(&bytes[..5]);
}

fn read_id(bytes: &[u8]) -> u64 {
    let mut tmp = [0u8; 8];
    tmp[..5].copy_from_slice(bytes);
    u64::from_le_bytes(tmp)
}

pub fn append_gates_to_file<P: AsRef<Path>>(path: P, gates: &[Gate]) -> io::Result<()> {
    let mut file = OpenOptions::new().create(true).append(true).open(path)?;
    let mut buf = Vec::with_capacity(gates.len() * 16);
    for gate in gates {
        let entry: GateEntry = gate.into();
        buf.push(entry.operation);
        write_id(&mut buf, entry.wire_a);
        write_id(&mut buf, entry.wire_b);
        write_id(&mut buf, entry.wire_c);
    }
    file.write_all(&buf)
}

pub fn read_gate_entries<P: AsRef<Path>>(path: P) -> io::Result<Vec<GateEntry>> {
    let mut file = OpenOptions::new().read(true).open(path)?;
    let mut data = Vec::new();
    file.read_to_end(&mut data)?;
    let mut entries = Vec::new();
    let mut i = 0;
    while i + 16 <= data.len() {
        let op = data[i];
        let a = read_id(&data[i + 1..i + 6]);
        let b = read_id(&data[i + 6..i + 11]);
        let c = read_id(&data[i + 11..i + 16]);
        entries.push(GateEntry { operation: op, wire_a: a, wire_b: b, wire_c: c });
        i += 16;
    }
    Ok(entries)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuits::bn254::fq::Fq;
    use crate::circuits::bn254::fp254impl::Fp254Impl;
    use std::fs;

    #[test]
    fn test_append_and_read() {
        let a = Fq::random();
        let b = Fq::random();
        let circuit = Fq::mul_montgomery(
            Fq::wires_set(Fq::as_montgomery(a)),
            Fq::wires_set(Fq::as_montgomery(b)),
        );

        let path = "test_topology.bin";
        let _ = fs::remove_file(path);
        append_gates_to_file(path, &circuit.1).unwrap();
        let entries = read_gate_entries(path).unwrap();
        assert_eq!(entries.len(), circuit.1.len());
    }
}
