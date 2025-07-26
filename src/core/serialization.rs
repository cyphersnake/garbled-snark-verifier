use std::fs::OpenOptions;
use std::io::{self, BufWriter, Read, Seek, SeekFrom, Write};
use std::path::Path;

use crate::bag::Gate;

/// Magic header written to serialized gate files.
pub const FILE_MAGIC: &[u8; 4] = b"GTV1";

/// Helper struct returned when reading a serialized gate file.
#[derive(Debug, PartialEq, Eq)]
pub struct GateRecord {
    pub operation: u8,
    pub wire_a: u64,
    pub wire_b: u64,
    pub wire_c: u64,
}

fn write_id<W: Write>(mut writer: W, id: u64) -> io::Result<()> {
    assert!(id <= 0xFFFF_FFFF_FFu64);
    let bytes = id.to_le_bytes();
    writer.write_all(&bytes[..5])
}

fn read_id<R: Read>(mut reader: R) -> io::Result<u64> {
    let mut buf = [0u8; 8];
    reader.read_exact(&mut buf[..5])?;
    Ok(u64::from_le_bytes(buf))
}

fn open_writer<P: AsRef<Path>>(path: P, append: bool) -> io::Result<BufWriter<std::fs::File>> {
    let file = OpenOptions::new()
        .create(true)
        .write(true)
        .append(append)
        .truncate(!append)
        .open(path)?;
    Ok(BufWriter::new(file))
}

/// Write gates to the given file, overwriting existing content.
pub fn write_gates<P: AsRef<Path>>(gates: &[Gate], path: P) -> io::Result<()> {
    let mut writer = open_writer(path, false)?;
    writer.write_all(FILE_MAGIC)?;
    writer.write_all(&(gates.len() as u64).to_le_bytes())?;
    for gate in gates {
        serialize_gate(&mut writer, gate)?;
    }
    writer.flush()
}

/// Append gates to an existing file.
pub fn append_gates<P: AsRef<Path>>(gates: &[Gate], path: P) -> io::Result<()> {
    let mut file = OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .open(path)?;

    if file.metadata()?.len() == 0 {
        file.write_all(FILE_MAGIC)?;
        file.write_all(&0u64.to_le_bytes())?;
    }

    file.seek(SeekFrom::Start(0))?;
    let mut magic = [0u8; 4];
    file.read_exact(&mut magic)?;
    if &magic != FILE_MAGIC {
        return Err(io::Error::new(io::ErrorKind::InvalidData, "bad magic"));
    }

    let mut count_bytes = [0u8; 8];
    file.read_exact(&mut count_bytes)?;
    let mut count = u64::from_le_bytes(count_bytes);
    count += gates.len() as u64;

    file.seek(SeekFrom::Start(FILE_MAGIC.len() as u64))?;
    file.write_all(&count.to_le_bytes())?;
    file.seek(SeekFrom::End(0))?;
    let mut writer = BufWriter::new(file);
    for gate in gates {
        serialize_gate(&mut writer, gate)?;
    }
    writer.flush()
}

fn serialize_gate<W: Write>(writer: &mut W, gate: &Gate) -> io::Result<()> {
    writer.write_all(&[gate.gate_type as u8])?;
    write_id(&mut *writer, gate.wire_a.borrow().id)?;
    write_id(&mut *writer, gate.wire_b.borrow().id)?;
    write_id(writer, gate.wire_c.borrow().id)
}

/// Read all gates from a serialized file.
pub fn read_gates<P: AsRef<Path>>(path: P) -> io::Result<Vec<GateRecord>> {
    let mut file = std::fs::File::open(path)?;
    let mut magic = [0u8; 4];
    file.read_exact(&mut magic)?;
    if &magic != FILE_MAGIC {
        return Err(io::Error::new(io::ErrorKind::InvalidData, "bad magic"));
    }
    let mut count_bytes = [0u8; 8];
    file.read_exact(&mut count_bytes)?;
    let count = u64::from_le_bytes(count_bytes);
    let mut gates = Vec::with_capacity(count as usize);
    for _ in 0..count {
        let mut op = [0u8; 1];
        file.read_exact(&mut op)?;
        let a = read_id(&mut file)?;
        let b = read_id(&mut file)?;
        let c = read_id(&mut file)?;
        gates.push(GateRecord {
            operation: op[0],
            wire_a: a,
            wire_b: b,
            wire_c: c,
        });
    }
    Ok(gates)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuits::bn254::fp254impl::Fp254Impl;
    use crate::circuits::bn254::fq::Fq;

    #[test]
    fn test_gate_serialization() {
        let a = Fq::random();
        let b = Fq::random();
        let circuit = Fq::mul_montgomery(
            Fq::wires_set(Fq::as_montgomery(a)),
            Fq::wires_set(Fq::as_montgomery(b)),
        );

        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("gates.bin");
        write_gates(&circuit.1, &path).unwrap();
        let records = read_gates(&path).unwrap();
        assert_eq!(records.len(), circuit.1.len());
        assert_eq!(records[0].operation, circuit.1[0].gate_type as u8);

        append_gates(&circuit.1, &path).unwrap();
        let records = read_gates(&path).unwrap();
        assert_eq!(records.len(), circuit.1.len() * 2);
        assert_eq!(
            records[circuit.1.len()].operation,
            circuit.1[0].gate_type as u8
        );
    }
}
