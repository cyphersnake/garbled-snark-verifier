use memmap2::Mmap;
use once_cell::sync::Lazy;
use std::fs::{File, OpenOptions};
use std::io::{self, BufReader, BufWriter, Read, Seek, SeekFrom, Write};
use std::path::Path;
use std::sync::Mutex;

use crate::bag::Gate;

use super::gate::GateType;

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

/// Streaming writer for gates that updates the count on `finish()`.
pub struct GateWriter {
    writer: BufWriter<std::fs::File>,
    count: u64,
}

impl GateWriter {
    /// Create a new writer and truncate any existing file.
    pub fn new<P: AsRef<Path>>(path: P) -> io::Result<Self> {
        let file = OpenOptions::new()
            .create(true)
            .read(true)
            .write(true)
            .truncate(true)
            .open(path)?;
        let mut writer = BufWriter::new(file);
        writer.write_all(FILE_MAGIC)?;
        writer.write_all(&0u64.to_le_bytes())?;
        Ok(Self { writer, count: 0 })
    }

    /// Append a single gate record to the file.
    pub fn record_gate(&mut self, gate: &Gate) -> io::Result<()> {
        serialize_gate(&mut self.writer, gate)?;
        self.count += 1;
        Ok(())
    }

    /// Finalize writing by updating the gate count header.
    pub fn finish(mut self) -> io::Result<()> {
        self.writer.flush()?;
        let file = self.writer.get_mut();
        file.seek(SeekFrom::Start(FILE_MAGIC.len() as u64))?;
        file.write_all(&self.count.to_le_bytes())?;
        file.flush()
    }
}

/// Global writer used when evaluating gates.
pub static GLOBAL_GATE_WRITER: Lazy<Mutex<Option<GateWriter>>> = Lazy::new(|| Mutex::new(None));

pub(crate) fn install_gate_writer(writer: GateWriter) {
    *GLOBAL_GATE_WRITER.lock().unwrap() = Some(writer);
}

pub(crate) fn take_gate_writer() -> Option<GateWriter> {
    GLOBAL_GATE_WRITER.lock().unwrap().take()
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

// --- Исходная функция: читает все гейты и просто считает ---
pub fn read_gates(path: impl AsRef<Path>) -> io::Result<usize> {
    let mut count = 0;
    read_gates_optimized_with(path, |_| {
        if count % 1_000_000 == 0 {
            println!("{count}");
        }
        count += 1
    })?;
    Ok(count)
}

struct OriginalGate {
    a: u64,
    b: u64,
    c: u64,
    op: GateType,
}

fn read_id_from_slice(slice: &[u8]) -> u64 {
    let mut buf = [0u8; 8];
    buf[..5].copy_from_slice(&slice[..5]);
    u64::from_le_bytes(buf)
}

const GATE_SIZE: usize = 16;
const CHUNK_SIZE: usize = 8 * 1024 * 1024; // 8MB, кратно GATE_SIZE

// --- Обобщённая высокопроизводительная версия ---
pub fn read_gates_optimized_with<P: AsRef<Path>>(
    path: P,
    mut callback: impl FnMut(OriginalGate),
) -> Result<usize, io::Error> {
    let file = File::open(path)?;
    let mut reader = BufReader::with_capacity(CHUNK_SIZE, file);

    // 1. Читаем MAGIC
    let mut magic = [0u8; 4];
    reader.read_exact(&mut magic)?;
    if &magic != FILE_MAGIC {
        panic!("Invalid magic header");
    }

    // 2. Читаем COUNT
    let mut count_buf = [0u8; 8];
    reader.read_exact(&mut count_buf)?;
    let total = u64::from_le_bytes(count_buf) as usize;

    // 3. Чтение чанками
    let mut processed = 0;
    let mut buffer = vec![0u8; CHUNK_SIZE];

    while processed < total {
        let remaining = total - processed;
        let to_read = remaining * GATE_SIZE;
        let read_size = std::cmp::min(to_read, buffer.len());

        let chunk = &mut buffer[..read_size];
        reader.read_exact(chunk)?;

        let gates_in_chunk = chunk.len() / GATE_SIZE;
        for i in 0..gates_in_chunk {
            let offset = i * GATE_SIZE;
            let data = &chunk[offset..offset + GATE_SIZE];

            let op = GateType::try_from(data[0]).unwrap();
            let a = read_id_from_slice(&data[1..6]);
            let b = read_id_from_slice(&data[6..11]);
            let c = read_id_from_slice(&data[11..16]);

            callback(OriginalGate { op, a, b, c });
        }

        processed += gates_in_chunk;
    }

    Ok(processed)
}

//#[cfg(test)]
//mod tests {
//    use super::*;
//    use crate::bag::Circuit;
//    use crate::circuits::bn254::fp254impl::Fp254Impl;
//    use crate::circuits::bn254::fq::Fq;
//
//    #[test]
//    fn test_gate_serialization() {
//        let a = Fq::random();
//        let b = Fq::random();
//        let circuit = Fq::mul_montgomery(
//            Fq::wires_set(Fq::as_montgomery(a)),
//            Fq::wires_set(Fq::as_montgomery(b)),
//        );
//
//        let dir = tempfile::tempdir().unwrap();
//        let path = dir.path().join("gates.bin");
//        write_gates(&circuit.1, &path).unwrap();
//        let records = read_gates(&path).unwrap();
//        assert_eq!(records.len(), circuit.1.len());
//        assert_eq!(records[0].operation, circuit.1[0].gate_type as u8);
//
//        append_gates(&circuit.1, &path).unwrap();
//        let records = read_gates(&path).unwrap();
//        assert_eq!(records.len(), circuit.1.len() * 2);
//        assert_eq!(
//            records[circuit.1.len()].operation,
//            circuit.1[0].gate_type as u8
//        );
//    }
//
//    #[test]
//    fn test_gate_writer_stream() {
//        let a = Fq::random();
//        let b = Fq::random();
//        let circuit = Fq::mul_montgomery(
//            Fq::wires_set(Fq::as_montgomery(a)),
//            Fq::wires_set(Fq::as_montgomery(b)),
//        );
//
//        let dir = tempfile::tempdir().unwrap();
//        let path = dir.path().join("stream.bin");
//        Circuit::start_gate_recording(&path).unwrap();
//        for mut g in circuit.1.clone() {
//            g.evaluate();
//        }
//        Circuit::finish_gate_recording().unwrap();
//        let records = read_gates(&path).unwrap();
//        assert_eq!(records.len(), circuit.1.len());
//    }
//}
