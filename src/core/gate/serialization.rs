use std::{
    fs::File,
    io::{self, BufReader, Read},
    path::Path,
    thread,
};

use super::{Gate, GateType};

/// Magic header written to serialized gate files.
pub const FILE_MAGIC: &[u8; 4] = b"GTV1";

fn read_id_from_slice(slice: &[u8]) -> u64 {
    let mut buf = [0u8; 8];
    buf[..5].copy_from_slice(&slice[..5]);
    u64::from_le_bytes(buf)
}

const GATE_SIZE: usize = 16;
const CHUNK_SIZE: usize = 8 * 1024 * 1024; // 8MB, кратно GATE_SIZE
                                           // use
use crossbeam::channel::Receiver;
use thread::JoinHandle;

/// Returns a channel receiver for streaming gates from file
/// Designed for lazy loading of 11b+ gates
#[allow(clippy::type_complexity)]
pub fn read_gates_channel(
    path: impl AsRef<Path>,
) -> io::Result<(Receiver<Vec<Gate>>, JoinHandle<io::Result<()>>)> {
    let (sender, receiver) = crossbeam::channel::bounded::<Vec<Gate>>(2); // максимум 2 чанка в буфере (~128MB RAM)

    let path = path.as_ref().to_owned();

    let reader_thread = thread::spawn(move || -> io::Result<()> {
        let file = File::open(&path)?;
        let mut reader = BufReader::with_capacity(CHUNK_SIZE, file);

        // Проверка заголовка
        let mut magic = [0u8; 4];
        reader.read_exact(&mut magic)?;
        if &magic != FILE_MAGIC {
            panic!("Invalid magic header");
        }

        let mut count_buf = [0u8; 8];
        reader.read_exact(&mut count_buf)?;
        let total = u64::from_le_bytes(count_buf) as usize;

        let mut processed = 0;
        let mut buffer = vec![0u8; CHUNK_SIZE];

        while processed < total {
            let remaining = total - processed;
            let to_read = std::cmp::min(remaining * GATE_SIZE, buffer.len());
            let chunk = &mut buffer[..to_read];
            reader.read_exact(chunk)?;

            let gates = chunk.len() / GATE_SIZE;
            let mut parsed = Vec::with_capacity(gates);

            for i in 0..gates {
                let offset = i * GATE_SIZE;
                let data = &chunk[offset..offset + GATE_SIZE];

                use GateType::*;
                let op = match data[0] {
                    0 => And,
                    1 => Nand,
                    2 => Nimp,
                    3 => Imp, // a => b
                    4 => Ncimp,
                    5 => Cimp, // b => a
                    6 => Nor,
                    7 => Or,
                    8 => Xor,
                    9 => Xnor,
                    10 => Not,
                    _other => panic!("{_other}"),
                };
                let a = read_id_from_slice(&data[1..6]);
                let b = read_id_from_slice(&data[6..11]);
                let c = read_id_from_slice(&data[11..16]);

                parsed.push(Gate {
                    wire_a: crate::WireId(a as usize),
                    wire_b: crate::WireId(b as usize),
                    wire_c: crate::WireId(c as usize),
                    gate_type: op,
                });
            }

            if sender.send(parsed).is_err() {
                // Receiver dropped, stop reading
                break;
            }
            processed += gates;
        }

        Ok(())
    });

    Ok((receiver, reader_thread))
}

/// Designed to read 11b gates
pub fn read_gates_optimized_with(
    path: impl AsRef<Path>,
    mut callback: impl FnMut(Gate),
) -> io::Result<usize> {
    let (receiver, reader_thread) = read_gates_channel(path)?;

    let mut total = 0;
    for chunk in receiver.iter() {
        for gate in chunk {
            callback(gate);
            total += 1;
        }
    }

    reader_thread.join().unwrap()?; // propagate reader error
    Ok(total)
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
