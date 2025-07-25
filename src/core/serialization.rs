use std::fs::File;
use std::io::{self, Read};
use std::path::Path;

use crate::{GateType, WireId, core::gate::Gate};

const HEADER: &[u8; 4] = b"GTV1";

fn read_wire_id(bytes: &[u8; 5]) -> WireId {
    let mut v = 0u64;
    for i in (0..5).rev() {
        v <<= 8;
        v |= bytes[i] as u64;
    }
    WireId(v as usize)
}

pub struct GateReader<R: Read> {
    reader: R,
    remaining: u64,
}

impl GateReader<File> {
    pub fn open<P: AsRef<Path>>(path: P) -> io::Result<Self> {
        let mut file = File::open(path)?;
        let mut header = [0u8; 4];
        file.read_exact(&mut header)?;
        if &header != HEADER {
            return Err(io::Error::new(io::ErrorKind::InvalidData, "bad header"));
        }
        let mut count_bytes = [0u8; 8];
        file.read_exact(&mut count_bytes)?;
        let count = u64::from_le_bytes(count_bytes);
        Ok(Self {
            reader: file,
            remaining: count,
        })
    }
}

impl<R: Read> Iterator for GateReader<R> {
    type Item = io::Result<Gate>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }

        let mut op = [0u8; 1];
        if let Err(e) = self.reader.read_exact(&mut op) {
            return Some(Err(e));
        }

        let mut buf = [0u8; 5];
        if let Err(e) = self.reader.read_exact(&mut buf) {
            return Some(Err(e));
        }
        let wire_a = read_wire_id(&buf);

        if let Err(e) = self.reader.read_exact(&mut buf) {
            return Some(Err(e));
        }
        let wire_b = read_wire_id(&buf);

        if let Err(e) = self.reader.read_exact(&mut buf) {
            return Some(Err(e));
        }
        let wire_c = read_wire_id(&buf);

        self.remaining -= 1;
        Some(Ok(Gate {
            wire_a,
            wire_b,
            wire_c,
            gate_type: match op[0] {
                0 => GateType::And,
                1 => GateType::Nand,
                2 => GateType::Nimp,
                3 => GateType::Imp,
                4 => GateType::Ncimp,
                5 => GateType::Cimp,
                6 => GateType::Nor,
                7 => GateType::Or,
                8 => GateType::Xor,
                9 => GateType::Xnor,
                10 => GateType::Not,
                _ => {
                    return Some(Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "bad gate type",
                    )));
                }
            },
        }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::fs::File;
    use std::io::Write;

    #[test]
    fn test_roundtrip() -> io::Result<()> {
        let path = std::env::temp_dir().join("gate_serial_test.bin");
        let _ = fs::remove_file(&path);

        let gates = vec![
            Gate::and(WireId(1), WireId(2), WireId(3)),
            Gate::xor(WireId(3), WireId(4), WireId(5)),
            Gate::or(WireId(5), WireId(6), WireId(7)),
        ];

        // Manually write the file following the serialization format
        let mut file = File::create(&path)?;
        file.write_all(HEADER)?;
        file.write_all(&(gates.len() as u64).to_le_bytes())?;
        for g in &gates {
            file.write_all(&[g.gate_type as u8])?;
            let mut id = g.wire_a.0 as u64;
            let mut buf = [0u8; 5];
            for i in 0..5 {
                buf[i] = (id & 0xff) as u8;
                id >>= 8;
            }
            file.write_all(&buf)?;
            id = g.wire_b.0 as u64;
            for i in 0..5 {
                buf[i] = (id & 0xff) as u8;
                id >>= 8;
            }
            file.write_all(&buf)?;
            id = g.wire_c.0 as u64;
            for i in 0..5 {
                buf[i] = (id & 0xff) as u8;
                id >>= 8;
            }
            file.write_all(&buf)?;
        }

        let reader = GateReader::open(&path)?;
        let loaded: io::Result<Vec<_>> = reader.collect();
        let loaded = loaded?;

        assert_eq!(gates, loaded);
        fs::remove_file(path)?;
        Ok(())
    }
}
