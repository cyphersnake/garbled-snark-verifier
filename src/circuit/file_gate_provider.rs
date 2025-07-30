use std::{
    collections::VecDeque,
    fs::File,
    io::{BufReader, Read},
    path::{Path, PathBuf},
    thread,
};

use super::{GateProvider, GateRef};
use crate::{
    Gate,
    core::gate::serialization::{FILE_MAGIC, read_gates_channel},
};

/// A gate provider that lazily streams gates from a file using channels.
/// Memory efficient for very large files (11+ billion gates).
pub struct FileGateProvider {
    file_path: PathBuf,
    gate_count: usize,
}

impl FileGateProvider {
    /// Create a new FileGateProvider by reading only the header to get gate count
    pub fn new(file_path: impl AsRef<Path>) -> std::io::Result<Self> {
        let file_path = file_path.as_ref().to_path_buf();

        // Read only the header to get gate count (fast!)
        let file = File::open(&file_path)?;
        let mut reader = BufReader::new(file);

        // Check magic header
        let mut magic = [0u8; 4];
        reader.read_exact(&mut magic)?;
        if &magic != FILE_MAGIC {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "Invalid magic header",
            ));
        }

        // Read gate count from header
        let mut count_buf = [0u8; 8];
        reader.read_exact(&mut count_buf)?;
        let gate_count = u64::from_le_bytes(count_buf) as usize;

        Ok(Self {
            file_path,
            gate_count,
        })
    }
}

/// Iterator that streams gates using the channel from serialization module
pub struct FileGateIterator<'a> {
    receiver: crossbeam::channel::Receiver<Vec<Gate>>,
    current_chunk: VecDeque<Gate>,
    reader_handle: Option<thread::JoinHandle<std::io::Result<()>>>,
    finished: bool,
    _phantom: std::marker::PhantomData<&'a ()>,
}

impl<'a> FileGateIterator<'a> {
    fn new(file_path: PathBuf) -> std::io::Result<Self> {
        let (receiver, reader_handle) = read_gates_channel(&file_path)?;

        Ok(Self {
            receiver,
            current_chunk: VecDeque::new(),
            reader_handle: Some(reader_handle),
            finished: false,
            _phantom: std::marker::PhantomData,
        })
    }
}

impl<'a> Iterator for FileGateIterator<'a> {
    type Item = GateRef<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        // If current chunk is empty, try to get next chunk
        if self.current_chunk.is_empty() && !self.finished {
            match self.receiver.recv() {
                Ok(chunk) => {
                    self.current_chunk.extend(chunk);
                }
                Err(_) => {
                    // Channel closed, finish
                    self.finished = true;
                    if let Some(handle) = self.reader_handle.take() {
                        let _ = handle.join();
                    }
                }
            }
        }

        // Return next gate from current chunk as owned
        self.current_chunk.pop_front().map(GateRef::Owned)
    }
}

impl GateProvider for FileGateProvider {
    type Iter<'a> = FileGateIterator<'a>;

    fn gates(&self) -> Self::Iter<'_> {
        FileGateIterator::new(self.file_path.clone())
            .expect("Failed to create gate iterator from file")
    }

    fn gate_count(&self) -> Option<usize> {
        Some(self.gate_count)
    }

    fn add_gate(&mut self, _gate: Gate) {
        // File-based providers are read-only - ignore add_gate calls
    }
}
