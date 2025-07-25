# Gate topology file format

The topology is stored as a sequence of fixed size records representing gates. Each record is 16 bytes long:

- **byte 0**   – gate operation as defined by `GateType` (u8).
- **bytes 1..5**   – little endian encoding of `wire_id_a`.
- **bytes 6..10**  – little endian encoding of `wire_id_b`.
- **bytes 11..15** – little endian encoding of `wire_id_c`.

Wire identifiers are stored using 5 bytes because `Wire.id` never exceeds `11_000_000_000` (less than 2^34).  Gates are appended sequentially so the file can be built incrementally without loading the entire circuit into memory.
