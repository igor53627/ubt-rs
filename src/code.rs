//! Code chunkification for EIP-7864.
//!
//! Contract bytecode is split into 31-byte chunks. The first byte of each chunk
//! indicates how many of the following bytes are PUSHDATA from a previous chunk
//! (i.e., data that should not be interpreted as opcodes).

use alloy_primitives::B256;

/// Size of code data per chunk (31 bytes)
pub const CODE_CHUNK_DATA_SIZE: usize = 31;

/// A code chunk with leading PUSHDATA count.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CodeChunk {
    /// Number of leading bytes that are PUSHDATA (0-31)
    pub leading_pushdata: u8,
    /// The 31 bytes of code/data
    pub data: [u8; CODE_CHUNK_DATA_SIZE],
}

impl CodeChunk {
    /// Create a new code chunk.
    pub const fn new(leading_pushdata: u8, data: [u8; CODE_CHUNK_DATA_SIZE]) -> Self {
        Self {
            leading_pushdata,
            data,
        }
    }

    /// Encode to a 32-byte value.
    pub fn encode(&self) -> B256 {
        let mut bytes = [0u8; 32];
        bytes[0] = self.leading_pushdata;
        bytes[1..32].copy_from_slice(&self.data);
        B256::from(bytes)
    }

    /// Decode from a 32-byte value.
    pub fn decode(value: B256) -> Self {
        let bytes = value.as_slice();
        let mut data = [0u8; CODE_CHUNK_DATA_SIZE];
        data.copy_from_slice(&bytes[1..32]);
        Self {
            leading_pushdata: bytes[0],
            data,
        }
    }
}

/// Chunkify bytecode into 31-byte chunks with PUSHDATA tracking.
///
/// Returns a vector of code chunks. Each chunk contains:
/// - 1 byte: count of leading bytes that are PUSHDATA
/// - 31 bytes: the actual code/data
///
/// This allows code analysis to skip PUSHDATA bytes when looking for valid opcodes.
///
/// The leading PUSHDATA count is always bounded by `CODE_CHUNK_DATA_SIZE` (31),
/// so all casts to `u8` are safe.
pub fn chunkify_code(bytecode: &[u8]) -> Vec<CodeChunk> {
    if bytecode.is_empty() {
        return vec![];
    }

    let num_chunks = bytecode.len().div_ceil(CODE_CHUNK_DATA_SIZE);
    let mut chunks = Vec::with_capacity(num_chunks);

    // Mirrors Geth's chunkOffset / codeOffset tracking exactly.
    let mut chunk_offset: usize = 0;
    let mut code_offset: usize = 0;

    for i in 0..num_chunks {
        let end = std::cmp::min(bytecode.len(), CODE_CHUNK_DATA_SIZE * (i + 1));

        let mut data = [0u8; CODE_CHUNK_DATA_SIZE];
        let src = &bytecode[CODE_CHUNK_DATA_SIZE * i..end];
        data[..src.len()].copy_from_slice(src);

        if chunk_offset > CODE_CHUNK_DATA_SIZE {
            // PUSH data overflows this entire chunk — metadata = StemSize (31)
            #[allow(clippy::cast_possible_truncation)]
            let md = CODE_CHUNK_DATA_SIZE as u8; // 31 always fits in u8
            chunks.push(CodeChunk::new(md, data));
            chunk_offset = 1;
            continue;
        }

        // Normal case: metadata = chunk_offset
        #[allow(clippy::cast_possible_truncation)]
        let leading = chunk_offset as u8;
        chunks.push(CodeChunk::new(leading, data));
        chunk_offset = 0;

        // Scan for PUSH instructions in the bytecode covered by this chunk
        while code_offset < end {
            let opcode = bytecode[code_offset];
            if (0x60..=0x7f).contains(&opcode) {
                // PUSH1..PUSH32
                code_offset += (opcode - 0x60 + 1) as usize;
                if code_offset + 1 >= CODE_CHUNK_DATA_SIZE * (i + 1) {
                    code_offset += 1;
                    chunk_offset = code_offset - CODE_CHUNK_DATA_SIZE * (i + 1);
                    break;
                }
            }
            code_offset += 1;
        }
    }

    chunks
}

/// Reconstruct bytecode from chunks.
pub fn dechunkify_code(chunks: &[CodeChunk], code_size: usize) -> Vec<u8> {
    let mut bytecode = Vec::with_capacity(code_size);

    for chunk in chunks {
        let remaining = code_size.saturating_sub(bytecode.len());
        let to_copy = std::cmp::min(remaining, CODE_CHUNK_DATA_SIZE);
        bytecode.extend_from_slice(&chunk.data[..to_copy]);
    }

    bytecode
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_code() {
        let chunks = chunkify_code(&[]);
        assert!(chunks.is_empty());
    }

    #[test]
    fn test_simple_code() {
        let code = vec![0x60, 0x00, 0x60, 0x00]; // PUSH1 0 PUSH1 0
        let chunks = chunkify_code(&code);

        assert_eq!(chunks.len(), 1);
        assert_eq!(chunks[0].leading_pushdata, 0);
        assert_eq!(&chunks[0].data[..4], &code[..]);
    }

    #[test]
    fn test_push_spanning_chunks() {
        // Create code where PUSH32 spans two chunks
        let mut code = vec![0x7f]; // PUSH32
        code.extend_from_slice(&[0x11; 32]); // 32 bytes of push data

        let chunks = chunkify_code(&code);

        assert_eq!(chunks.len(), 2);
        assert_eq!(chunks[0].leading_pushdata, 0); // First chunk starts with PUSH32 opcode
        assert_eq!(chunks[1].leading_pushdata, 2); // Second chunk has 2 bytes of pushdata (31 bytes in first chunk, 2 remain)
    }

    #[test]
    fn test_roundtrip() {
        let original = vec![0x60, 0x80, 0x60, 0x40, 0x52]; // PUSH1 0x80 PUSH1 0x40 MSTORE
        let chunks = chunkify_code(&original);
        let recovered = dechunkify_code(&chunks, original.len());
        assert_eq!(original, recovered);
    }

    #[test]
    fn test_multi_chunk_push_overflow() {
        // From issue #71: code where PUSH data overflows across multiple chunk boundaries
        let code = hex::decode(
            "d76cd86a332eccc8fc09612a4bee018df261bf00aa5076287faf5f09b0737f\
             4224338e894f4f24665e21d39d4c6ec40310ffefe6923cdcc93ab9709d0c58\
             4d11f505f95d4a42bf22c7",
        )
        .unwrap();

        let chunks = chunkify_code(&code);

        assert_eq!(chunks[0].leading_pushdata, 0x00);
        assert_eq!(chunks[1].leading_pushdata, 0x0f); // 15
        assert_eq!(chunks[2].leading_pushdata, 0x0e); // 14 - must match Geth
    }

    #[test]
    fn test_push32_full_chunk_overflow() {
        // PUSH32 at last byte of chunk 0: its 32 bytes of data span all of chunk 1
        // and 1 byte into chunk 2. Chunk 1 should have metadata = 31 (full overflow).
        let mut code = vec![0x00; 30]; // 30 bytes of filler
        code.push(0x7f); // PUSH32 at byte 30 (last byte of chunk 0)
        code.extend_from_slice(&[0xAA; 32]); // 32 bytes of push data

        let chunks = chunkify_code(&code);

        assert_eq!(chunks.len(), 3);
        assert_eq!(chunks[0].leading_pushdata, 0); // no leading pushdata
        assert_eq!(chunks[1].leading_pushdata, 31); // entire chunk is pushdata
        assert_eq!(chunks[2].leading_pushdata, 1); // 1 byte of pushdata remains
    }

    #[test]
    fn test_truncated_push_at_eof() {
        // PUSH4 at byte 29 of a 31-byte chunk: opcode needs 4 immediate bytes
        // but only 1 byte remains in the bytecode. The chunk should still
        // record the correct overflow (even though the data is truncated).
        let mut code = vec![0x00; 29]; // 29 bytes of filler
        code.push(0x63); // PUSH4 at byte 29
        code.push(0xBB); // 1 byte of push data (only 1 of 4 available)

        let chunks = chunkify_code(&code);

        assert_eq!(chunks.len(), 1);
        assert_eq!(chunks[0].leading_pushdata, 0);
    }

    #[test]
    fn test_code_chunk_encode_decode() {
        let mut data = [0u8; 31];
        data[0] = 0x60;
        data[1] = 0x80;
        let chunk = CodeChunk::new(5, data);

        let encoded = chunk.encode();
        let decoded = CodeChunk::decode(encoded);

        assert_eq!(chunk, decoded);
    }
}
