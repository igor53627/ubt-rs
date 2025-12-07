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
        Self { leading_pushdata, data }
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

/// PUSH opcodes and their data sizes.
fn push_size(opcode: u8) -> usize {
    if (0x60..=0x7f).contains(&opcode) {
        (opcode - 0x5f) as usize // PUSH1 = 0x60 pushes 1 byte, PUSH32 = 0x7f pushes 32 bytes
    } else {
        0
    }
}

/// Chunkify bytecode into 31-byte chunks with PUSHDATA tracking.
///
/// Returns a vector of code chunks. Each chunk contains:
/// - 1 byte: count of leading bytes that are PUSHDATA
/// - 31 bytes: the actual code/data
///
/// This allows code analysis to skip PUSHDATA bytes when looking for valid opcodes.
pub fn chunkify_code(bytecode: &[u8]) -> Vec<CodeChunk> {
    if bytecode.is_empty() {
        return vec![];
    }

    let num_chunks = (bytecode.len() + CODE_CHUNK_DATA_SIZE - 1) / CODE_CHUNK_DATA_SIZE;
    let mut chunks = Vec::with_capacity(num_chunks);
    
    // Track how many bytes of PUSHDATA remain from previous instruction
    let mut pushdata_remaining: usize = 0;

    for chunk_idx in 0..num_chunks {
        let start = chunk_idx * CODE_CHUNK_DATA_SIZE;
        let end = std::cmp::min(start + CODE_CHUNK_DATA_SIZE, bytecode.len());
        
        // How many bytes at the start of this chunk are PUSHDATA from previous chunk?
        let leading_pushdata = std::cmp::min(pushdata_remaining, end - start) as u8;
        
        let mut data = [0u8; CODE_CHUNK_DATA_SIZE];
        let chunk_data = &bytecode[start..end];
        data[..chunk_data.len()].copy_from_slice(chunk_data);
        
        chunks.push(CodeChunk::new(leading_pushdata, data));
        
        // Update pushdata_remaining for next chunk
        if pushdata_remaining > CODE_CHUNK_DATA_SIZE {
            pushdata_remaining -= CODE_CHUNK_DATA_SIZE;
        } else {
            // Scan this chunk for PUSH instructions
            pushdata_remaining = 0;
            let mut i = pushdata_remaining.max(leading_pushdata as usize);
            while i < chunk_data.len() {
                let opcode = chunk_data[i];
                let push_bytes = push_size(opcode);
                if push_bytes > 0 {
                    let bytes_in_chunk = chunk_data.len() - i - 1;
                    if push_bytes > bytes_in_chunk {
                        pushdata_remaining = push_bytes - bytes_in_chunk;
                    }
                    i += push_bytes + 1;
                } else {
                    i += 1;
                }
            }
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
