#![no_main]

use libfuzzer_sys::fuzz_target;
use ubt::{chunkify_code, dechunkify_code, CodeChunk, B256};

/// Fuzz code chunking with arbitrary bytecode
/// Tests roundtrip and invariants
fuzz_target!(|data: &[u8]| {
    // Test chunkify/dechunkify roundtrip
    let chunks = chunkify_code(data);
    let recovered = dechunkify_code(&chunks, data.len());
    assert_eq!(data, recovered.as_slice(), "roundtrip failed");

    // Verify chunk invariants
    for chunk in &chunks {
        // leading_pushdata should be <= 31
        assert!(chunk.leading_pushdata <= 31, "leading_pushdata out of bounds");

        // encode/decode roundtrip
        let encoded = chunk.encode();
        let decoded = CodeChunk::decode(encoded);
        assert_eq!(chunk.leading_pushdata, decoded.leading_pushdata);
        assert_eq!(chunk.data, decoded.data);
    }
});
