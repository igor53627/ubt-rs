#![no_main]

use libfuzzer_sys::fuzz_target;
use ubt::{BasicDataLeaf, B256};

/// Fuzz BasicDataLeaf encode/decode with arbitrary bytes
fuzz_target!(|data: &[u8]| {
    if data.len() < 32 {
        return;
    }

    // Test decode from arbitrary 32 bytes
    let bytes: [u8; 32] = data[0..32].try_into().unwrap();
    let value = B256::from(bytes);
    let decoded = BasicDataLeaf::decode(value);

    // Re-encode and verify fields are preserved
    let reencoded = decoded.encode();
    let redecoded = BasicDataLeaf::decode(reencoded);

    assert_eq!(decoded.version, redecoded.version);
    assert_eq!(decoded.nonce, redecoded.nonce);
    assert_eq!(decoded.balance, redecoded.balance);
    // code_size is only 24 bits, so mask it
    assert_eq!(decoded.code_size & 0x00FFFFFF, redecoded.code_size);
});
