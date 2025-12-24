#![no_main]

use libfuzzer_sys::fuzz_target;
use ubt::{get_basic_data_key, get_code_chunk_key, get_storage_slot_key, Address};

/// Fuzz embedding functions with arbitrary inputs
/// Tests that no address/slot combination causes panics
fuzz_target!(|data: &[u8]| {
    if data.len() < 52 {
        return;
    }

    // Parse address from first 20 bytes
    let addr_bytes: [u8; 20] = data[0..20].try_into().unwrap();
    let addr = Address::from(addr_bytes);

    // Parse slot from next 32 bytes
    let slot_bytes: [u8; 32] = data[20..52].try_into().unwrap();

    // get_storage_slot_key should never panic for any slot value
    // This includes slots with high byte = 0xff (previously caused panic)
    let key1 = get_storage_slot_key(&addr, &slot_bytes);
    let key2 = get_storage_slot_key(&addr, &slot_bytes);
    assert_eq!(key1, key2, "storage key must be deterministic");

    // get_basic_data_key should never panic
    let _basic = get_basic_data_key(&addr);

    // get_code_chunk_key should never panic
    // Use remaining bytes to determine chunk number
    if data.len() >= 60 {
        let chunk_bytes: [u8; 8] = data[52..60].try_into().unwrap();
        let chunk_num = u64::from_be_bytes(chunk_bytes);
        let _code = get_code_chunk_key(&addr, chunk_num);
    }

    // Test specific edge cases that previously caused issues
    // Slot with high byte = 0xff
    let mut slot_ff = [0u8; 32];
    slot_ff[0] = 0xff;
    slot_ff[31] = slot_bytes[31]; // Use fuzzed subindex
    let _key_ff = get_storage_slot_key(&addr, &slot_ff);

    // Max slot value
    let slot_max = [0xffu8; 32];
    let _key_max = get_storage_slot_key(&addr, &slot_max);
});
