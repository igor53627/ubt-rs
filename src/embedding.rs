//! Tree embedding for Ethereum state.
//!
//! This module defines how Ethereum state (accounts, storage, code) is mapped
//! to tree keys per EIP-7864.
//!
//! ## Layout Overview
//!
//! Each account has a "base stem" derived from its address. Within that stem's subtree:
//! - Subindex 0: Basic data (version, code size, nonce, balance)
//! - Subindex 1: Code hash
//! - Subindexes 2-63: Reserved for future use
//! - Subindexes 64-127: First 64 storage slots (HEADER_STORAGE_OFFSET)
//! - Subindexes 128-255: First 128 code chunks (CODE_OFFSET)
//!
//! Storage slots beyond the first 64 and code chunks beyond the first 128
//! are stored in separate stems calculated from the account address and slot/chunk index.
//!
//! ## Key Derivation
//!
//! Per go-ethereum reference implementation, keys are derived using SHA256:
//! ```text
//! key = SHA256(zeroHash[:12] || address[:] || inputKey[:31])
//! key[31] = inputKey[31]  // subindex preserved
//! ```

use alloy_primitives::{Address, B256, U256};
use sha2::{Digest, Sha256};

use crate::{Stem, SubIndex, TreeKey, STEM_LEN};

/// Subindex for basic account data (nonce, balance, code size)
pub const BASIC_DATA_LEAF_KEY: SubIndex = 0;

/// Subindex for code hash
pub const CODE_HASH_LEAF_KEY: SubIndex = 1;

/// Offset in basic data leaf for code size (bytes 5-7)
pub const BASIC_DATA_CODE_SIZE_OFFSET: usize = 5;

/// Offset in basic data leaf for nonce (bytes 8-15)
pub const BASIC_DATA_NONCE_OFFSET: usize = 8;

/// Offset in basic data leaf for balance (bytes 16-31)
pub const BASIC_DATA_BALANCE_OFFSET: usize = 16;

/// Offset for first 64 storage slots within account stem (subindexes 64-127)
pub const HEADER_STORAGE_OFFSET: SubIndex = 64;

/// Offset for first 128 code chunks within account stem (subindexes 128-255)
pub const CODE_OFFSET: SubIndex = 128;

/// Width of a stem subtree (256 values)
pub const STEM_SUBTREE_WIDTH: u64 = 256;

/// Zero hash prefix used in key derivation (12 zero bytes)
const ZERO_PREFIX: [u8; 12] = [0u8; 12];

/// Derive a tree key using the go-ethereum algorithm.
///
/// Per reference implementation:
/// ```text
/// key = SHA256(zeroHash[:12] || address[:] || inputKey[:31])
/// key[31] = inputKey[31]
/// ```
pub fn get_binary_tree_key(address: &Address, input_key: &[u8; 32]) -> TreeKey {
    let mut hasher = Sha256::new();
    hasher.update(ZERO_PREFIX);
    hasher.update(address.as_slice());
    hasher.update(&input_key[..31]);

    let hash = hasher.finalize();
    let mut stem_bytes = [0u8; STEM_LEN];
    stem_bytes.copy_from_slice(&hash[..STEM_LEN]);

    TreeKey::new(Stem::new(stem_bytes), input_key[31])
}

/// Get the tree key for basic account data (nonce, balance, code size).
pub fn get_basic_data_key(address: &Address) -> TreeKey {
    let mut k = [0u8; 32];
    k[31] = BASIC_DATA_LEAF_KEY;
    get_binary_tree_key(address, &k)
}

/// Get the tree key for code hash.
pub fn get_code_hash_key(address: &Address) -> TreeKey {
    let mut k = [0u8; 32];
    k[31] = CODE_HASH_LEAF_KEY;
    get_binary_tree_key(address, &k)
}

/// Get the tree key for a storage slot.
///
/// Per EIP-7864:
/// - Slots 0-63: pos = HEADER_STORAGE_OFFSET + slot, stored in account stem
/// - Slots >= 64: pos = MAIN_STORAGE_OFFSET + slot (MAIN_STORAGE_OFFSET = 256^31)
/// - tree_index = pos // 256, subindex = pos % 256
pub fn get_storage_slot_key(address: &Address, slot: &[u8; 32]) -> TreeKey {
    let mut k = [0u8; 32];

    // Check if key belongs to account header (first 31 bytes zero, last byte < 64)
    let is_header_slot = slot[..31].iter().all(|&b| b == 0) && slot[31] < 64;

    if is_header_slot {
        // Header storage: pos = 64 + slot, tree_index = 0, subindex = 64 + slot
        k[31] = HEADER_STORAGE_OFFSET + slot[31];
    } else {
        // Main storage: pos = MAIN_STORAGE_OFFSET + slot = 256^31 + slot
        // tree_index = pos // 256 = 256^30 + slot // 256
        // subindex = pos % 256 = slot % 256 = slot[31]
        //
        // 256^30 as 31-byte big-endian: byte 0 = 1, rest = 0
        // slot // 256 as 31-byte big-endian: [slot[0], slot[1], ..., slot[30]]
        // Sum: tree_index[0] = 1 + slot[0], tree_index[1..31] = slot[1..31]
        // (with carry propagation)

        // Start with slot[0..31] shifted: tree_index = slot >> 8
        // Then add 256^30 (which is 1 in byte 0)

        // First, compute tree_index bytes 1..31 = slot[1..31] (no addition needed here)
        for i in (1..31).rev() {
            k[i] = slot[i];
        }

        // Byte 0: 1 (from 256^30) + slot[0], modulo 256.
        // Per EIP-7864, storage keys are full 256-bit values, so we must
        // support all possible slot[0] values including 0xff. Adding 1 to
        // the most significant byte corresponds to adding 256^30 to the
        // 31-byte tree_index, modulo 256^31.
        k[0] = slot[0].wrapping_add(1);

        // subindex = slot % 256 = slot[31]
        k[31] = slot[31];
    }

    get_binary_tree_key(address, &k)
}

/// Get the tree key for a storage slot from U256.
pub fn get_storage_slot_key_u256(address: &Address, slot: U256) -> TreeKey {
    get_storage_slot_key(address, &slot.to_be_bytes::<32>())
}

/// Get the tree key for a code chunk.
///
/// Per EIP-7864:
/// - First 128 chunks (pos 128-255) go in account stem at subindex 128+chunk_num
/// - Chunks >= 128 go in separate stems calculated from stem_index
pub fn get_code_chunk_key(address: &Address, chunk_number: u64) -> TreeKey {
    let pos = CODE_OFFSET as u64 + chunk_number;

    // First 128 chunks (pos < 256) go in account stem
    if pos < STEM_SUBTREE_WIDTH {
        let mut k = [0u8; 32];
        k[31] = pos as u8; // subindex 128..255
        return get_binary_tree_key(address, &k);
    }

    // Chunks >= 128 go in separate stems per EIP
    let stem_index = pos / STEM_SUBTREE_WIDTH;
    let subindex = (pos % STEM_SUBTREE_WIDTH) as u8;

    let mut k = [0u8; 32];
    // Encode stem_index into first 31 bytes (big-endian)
    let stem_bytes = stem_index.to_be_bytes();
    k[23..31].copy_from_slice(&stem_bytes); // align to end of 31-byte prefix
    k[31] = subindex;
    get_binary_tree_key(address, &k)
}

/// Basic account data packed into a single 32-byte leaf.
///
/// Layout (per EIP-7864 / go-ethereum):
/// - Byte 0: Version (currently 0)
/// - Bytes 1-4: Reserved
/// - Bytes 5-7: Code size (3 bytes, big-endian)
/// - Bytes 8-15: Nonce (8 bytes, big-endian)
/// - Bytes 16-31: Balance (16 bytes, big-endian)
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct BasicDataLeaf {
    /// Version byte (currently 0)
    pub version: u8,
    /// Code size in bytes (max ~16MB with 3 bytes)
    pub code_size: u32,
    /// Account nonce
    pub nonce: u64,
    /// Account balance
    pub balance: u128,
}

impl BasicDataLeaf {
    /// Create a new basic data leaf.
    pub const fn new(nonce: u64, balance: u128, code_size: u32) -> Self {
        Self {
            version: 0,
            code_size,
            nonce,
            balance,
        }
    }

    /// Encode to a 32-byte value.
    pub fn encode(&self) -> B256 {
        let mut bytes = [0u8; 32];
        bytes[0] = self.version;
        // bytes[1..5] = reserved
        bytes[5..8].copy_from_slice(&self.code_size.to_be_bytes()[1..4]); // 3 bytes
        bytes[8..16].copy_from_slice(&self.nonce.to_be_bytes());
        bytes[16..32].copy_from_slice(&self.balance.to_be_bytes());
        B256::from(bytes)
    }

    /// Decode from a 32-byte value.
    pub fn decode(value: B256) -> Self {
        let bytes = value.as_slice();

        let mut code_size_bytes = [0u8; 4];
        code_size_bytes[1..4].copy_from_slice(&bytes[5..8]);

        let mut nonce_bytes = [0u8; 8];
        nonce_bytes.copy_from_slice(&bytes[8..16]);

        let mut balance_bytes = [0u8; 16];
        balance_bytes.copy_from_slice(&bytes[16..32]);

        Self {
            version: bytes[0],
            code_size: u32::from_be_bytes(code_size_bytes),
            nonce: u64::from_be_bytes(nonce_bytes),
            balance: u128::from_be_bytes(balance_bytes),
        }
    }
}

/// Helper struct for computing account keys.
pub struct AccountStem {
    /// The account address
    pub address: Address,
}

impl AccountStem {
    /// Create a new account stem helper from an address.
    pub fn new(address: Address) -> Self {
        Self { address }
    }

    /// Get the tree key for basic data.
    pub fn basic_data_key(&self) -> TreeKey {
        get_basic_data_key(&self.address)
    }

    /// Get the tree key for code hash.
    pub fn code_hash_key(&self) -> TreeKey {
        get_code_hash_key(&self.address)
    }

    /// Get the tree key for a storage slot.
    pub fn storage_key(&self, slot: U256) -> TreeKey {
        get_storage_slot_key_u256(&self.address, slot)
    }

    /// Get the tree key for a code chunk.
    pub fn code_chunk_key(&self, chunk_index: u64) -> TreeKey {
        get_code_chunk_key(&self.address, chunk_index)
    }
}

// Legacy exports for backwards compatibility
#[deprecated(
    since = "0.2.0",
    note = "Use `get_basic_data_key` or `AccountStem::basic_data_key` instead"
)]
#[allow(unused_imports)]
pub use get_basic_data_key as account_stem_basic_data;

#[deprecated(
    since = "0.2.0",
    note = "Use `get_code_chunk_key` or `AccountStem::code_chunk_key` instead"
)]
#[allow(unused_imports)]
pub use get_code_chunk_key as code_chunk_key;

#[deprecated(
    since = "0.2.0",
    note = "Use `get_storage_slot_key_u256` or `AccountStem::storage_key` instead"
)]
#[allow(unused_imports)]
pub use get_storage_slot_key_u256 as storage_key;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_data_roundtrip() {
        let original = BasicDataLeaf::new(42, 1000000, 1024);
        let encoded = original.encode();
        let decoded = BasicDataLeaf::decode(encoded);
        assert_eq!(original, decoded);
    }

    #[test]
    fn test_storage_key_header_slots() {
        let address = Address::repeat_byte(0x42);
        let base_key = get_basic_data_key(&address);

        for slot in 0..64u8 {
            let mut slot_bytes = [0u8; 32];
            slot_bytes[31] = slot;
            let key = get_storage_slot_key(&address, &slot_bytes);
            // Header slots share the same stem as basic data
            assert_eq!(key.stem, base_key.stem);
            assert_eq!(key.subindex, HEADER_STORAGE_OFFSET + slot);
        }
    }

    #[test]
    fn test_storage_key_main_storage() {
        let address = Address::repeat_byte(0x42);
        let base_key = get_basic_data_key(&address);

        // Slot 100 should be in main storage (different stem)
        let mut slot_bytes = [0u8; 32];
        slot_bytes[31] = 100;
        let key = get_storage_slot_key(&address, &slot_bytes);

        assert_ne!(key.stem, base_key.stem);
    }

    #[test]
    fn test_code_chunk_key() {
        let address = Address::repeat_byte(0x42);

        // Test that code chunk keys are deterministic
        let key0a = get_code_chunk_key(&address, 0);
        let key0b = get_code_chunk_key(&address, 0);
        assert_eq!(key0a, key0b);

        // Different chunks have different keys
        let key1 = get_code_chunk_key(&address, 1);
        assert_ne!(key0a.to_bytes(), key1.to_bytes());

        // Different addresses have different keys for same chunk
        let addr2 = Address::repeat_byte(0x43);
        let key0_addr2 = get_code_chunk_key(&addr2, 0);
        assert_ne!(key0a.stem, key0_addr2.stem);
    }

    #[test]
    fn test_key_derivation_deterministic() {
        let address = Address::repeat_byte(0x42);
        let key1 = get_basic_data_key(&address);
        let key2 = get_basic_data_key(&address);
        assert_eq!(key1, key2);
    }

    #[test]
    fn test_different_addresses_different_stems() {
        let addr1 = Address::repeat_byte(0x01);
        let addr2 = Address::repeat_byte(0x02);

        let key1 = get_basic_data_key(&addr1);
        let key2 = get_basic_data_key(&addr2);

        assert_ne!(key1.stem, key2.stem);
    }

    #[test]
    fn test_code_chunks_share_account_stem() {
        let address = Address::repeat_byte(0x42);
        let basic_key = get_basic_data_key(&address);

        // First 128 code chunks should share stem with basic data
        for chunk_idx in 0..128u64 {
            let chunk_key = get_code_chunk_key(&address, chunk_idx);
            assert_eq!(
                chunk_key.stem, basic_key.stem,
                "Chunk {} should share account stem",
                chunk_idx
            );
            assert_eq!(chunk_key.subindex, (128 + chunk_idx) as u8);
        }

        // Chunk 128+ should be in different stems
        let chunk_128_key = get_code_chunk_key(&address, 128);
        assert_ne!(chunk_128_key.stem, basic_key.stem);
    }

    #[test]
    fn test_main_storage_slot_key_correctness() {
        // Per EIP-7864:
        // pos = MAIN_STORAGE_OFFSET + storage_key (for storage_key >= 64)
        // tree_index = pos // STEM_SUBTREE_WIDTH
        // subindex = pos % STEM_SUBTREE_WIDTH
        //
        // MAIN_STORAGE_OFFSET = 256^31, STEM_SUBTREE_WIDTH = 256
        // So: tree_index = 256^30 + storage_key // 256
        //     subindex = storage_key % 256

        let address = Address::repeat_byte(0x42);

        // Test case 1: slot 64 (first main storage slot)
        // tree_index = 256^30 + 0 = 256^30 (in 31-byte BE: [1, 0, 0, ..., 0])
        // subindex = 64
        let slot_64 = U256::from(64);
        let key_64 = get_storage_slot_key_u256(&address, slot_64);
        assert_eq!(key_64.subindex, 64);

        // Test case 2: slot 100
        // tree_index = 256^30 + 0 = 256^30
        // subindex = 100
        let slot_100 = U256::from(100);
        let key_100 = get_storage_slot_key_u256(&address, slot_100);
        assert_eq!(key_100.subindex, 100);

        // Slots 64 and 100 should share the same stem (both in first main storage subtree)
        assert_eq!(key_64.stem, key_100.stem);

        // Test case 3: slot 256 (crosses into next subtree)
        // tree_index = 256^30 + 1
        // subindex = 0
        let slot_256 = U256::from(256);
        let key_256 = get_storage_slot_key_u256(&address, slot_256);
        assert_eq!(key_256.subindex, 0);
        assert_ne!(
            key_256.stem, key_64.stem,
            "slot 256 should be in different stem than slot 64"
        );

        // Test case 4: slot 257
        // tree_index = 256^30 + 1
        // subindex = 1
        let slot_257 = U256::from(257);
        let key_257 = get_storage_slot_key_u256(&address, slot_257);
        assert_eq!(key_257.subindex, 1);
        assert_eq!(
            key_257.stem, key_256.stem,
            "slot 257 should share stem with slot 256"
        );

        // Test case 5: slot 511 (last in second subtree)
        // tree_index = 256^30 + 1
        // subindex = 255
        let slot_511 = U256::from(511);
        let key_511 = get_storage_slot_key_u256(&address, slot_511);
        assert_eq!(key_511.subindex, 255);
        assert_eq!(key_511.stem, key_256.stem);

        // Test case 6: slot 512 (third subtree)
        // tree_index = 256^30 + 2
        // subindex = 0
        let slot_512 = U256::from(512);
        let key_512 = get_storage_slot_key_u256(&address, slot_512);
        assert_eq!(key_512.subindex, 0);
        assert_ne!(key_512.stem, key_256.stem);

        // Test case 7: Large slot value to verify tree_index encoding
        // slot = 0x0102...1F20 (arbitrary 32-byte value)
        // tree_index[0] = 1 + slot[0], tree_index[1..31] = slot[1..31]
        // subindex = slot[31]
        let mut large_slot_bytes = [0u8; 32];
        large_slot_bytes[0] = 0x01;
        large_slot_bytes[1] = 0x02;
        large_slot_bytes[30] = 0x1F;
        large_slot_bytes[31] = 0x20;
        let _large_slot = U256::from_be_bytes(large_slot_bytes);
        let key_large = get_storage_slot_key(&address, &large_slot_bytes);
        assert_eq!(key_large.subindex, 0x20);

        // Verify the input_key (tree_index || subindex) has correct structure
        // tree_index[0] should be 1 + 0x01 = 0x02
        // tree_index[1] should be 0x02
        // tree_index[30] should be 0x1F
        // We can verify indirectly by checking different slots produce different stems
        let mut other_slot_bytes = large_slot_bytes;
        other_slot_bytes[1] = 0x03; // Different tree_index
        let key_other = get_storage_slot_key(&address, &other_slot_bytes);
        assert_ne!(
            key_large.stem, key_other.stem,
            "different tree_index should produce different stem"
        );
    }

    #[test]
    fn test_storage_slot_high_byte_0xff() {
        let address = Address::repeat_byte(0x42);

        // Test slot with high byte = 0xff (previously caused panic)
        // This is a valid keccak-derived storage slot from real Ethereum state
        let mut slot_bytes = [0u8; 32];
        slot_bytes[0] = 0xff;
        slot_bytes[31] = 0x20;

        // Should not panic - must handle all 256-bit storage keys per EIP-7864
        let key1 = get_storage_slot_key(&address, &slot_bytes);
        let key2 = get_storage_slot_key(&address, &slot_bytes);
        assert_eq!(key1, key2, "storage key must be deterministic");

        // Verify subindex is preserved
        assert_eq!(key1.subindex, 0x20);

        // tree_index[0] = 0xff + 1 = 0x00 (wrapping)
        // Verify by checking it's different from slot with high byte 0xfe
        let mut slot_fe = slot_bytes;
        slot_fe[0] = 0xfe;
        let key_fe = get_storage_slot_key(&address, &slot_fe);
        assert_ne!(
            key1.stem, key_fe.stem,
            "0xff and 0xfe high bytes should produce different stems"
        );
    }

    #[test]
    fn test_storage_slot_all_high_bytes() {
        let address = Address::repeat_byte(0x42);

        // Test slot = 0xffffffff...ffff (max U256)
        let slot_max = [0xffu8; 32];
        let key_max = get_storage_slot_key(&address, &slot_max);
        assert_eq!(key_max.subindex, 0xff);

        // Test slot = 0xff00...0000
        let mut slot_ff00 = [0u8; 32];
        slot_ff00[0] = 0xff;
        let key_ff00 = get_storage_slot_key(&address, &slot_ff00);
        assert_eq!(key_ff00.subindex, 0x00);

        // Both should work without panic
        assert_ne!(key_max.stem, key_ff00.stem);
    }

    #[test]
    fn test_storage_slot_boundary_values() {
        let address = Address::repeat_byte(0x42);

        // Test all boundary values for high byte
        for high_byte in [0x00, 0x01, 0x7f, 0x80, 0xfe, 0xff] {
            let mut slot = [0u8; 32];
            slot[0] = high_byte;
            slot[31] = 0x42;

            // Should not panic for any high byte value
            let key = get_storage_slot_key(&address, &slot);
            assert_eq!(key.subindex, 0x42);
        }
    }
}
