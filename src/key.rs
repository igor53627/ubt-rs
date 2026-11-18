//! Tree key types and utilities.
//!
//! In EIP-7864, tree keys are 32 bytes where:
//! - First 31 bytes: stem (defines which 256-value subtree)
//! - Last byte: subindex (position within the subtree, 0-255)

use alloy_primitives::B256;
use std::fmt;

use crate::UbtError;

/// Length of a stem in bytes (31 bytes = 248 bits)
pub const STEM_LEN: usize = 31;

/// Number of bits in the subindex (8 bits = 256 possible values)
pub const SUBINDEX_BITS: usize = 8;

/// A 31-byte stem that identifies a subtree of 256 values.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Stem(pub [u8; STEM_LEN]);

impl Stem {
    /// Create a new stem from bytes.
    pub const fn new(bytes: [u8; STEM_LEN]) -> Self {
        Self(bytes)
    }

    /// Create a stem from a slice.
    ///
    /// # Panics
    ///
    /// Panics if the length of `slice` is not [`STEM_LEN`] (31). For a slice
    /// whose length is not known, use `Stem::try_from(slice)`.
    pub fn from_slice(slice: &[u8]) -> Self {
        let mut bytes = [0u8; STEM_LEN];
        bytes.copy_from_slice(slice);
        Self(bytes)
    }

    /// Get the underlying bytes.
    pub const fn as_bytes(&self) -> &[u8; STEM_LEN] {
        &self.0
    }

    /// Check if this stem is all zeros.
    pub fn is_zero(&self) -> bool {
        self.0.iter().all(|&b| b == 0)
    }

    /// Get bit at position (0 = MSB of first byte, 247 = LSB of last byte).
    /// This is used for tree traversal.
    ///
    /// # Panics
    ///
    /// Panics if `pos` is 248 or more.
    pub fn bit_at(&self, pos: usize) -> bool {
        assert!(
            pos < STEM_LEN * 8,
            "bit position {pos} is not in a 248-bit stem"
        );
        let byte_idx = pos / 8;
        let bit_idx = 7 - (pos % 8); // MSB first
        (self.0[byte_idx] >> bit_idx) & 1 == 1
    }

    /// Find the first bit position where two stems differ.
    /// Returns None if stems are equal.
    pub fn first_differing_bit(&self, other: &Self) -> Option<usize> {
        (0..STEM_LEN * 8).find(|&pos| self.bit_at(pos) != other.bit_at(pos))
    }
}

impl Ord for Stem {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.cmp(&other.0)
    }
}

impl PartialOrd for Stem {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Debug for Stem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Stem(0x{})", hex::encode(self.0))
    }
}

impl From<[u8; STEM_LEN]> for Stem {
    fn from(bytes: [u8; STEM_LEN]) -> Self {
        Self(bytes)
    }
}

impl TryFrom<&[u8]> for Stem {
    type Error = UbtError;

    /// Create a stem from a slice.
    ///
    /// # Errors
    ///
    /// Returns [`UbtError::InvalidStemLength`] if the length of `slice` is not
    /// [`STEM_LEN`] (31).
    fn try_from(slice: &[u8]) -> Result<Self, Self::Error> {
        let bytes: [u8; STEM_LEN] = slice
            .try_into()
            .map_err(|_| UbtError::InvalidStemLength(slice.len()))?;
        Ok(Self(bytes))
    }
}

/// Subindex within a stem's subtree (0-255).
pub type SubIndex = u8;

/// A complete 32-byte tree key (stem + subindex).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TreeKey {
    /// The 31-byte stem identifying the subtree.
    pub stem: Stem,
    /// The subindex within the subtree (0-255).
    pub subindex: SubIndex,
}

impl TreeKey {
    /// Create a new tree key from stem and subindex.
    pub const fn new(stem: Stem, subindex: SubIndex) -> Self {
        Self { stem, subindex }
    }

    /// Create a tree key from a 32-byte array.
    pub fn from_bytes(bytes: B256) -> Self {
        let mut stem_bytes = [0u8; STEM_LEN];
        stem_bytes.copy_from_slice(&bytes[..STEM_LEN]);
        Self {
            stem: Stem(stem_bytes),
            subindex: bytes[STEM_LEN],
        }
    }

    /// Convert to a 32-byte array.
    pub fn to_bytes(&self) -> B256 {
        let mut bytes = [0u8; 32];
        bytes[..STEM_LEN].copy_from_slice(&self.stem.0);
        bytes[STEM_LEN] = self.subindex;
        B256::from(bytes)
    }
}

impl fmt::Debug for TreeKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "TreeKey {{ stem: 0x{}, subindex: {} }}",
            hex::encode(self.stem.0),
            self.subindex
        )
    }
}

impl From<B256> for TreeKey {
    fn from(bytes: B256) -> Self {
        Self::from_bytes(bytes)
    }
}

impl From<TreeKey> for B256 {
    fn from(key: TreeKey) -> Self {
        key.to_bytes()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_stem_bit_at() {
        let mut bytes = [0u8; STEM_LEN];
        bytes[0] = 0b1000_0000; // MSB set
        let stem = Stem(bytes);

        assert!(stem.bit_at(0));
        assert!(!stem.bit_at(1));
        assert!(!stem.bit_at(7));
    }

    #[test]
    fn test_first_differing_bit() {
        let stem1 = Stem([0u8; STEM_LEN]);
        let mut bytes2 = [0u8; STEM_LEN];
        bytes2[0] = 0b1000_0000;
        let stem2 = Stem(bytes2);

        assert_eq!(stem1.first_differing_bit(&stem2), Some(0));

        let mut bytes3 = [0u8; STEM_LEN];
        bytes3[0] = 0b0000_0001;
        let stem3 = Stem(bytes3);

        assert_eq!(stem1.first_differing_bit(&stem3), Some(7));
    }

    #[test]
    fn test_stem_try_from_slice() {
        let mut bytes = [0u8; STEM_LEN];
        for (byte, value) in bytes.iter_mut().zip(1u8..=31) {
            *byte = value;
        }
        assert_eq!(Stem::try_from(&bytes[..]).unwrap(), Stem::new(bytes));

        for len in [0usize, 30, 32] {
            let slice = vec![0u8; len];
            let err = Stem::try_from(slice.as_slice()).unwrap_err();
            assert!(matches!(err, UbtError::InvalidStemLength(got) if got == len));
        }
    }

    #[test]
    fn test_tree_key_roundtrip() {
        let original = B256::repeat_byte(0x42);
        let key = TreeKey::from_bytes(original);
        let recovered = key.to_bytes();
        assert_eq!(original, recovered);
    }
}
