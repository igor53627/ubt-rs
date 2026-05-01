//! Compact binary encoding for UBT nodes.
//!
//! All node types use a 1-byte type tag prefix:
//!
//! | Tag | Type | Size |
//! |-----|------|------|
//! | `0x00` | Empty | 1 byte |
//! | `0x01` | Internal | 65 bytes (tag + two 32B hashes) |
//! | `0x02` | Stem | 64 + N×32 bytes (tag + stem + bitmap + values) |
//! | `0x03` | Leaf | 33 bytes (tag + 32B value) |
//!
//! ## `StemNode` layout
//!
//! ```text
//! [1B type=0x02] [31B stem] [32B bitmap] [N×32B values]
//! ```
//!
//! Bitmap: 256 bits, bit `i` set = subindex `i` present.
//! Bit ordering: `byte[i/8] & (1 << (i%8))`.
//! Values in ascending subindex order, only for set bits.

use alloy_primitives::B256;

use crate::{error::Result, Stem, StemNode, UbtError, STEM_LEN};

/// Type tag for empty nodes.
pub const EMPTY_NODE_TAG: u8 = 0x00;
/// Type tag for internal nodes (two child hashes).
pub const INTERNAL_NODE_TAG: u8 = 0x01;
/// Type tag for stem nodes (bitmap + values).
pub const STEM_NODE_TAG: u8 = 0x02;
/// Type tag for leaf nodes (single value).
pub const LEAF_NODE_TAG: u8 = 0x03;

const STEM_HEADER_SIZE: usize = 1 + STEM_LEN + 32;
const INTERNAL_SIZE: usize = 1 + 32 + 32;
const LEAF_SIZE: usize = 1 + 32;

/// Encode a [`StemNode`] into compact binary format.
///
/// # Example
///
/// ```
/// use ubt::{Stem, StemNode, B256};
/// use ubt::codec::encode_stem_node;
///
/// let mut node = StemNode::new(Stem::new([0u8; 31]));
/// node.set_value(0, B256::repeat_byte(0x42));
///
/// let bytes = encode_stem_node(&node);
/// assert_eq!(bytes.len(), 64 + 32); // header + 1 value
/// ```
pub fn encode_stem_node(node: &StemNode) -> Vec<u8> {
    let mut buf = Vec::with_capacity(STEM_HEADER_SIZE + node.values.len() * 32);

    buf.push(STEM_NODE_TAG);
    buf.extend_from_slice(node.stem.as_bytes());

    let mut bitmap = [0u8; 32];
    for &subindex in node.values.keys() {
        bitmap[subindex as usize / 8] |= 1 << (subindex % 8);
    }
    buf.extend_from_slice(&bitmap);

    let mut indices: Vec<u8> = node.values.keys().copied().collect();
    indices.sort_unstable();
    for idx in indices {
        buf.extend_from_slice(node.values[&idx].as_slice());
    }

    buf
}

/// Decode a [`StemNode`] from compact binary format.
///
/// # Errors
///
/// Returns [`UbtError::InvalidEncoding`] if the buffer is too short,
/// has a wrong type tag, or contains inconsistent bitmap/value data.
pub fn decode_stem_node(bytes: &[u8]) -> Result<StemNode> {
    if bytes.len() < STEM_HEADER_SIZE {
        return Err(UbtError::InvalidEncoding(format!(
            "stem node: expected at least {STEM_HEADER_SIZE} bytes, got {}",
            bytes.len()
        )));
    }

    if bytes[0] != STEM_NODE_TAG {
        return Err(UbtError::InvalidEncoding(format!(
            "expected stem node tag 0x{STEM_NODE_TAG:02x}, got 0x{:02x}",
            bytes[0]
        )));
    }

    let mut stem_bytes = [0u8; STEM_LEN];
    stem_bytes.copy_from_slice(&bytes[1..=STEM_LEN]);
    let stem = Stem::new(stem_bytes);

    let bitmap = &bytes[1 + STEM_LEN..STEM_HEADER_SIZE];
    let value_count: usize = bitmap.iter().map(|b| b.count_ones() as usize).sum();

    let expected_size = STEM_HEADER_SIZE + value_count * 32;
    if bytes.len() != expected_size {
        return Err(UbtError::InvalidEncoding(format!(
            "stem node: expected {expected_size} bytes, got {}",
            bytes.len()
        )));
    }

    let mut node = StemNode::new(stem);
    let mut offset = STEM_HEADER_SIZE;
    for subindex in 0u8..=255 {
        if bitmap[subindex as usize / 8] & (1 << (subindex % 8)) != 0 {
            let value = B256::from_slice(&bytes[offset..offset + 32]);
            node.set_value(subindex, value);
            offset += 32;
        }
    }

    Ok(node)
}

/// Returns the encoded size of a stem node without allocating.
#[must_use]
pub fn encoded_stem_size(node: &StemNode) -> usize {
    STEM_HEADER_SIZE + node.values.len() * 32
}

/// Encode an internal node as `[0x01] [32B left_hash] [32B right_hash]`.
pub fn encode_internal_node(left_hash: &B256, right_hash: &B256) -> Vec<u8> {
    let mut buf = Vec::with_capacity(INTERNAL_SIZE);
    buf.push(INTERNAL_NODE_TAG);
    buf.extend_from_slice(left_hash.as_slice());
    buf.extend_from_slice(right_hash.as_slice());
    buf
}

/// Decode an internal node from `[0x01] [32B left_hash] [32B right_hash]`.
///
/// # Errors
///
/// Returns [`UbtError::InvalidEncoding`] on wrong tag or insufficient bytes.
pub fn decode_internal_node(bytes: &[u8]) -> Result<(B256, B256)> {
    if bytes.len() != INTERNAL_SIZE {
        return Err(UbtError::InvalidEncoding(format!(
            "internal node: expected {INTERNAL_SIZE} bytes, got {}",
            bytes.len()
        )));
    }
    if bytes[0] != INTERNAL_NODE_TAG {
        return Err(UbtError::InvalidEncoding(format!(
            "expected internal node tag 0x{INTERNAL_NODE_TAG:02x}, got 0x{:02x}",
            bytes[0]
        )));
    }
    let left = B256::from_slice(&bytes[1..33]);
    let right = B256::from_slice(&bytes[33..65]);
    Ok((left, right))
}

/// Encode a leaf node as `[0x03] [32B value]`.
pub fn encode_leaf_node(value: &B256) -> Vec<u8> {
    let mut buf = Vec::with_capacity(LEAF_SIZE);
    buf.push(LEAF_NODE_TAG);
    buf.extend_from_slice(value.as_slice());
    buf
}

/// Decode a leaf node from `[0x03] [32B value]`.
///
/// # Errors
///
/// Returns [`UbtError::InvalidEncoding`] on wrong tag or insufficient bytes.
pub fn decode_leaf_node(bytes: &[u8]) -> Result<B256> {
    if bytes.len() != LEAF_SIZE {
        return Err(UbtError::InvalidEncoding(format!(
            "leaf node: expected {LEAF_SIZE} bytes, got {}",
            bytes.len()
        )));
    }
    if bytes[0] != LEAF_NODE_TAG {
        return Err(UbtError::InvalidEncoding(format!(
            "expected leaf node tag 0x{LEAF_NODE_TAG:02x}, got 0x{:02x}",
            bytes[0]
        )));
    }
    Ok(B256::from_slice(&bytes[1..33]))
}

/// Encode an empty node as `[0x00]`.
#[must_use]
pub fn encode_empty_node() -> Vec<u8> {
    vec![EMPTY_NODE_TAG]
}

/// A decoded node from the wire format.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DecodedNode {
    /// Empty node.
    Empty,
    /// Internal node with left and right child hashes.
    Internal {
        /// Left child hash.
        left_hash: B256,
        /// Right child hash.
        right_hash: B256,
    },
    /// Stem node with values.
    Stem(StemNode),
    /// Leaf node with a value.
    Leaf {
        /// The 32-byte value.
        value: B256,
    },
}

/// Decode any node type by dispatching on the type tag.
///
/// # Errors
///
/// Returns [`UbtError::InvalidEncoding`] if the buffer is empty,
/// has an unknown tag, or is malformed.
pub fn decode_node(bytes: &[u8]) -> Result<DecodedNode> {
    if bytes.is_empty() {
        return Err(UbtError::InvalidEncoding("empty buffer".to_string()));
    }
    match bytes[0] {
        EMPTY_NODE_TAG if bytes.len() == 1 => Ok(DecodedNode::Empty),
        EMPTY_NODE_TAG => Err(UbtError::InvalidEncoding(format!(
            "empty node: expected 1 byte, got {}",
            bytes.len()
        ))),
        INTERNAL_NODE_TAG => {
            let (left, right) = decode_internal_node(bytes)?;
            Ok(DecodedNode::Internal {
                left_hash: left,
                right_hash: right,
            })
        }
        STEM_NODE_TAG => Ok(DecodedNode::Stem(decode_stem_node(bytes)?)),
        LEAF_NODE_TAG => Ok(DecodedNode::Leaf {
            value: decode_leaf_node(bytes)?,
        }),
        tag => Err(UbtError::InvalidEncoding(format!(
            "unknown node type tag: 0x{tag:02x}"
        ))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_roundtrip_empty() {
        let node = StemNode::new(Stem::new([0xAA; 31]));
        let bytes = encode_stem_node(&node);
        assert_eq!(bytes.len(), STEM_HEADER_SIZE);

        let decoded = decode_stem_node(&bytes).unwrap();
        assert_eq!(decoded.stem, node.stem);
        assert!(decoded.values.is_empty());
    }

    #[test]
    fn test_roundtrip_single_value() {
        let mut node = StemNode::new(Stem::new([0x01; 31]));
        node.set_value(42, B256::repeat_byte(0xFF));

        let bytes = encode_stem_node(&node);
        assert_eq!(bytes.len(), STEM_HEADER_SIZE + 32);

        let decoded = decode_stem_node(&bytes).unwrap();
        assert_eq!(decoded.stem, node.stem);
        assert_eq!(decoded.get_value(42), Some(B256::repeat_byte(0xFF)));
        assert_eq!(decoded.values.len(), 1);
    }

    #[test]
    fn test_roundtrip_sparse() {
        let mut node = StemNode::new(Stem::new([0x00; 31]));
        node.set_value(0, B256::repeat_byte(0x01));
        node.set_value(127, B256::repeat_byte(0x02));
        node.set_value(255, B256::repeat_byte(0x03));

        let bytes = encode_stem_node(&node);
        assert_eq!(bytes.len(), STEM_HEADER_SIZE + 3 * 32);

        let decoded = decode_stem_node(&bytes).unwrap();
        assert_eq!(decoded.get_value(0), Some(B256::repeat_byte(0x01)));
        assert_eq!(decoded.get_value(127), Some(B256::repeat_byte(0x02)));
        assert_eq!(decoded.get_value(255), Some(B256::repeat_byte(0x03)));
        assert_eq!(decoded.get_value(1), None);
        assert_eq!(decoded.values.len(), 3);
    }

    #[test]
    fn test_roundtrip_full() {
        let mut node = StemNode::new(Stem::new([0xBB; 31]));
        for i in 0u16..256 {
            node.set_value(i as u8, B256::repeat_byte((i as u8).max(1)));
        }

        let bytes = encode_stem_node(&node);
        assert_eq!(bytes.len(), STEM_HEADER_SIZE + 256 * 32);

        let decoded = decode_stem_node(&bytes).unwrap();
        assert_eq!(decoded.values.len(), 256);
        for i in 0u16..256 {
            assert_eq!(
                decoded.get_value(i as u8),
                Some(B256::repeat_byte((i as u8).max(1)))
            );
        }
    }

    #[test]
    fn test_encoded_size() {
        let mut node = StemNode::new(Stem::new([0; 31]));
        assert_eq!(encoded_stem_size(&node), STEM_HEADER_SIZE);

        node.set_value(0, B256::repeat_byte(1));
        node.set_value(100, B256::repeat_byte(2));
        assert_eq!(encoded_stem_size(&node), STEM_HEADER_SIZE + 2 * 32);
        assert_eq!(encode_stem_node(&node).len(), encoded_stem_size(&node));
    }

    #[test]
    fn test_decode_too_short() {
        let err = decode_stem_node(&[0x02; 10]).unwrap_err();
        assert!(matches!(err, UbtError::InvalidEncoding(_)));
    }

    #[test]
    fn test_decode_wrong_tag() {
        let mut bytes = vec![0x00; STEM_HEADER_SIZE];
        bytes[0] = 0xFF;
        let err = decode_stem_node(&bytes).unwrap_err();
        assert!(matches!(err, UbtError::InvalidEncoding(_)));
    }

    #[test]
    fn test_decode_truncated_values() {
        let mut node = StemNode::new(Stem::new([0; 31]));
        node.set_value(0, B256::repeat_byte(0x42));
        let bytes = encode_stem_node(&node);

        let truncated = &bytes[..STEM_HEADER_SIZE + 16];
        let err = decode_stem_node(truncated).unwrap_err();
        assert!(matches!(err, UbtError::InvalidEncoding(_)));
    }

    #[test]
    fn test_wire_format_layout() {
        let mut stem_bytes = [0u8; 31];
        stem_bytes[0] = 0xAB;
        let mut node = StemNode::new(Stem::new(stem_bytes));
        node.set_value(0, B256::repeat_byte(0x11));
        node.set_value(8, B256::repeat_byte(0x22));

        let bytes = encode_stem_node(&node);

        assert_eq!(bytes[0], STEM_NODE_TAG);
        assert_eq!(bytes[1], 0xAB);
        assert_eq!(bytes[2..32], [0u8; 30]);

        // Bitmap: subindex 0 → byte[0] bit 0, subindex 8 → byte[1] bit 0
        assert_eq!(bytes[32], 0x01);
        assert_eq!(bytes[33], 0x01);
        assert_eq!(bytes[34..64], [0u8; 30]);

        // Values in order: subindex 0 first, then subindex 8
        assert_eq!(&bytes[64..96], B256::repeat_byte(0x11).as_slice());
        assert_eq!(&bytes[96..128], B256::repeat_byte(0x22).as_slice());
    }

    #[test]
    fn test_internal_roundtrip() {
        let left = B256::repeat_byte(0xAA);
        let right = B256::repeat_byte(0xBB);
        let bytes = encode_internal_node(&left, &right);
        assert_eq!(bytes.len(), INTERNAL_SIZE);

        let (l, r) = decode_internal_node(&bytes).unwrap();
        assert_eq!(l, left);
        assert_eq!(r, right);
    }

    #[test]
    fn test_leaf_roundtrip() {
        let value = B256::repeat_byte(0x42);
        let bytes = encode_leaf_node(&value);
        assert_eq!(bytes.len(), LEAF_SIZE);

        let decoded = decode_leaf_node(&bytes).unwrap();
        assert_eq!(decoded, value);
    }

    #[test]
    fn test_empty_roundtrip() {
        let bytes = encode_empty_node();
        assert_eq!(bytes.len(), 1);
        assert_eq!(bytes[0], EMPTY_NODE_TAG);

        let decoded = decode_node(&bytes).unwrap();
        assert_eq!(decoded, DecodedNode::Empty);
    }

    #[test]
    fn test_decode_node_dispatches() {
        let stem_bytes = encode_stem_node(&StemNode::new(Stem::new([0; 31])));
        assert!(matches!(
            decode_node(&stem_bytes).unwrap(),
            DecodedNode::Stem(_)
        ));

        let internal_bytes = encode_internal_node(&B256::ZERO, &B256::ZERO);
        assert!(matches!(
            decode_node(&internal_bytes).unwrap(),
            DecodedNode::Internal { .. }
        ));

        let leaf_bytes = encode_leaf_node(&B256::repeat_byte(1));
        assert!(matches!(
            decode_node(&leaf_bytes).unwrap(),
            DecodedNode::Leaf { .. }
        ));
    }

    #[test]
    fn test_decode_node_unknown_tag() {
        let err = decode_node(&[0xFF]).unwrap_err();
        assert!(matches!(err, UbtError::InvalidEncoding(_)));
    }

    #[test]
    fn test_decode_node_empty_buffer() {
        let err = decode_node(&[]).unwrap_err();
        assert!(matches!(err, UbtError::InvalidEncoding(_)));
    }

    #[test]
    fn test_reject_trailing_bytes() {
        let mut leaf = encode_leaf_node(&B256::repeat_byte(0x42));
        leaf.push(0xDE);
        assert!(decode_leaf_node(&leaf).is_err());

        let mut internal = encode_internal_node(&B256::ZERO, &B256::ZERO);
        internal.push(0xDE);
        assert!(decode_internal_node(&internal).is_err());

        let mut stem = encode_stem_node(&StemNode::new(Stem::new([0; 31])));
        stem.push(0xDE);
        assert!(decode_stem_node(&stem).is_err());

        assert!(decode_node(&[EMPTY_NODE_TAG, 0xFF]).is_err());
    }
}
