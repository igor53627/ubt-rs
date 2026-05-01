//! Compact binary encoding for UBT nodes.
//!
//! Provides encode/decode for [`StemNode`] using a bitmap-based format
//! suitable for persistent storage backends.
//!
//! ## `StemNode` Wire Format
//!
//! ```text
//! [1B type=0x02] [31B stem] [32B bitmap] [N×32B values]
//! ```
//!
//! - **Type byte**: `0x02` identifies a stem node
//! - **Stem**: 31 raw stem bytes
//! - **Bitmap**: 256 bits (32 bytes). Bit `i` is set when subindex `i` has a value.
//!   Bit ordering: `byte[i/8] & (1 << (i%8))`
//! - **Values**: `N` raw 32-byte values in ascending subindex order,
//!   where `N` = popcount(bitmap)
//!
//! Total size: `64 + N×32` bytes.

use alloy_primitives::B256;

use crate::{error::Result, Stem, StemNode, UbtError, STEM_LEN};

/// Type tag for stem nodes.
pub const STEM_NODE_TAG: u8 = 0x02;

const HEADER_SIZE: usize = 1 + STEM_LEN + 32;

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
    let mut buf = Vec::with_capacity(HEADER_SIZE + node.values.len() * 32);

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
    if bytes.len() < HEADER_SIZE {
        return Err(UbtError::InvalidEncoding(format!(
            "buffer too short: expected at least {HEADER_SIZE} bytes, got {}",
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

    let bitmap = &bytes[1 + STEM_LEN..HEADER_SIZE];
    let value_count: usize = bitmap.iter().map(|b| b.count_ones() as usize).sum();

    let expected_size = HEADER_SIZE + value_count * 32;
    if bytes.len() < expected_size {
        return Err(UbtError::InvalidEncoding(format!(
            "buffer too short for {value_count} values: expected {expected_size} bytes, got {}",
            bytes.len()
        )));
    }

    let mut node = StemNode::new(stem);
    let mut offset = HEADER_SIZE;
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
    HEADER_SIZE + node.values.len() * 32
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_roundtrip_empty() {
        let node = StemNode::new(Stem::new([0xAA; 31]));
        let bytes = encode_stem_node(&node);
        assert_eq!(bytes.len(), HEADER_SIZE);

        let decoded = decode_stem_node(&bytes).unwrap();
        assert_eq!(decoded.stem, node.stem);
        assert!(decoded.values.is_empty());
    }

    #[test]
    fn test_roundtrip_single_value() {
        let mut node = StemNode::new(Stem::new([0x01; 31]));
        node.set_value(42, B256::repeat_byte(0xFF));

        let bytes = encode_stem_node(&node);
        assert_eq!(bytes.len(), HEADER_SIZE + 32);

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
        assert_eq!(bytes.len(), HEADER_SIZE + 3 * 32);

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
        assert_eq!(bytes.len(), HEADER_SIZE + 256 * 32);

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
        assert_eq!(encoded_stem_size(&node), HEADER_SIZE);

        node.set_value(0, B256::repeat_byte(1));
        node.set_value(100, B256::repeat_byte(2));
        assert_eq!(encoded_stem_size(&node), HEADER_SIZE + 2 * 32);
        assert_eq!(encode_stem_node(&node).len(), encoded_stem_size(&node));
    }

    #[test]
    fn test_decode_too_short() {
        let err = decode_stem_node(&[0x02; 10]).unwrap_err();
        assert!(matches!(err, UbtError::InvalidEncoding(_)));
    }

    #[test]
    fn test_decode_wrong_tag() {
        let mut bytes = vec![0x00; HEADER_SIZE];
        bytes[0] = 0xFF;
        let err = decode_stem_node(&bytes).unwrap_err();
        assert!(matches!(err, UbtError::InvalidEncoding(_)));
    }

    #[test]
    fn test_decode_truncated_values() {
        let mut node = StemNode::new(Stem::new([0; 31]));
        node.set_value(0, B256::repeat_byte(0x42));
        let bytes = encode_stem_node(&node);

        let truncated = &bytes[..HEADER_SIZE + 16];
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
}
