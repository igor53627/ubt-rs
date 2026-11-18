//! Error types for the UBT crate.

use alloy_primitives::B256;
use thiserror::Error;

use crate::{Stem, TreeKey};

/// Errors that can occur during UBT operations.
#[derive(Debug, Error)]
pub enum UbtError {
    /// Key not found in tree
    #[error("key not found: {0}")]
    KeyNotFound(B256),

    /// Invalid stem length
    #[error("invalid stem length: expected 31 bytes, got {0}")]
    InvalidStemLength(usize),

    /// Invalid key length
    #[error("invalid key length: expected 32 bytes, got {0}")]
    InvalidKeyLength(usize),

    /// Tree depth exceeded maximum allowed depth.
    #[error("tree depth exceeded maximum allowed depth (depth={depth})")]
    TreeDepthExceeded {
        /// Depth, in bits from the root, at which two or more stems were still not separated.
        depth: usize,
    },

    /// Stem collision during insertion (should not happen with proper key derivation)
    #[error("stem collision at {0:?}")]
    StemCollision(Stem),

    /// Invalid proof
    #[error("invalid proof: {0}")]
    InvalidProof(String),

    /// Code too large
    #[error("code size {0} exceeds maximum allowed size")]
    CodeTooLarge(usize),

    /// Invalid code chunk
    #[error("invalid code chunk at index {0}")]
    InvalidCodeChunk(usize),

    /// Account not found
    #[error("account not found: {0}")]
    AccountNotFound(alloy_primitives::Address),

    /// Storage slot not found
    #[error("storage slot {slot} not found for account {account}")]
    StorageNotFound {
        /// Address of the account that owns the storage slot.
        account: alloy_primitives::Address,
        /// Storage slot number.
        slot: alloy_primitives::U256,
    },

    /// Invalid binary encoding
    #[error("invalid encoding: {0}")]
    InvalidEncoding(String),

    /// Entries of a streaming build are not in strictly ascending `(stem, subindex)` order.
    #[error(
        "entries are not in strictly ascending key order: {previous:?} is followed by {current:?}"
    )]
    EntriesNotSorted {
        /// Key of the entry that came first.
        previous: TreeKey,
        /// Key of the next entry. It is equal to `previous` or sorts before it.
        current: TreeKey,
    },
}

/// Result type alias for UBT operations.
pub type Result<T> = std::result::Result<T, UbtError>;
