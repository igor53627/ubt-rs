//! Error types for the UBT crate.

use thiserror::Error;

use crate::TreeKey;

/// Errors that can occur during UBT operations.
///
/// The enum is non-exhaustive: a later release can add a variant, so a `match`
/// outside this crate needs a wildcard arm.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum UbtError {
    /// A slice does not have the length of a stem. See `TryFrom<&[u8]>` for
    /// [`Stem`](crate::Stem).
    #[error("invalid stem length: expected 31 bytes, got {0}")]
    InvalidStemLength(usize),

    /// Tree depth exceeded maximum allowed depth.
    #[error("tree depth exceeded maximum allowed depth (depth={depth})")]
    TreeDepthExceeded {
        /// Depth, in bits from the root, at which two or more stems were still not separated.
        depth: usize,
    },

    /// Invalid proof
    #[error("invalid proof: {0}")]
    InvalidProof(String),

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
