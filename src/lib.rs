//! # Unified Binary Tree (UBT)
//!
//! Implementation of EIP-7864: Ethereum state using a unified binary tree.
//!
//! This crate provides a binary tree structure intended to replace the hexary patricia trees
//! used in Ethereum. Key features:
//!
//! - **Single tree**: Account and storage tries are merged into a single tree with 32-byte keys
//! - **Code chunking**: Contract bytecode is chunked and stored in the tree
//! - **Data co-location**: Related data (nonce, balance, first storage slots, first code chunks)
//!   are grouped together in 256-value subtrees to reduce branch openings
//! - **ZK-friendly**: Designed for efficient proving in ZK circuits
//! - **Parallel hashing**: Uses rayon for concurrent stem hash computation (default feature)
//! - **Incremental updates**: O(D*C) root updates instead of O(S log S) rebuilds
//!
//! ## Tree Structure
//!
//! The tree uses 32-byte keys where:
//! - First 31 bytes: **stem** (defines the subtree)
//! - Last byte: **subindex** (position within the 256-value subtree)
//!
//! Node types:
//! - [`InternalNode`]: Has left_hash and right_hash
//! - [`StemNode`]: Has stem (31 bytes), left_hash and right_hash for its 256-value subtree
//! - [`LeafNode`]: Contains a 32-byte value or empty
//! - `EmptyNode`: Represents an empty node/subtree (hash = 0)
//!
//! ## Quick Start
//!
//! ```rust
//! use ubt::{UnifiedBinaryTree, TreeKey, Blake3Hasher, B256};
//!
//! let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
//! let key = TreeKey::from_bytes(B256::repeat_byte(0x01));
//! tree.insert(key, B256::repeat_byte(0x42));
//! let root = tree.root_hash();
//! ```
//!
//! ## Features
//!
//! - **`parallel`** (default): Enables parallel stem hashing via rayon. Provides significant
//!   speedup for trees with many dirty stems per rebuild cycle.
//! - **`serde`**: Enables serialization support for tree types.
//!
//! ## Performance Modes
//!
//! ### Parallel Hashing (default)
//!
//! When the `parallel` feature is enabled (default), stem hashes are computed concurrently
//! using rayon's parallel iterators. This is beneficial when many stems are modified
//! between `root_hash()` calls.
//!
//! ### Incremental Updates
//!
//! For block-by-block state updates where only a small subset of stems change,
//! enable incremental mode to cache intermediate node hashes:
//!
//! ```rust
//! use ubt::{UnifiedBinaryTree, Blake3Hasher};
//!
//! let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
//! // ... initial inserts ...
//! tree.root_hash(); // Initial full build
//!
//! // Enable incremental mode for subsequent updates
//! tree.enable_incremental_mode();
//!
//! // Future updates only recompute affected paths: O(D*C) vs O(S log S)
//! // where D=248 (tree depth) and C=changed stems per block
//! ```
//!
//! ## Hash Function
//!
//! **Note**: The hash function is not final per EIP-7864. This implementation uses BLAKE3
//! as a reference. Candidates include Keccak and Poseidon2.
//!
//! The [`Hasher`] trait is `Send + Sync` to support parallel hashing contexts.

#![cfg_attr(not(test), warn(unused_crate_dependencies))]

mod code;
mod compat_tests;
mod embedding;
mod error;
mod geth_compat;
mod hash;
mod key;
mod node;
mod proof;
mod streaming;
mod tree;

pub use error::UbtError;
pub use hash::{Blake3Hasher, Hasher, Sha256Hasher};
pub use key::{Stem, SubIndex, TreeKey, STEM_LEN, SUBINDEX_BITS};
pub use node::{InternalNode, LeafNode, Node, StemNode};

pub use code::{chunkify_code, CodeChunk};
pub use embedding::{
    get_basic_data_key, get_binary_tree_key, get_code_chunk_key, get_code_hash_key,
    get_storage_slot_key, get_storage_slot_key_u256, AccountStem, BasicDataLeaf,
    BASIC_DATA_BALANCE_OFFSET, BASIC_DATA_CODE_SIZE_OFFSET, BASIC_DATA_LEAF_KEY,
    BASIC_DATA_NONCE_OFFSET, CODE_HASH_LEAF_KEY, CODE_OFFSET, HEADER_STORAGE_OFFSET,
    STEM_SUBTREE_WIDTH,
};
pub use proof::{generate_stem_proof, Direction, MultiProof, Proof, ProofNode, Witness};
#[doc(hidden)]
pub use std::collections::HashMap;
pub use streaming::StreamingTreeBuilder;
pub use tree::UnifiedBinaryTree;

/// Re-export alloy primitives for convenience
pub use alloy_primitives::{Address, B256, U256};
