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
//!
//! ## Tree Structure
//!
//! The tree uses 32-byte keys where:
//! - First 31 bytes: **stem** (defines the subtree)
//! - Last byte: **subindex** (position within the 256-value subtree)
//!
//! Node types:
//! - `InternalNode`: Has left_hash and right_hash
//! - `StemNode`: Has stem (31 bytes), left_hash and right_hash for its 256-value subtree
//! - `LeafNode`: Contains a 32-byte value or empty
//! - `EmptyNode`: Represents an empty node/subtree (hash = 0)
//!
//! ## Hash Function
//!
//! **Note**: The hash function is not final per EIP-7864. This implementation uses BLAKE3
//! as a reference. Candidates include Keccak and Poseidon2.

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
