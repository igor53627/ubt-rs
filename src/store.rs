//! Storage backend abstraction for the UBT.
//!
//! The [`NodeStore`] trait abstracts how stem nodes are stored, enabling
//! custom backends (e.g., `RocksDB`, `redb`) for persistent storage.
//! The default [`InMemoryStore`] uses a `HashMap`.

use std::collections::HashMap;
use std::fmt::Debug;

use crate::{Stem, StemNode};

/// Backend storage for UBT stem nodes.
///
/// Implementations provide the key-value store that [`crate::UnifiedBinaryTree`]
/// uses for its stem node data. The default [`InMemoryStore`] wraps a `HashMap`.
///
/// A persistent store (e.g., backed by `RocksDB` or `redb`) must keep in memory
/// every stem node that it returns, because [`get`](Self::get) and
/// [`iter`](Self::iter) take `&self` and return references. It can flush dirty
/// nodes via a store-specific `commit()` method accessible through
/// [`UnifiedBinaryTree::store_mut`](crate::UnifiedBinaryTree::store_mut).
///
/// # Invariants
///
/// The tree relies on these rules and does not check them. A store that breaks
/// one of them gives a wrong root hash or wrong counts without an error.
///
/// - [`get`](Self::get), [`get_mut`](Self::get_mut), and
///   [`get_or_create`](Self::get_or_create) return a node whose `stem` field is
///   equal to the requested stem.
/// - [`iter`](Self::iter) gives each stem one time.
/// - [`value_count`](Self::value_count) is equal to the sum of `values.len()`
///   over all stem nodes.
/// - `clone()` gives an independent copy of the data. The tree derives `Clone`
///   and copies its hash caches, so a clone that shares data with the original
///   makes the caches of one tree stale when the other tree changes.
///
/// # Thread Safety
///
/// `Send + Sync` are required because the tree may hash stems in parallel
/// (via rayon when the `parallel` feature is enabled).
pub trait NodeStore: Clone + Debug + Send + Sync {
    /// Retrieve a stem node by its stem key.
    fn get(&self, stem: &Stem) -> Option<&StemNode>;

    /// Retrieve a mutable reference to a stem node.
    fn get_mut(&mut self, stem: &Stem) -> Option<&mut StemNode>;

    /// Get a mutable reference to a stem node, creating it if absent.
    ///
    /// If the stem does not exist, inserts a new `StemNode::new(stem)`.
    fn get_or_create(&mut self, stem: Stem) -> &mut StemNode;

    /// Remove a stem node. No-op if the stem does not exist.
    fn remove(&mut self, stem: &Stem);

    /// Number of stems in the store.
    fn len(&self) -> usize;

    /// Whether the store contains no stems.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Iterate over all `(stem, node)` pairs.
    fn iter(&self) -> impl Iterator<Item = (&Stem, &StemNode)>;

    /// Total number of non-empty values across all stems.
    fn value_count(&self) -> usize;

    /// Hint that the store should pre-allocate for `additional` stems.
    ///
    /// Default implementation is a no-op.
    fn reserve(&mut self, _additional: usize) {}
}

/// In-memory store backed by a `HashMap`.
///
/// This is the default store used by [`crate::UnifiedBinaryTree`].
#[derive(Clone, Debug)]
pub struct InMemoryStore {
    stems: HashMap<Stem, StemNode>,
}

impl InMemoryStore {
    /// Create a new empty store.
    #[must_use]
    pub fn new() -> Self {
        Self {
            stems: HashMap::new(),
        }
    }

    /// Create a new store with pre-allocated capacity.
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            stems: HashMap::with_capacity(capacity),
        }
    }
}

impl Default for InMemoryStore {
    fn default() -> Self {
        Self::new()
    }
}

impl NodeStore for InMemoryStore {
    fn get(&self, stem: &Stem) -> Option<&StemNode> {
        self.stems.get(stem)
    }

    fn get_mut(&mut self, stem: &Stem) -> Option<&mut StemNode> {
        self.stems.get_mut(stem)
    }

    fn get_or_create(&mut self, stem: Stem) -> &mut StemNode {
        self.stems
            .entry(stem)
            .or_insert_with(|| StemNode::new(stem))
    }

    fn remove(&mut self, stem: &Stem) {
        self.stems.remove(stem);
    }

    fn len(&self) -> usize {
        self.stems.len()
    }

    fn is_empty(&self) -> bool {
        self.stems.is_empty()
    }

    fn iter(&self) -> impl Iterator<Item = (&Stem, &StemNode)> {
        self.stems.iter()
    }

    fn value_count(&self) -> usize {
        self.stems.values().map(|s| s.values.len()).sum()
    }

    fn reserve(&mut self, additional: usize) {
        self.stems.reserve(additional);
    }
}
