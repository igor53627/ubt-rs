//! UBT adapter implementing TestableDatabase trait.

use crate::simulation::workload::{KeyValueEntries, TestableDatabase};
use std::collections::BTreeMap;
use std::convert::Infallible;
use ubt::{B256, Blake3Hasher, TreeKey, UnifiedBinaryTree};

/// UBT database wrapper for simulation testing.
pub struct UbtDatabase {
    tree: UnifiedBinaryTree<Blake3Hasher>,
    entries: BTreeMap<[u8; 32], [u8; 32]>,
    incremental_mode: bool,
}

impl TestableDatabase for UbtDatabase {
    type Error = Infallible;

    fn create() -> Self {
        Self {
            tree: UnifiedBinaryTree::new(),
            entries: BTreeMap::new(),
            incremental_mode: false,
        }
    }

    fn insert(&mut self, key: [u8; 32], value: [u8; 32]) -> Result<(), Self::Error> {
        let tree_key = TreeKey::from_bytes(B256::from(key));
        let b256_value = B256::from(value);
        self.tree.insert(tree_key, b256_value);
        self.entries.insert(key, value);
        Ok(())
    }

    fn get(&self, key: [u8; 32]) -> Result<Option<[u8; 32]>, Self::Error> {
        let tree_key = TreeKey::from_bytes(B256::from(key));
        let result = self.tree.get(&tree_key).map(|b256| b256.0);
        Ok(result)
    }

    fn delete(&mut self, key: [u8; 32]) -> Result<bool, Self::Error> {
        let tree_key = TreeKey::from_bytes(B256::from(key));
        let existed = self.tree.get(&tree_key).is_some();
        if existed {
            self.tree.insert(tree_key, B256::ZERO);
            self.entries.remove(&key);
        }
        Ok(existed)
    }

    fn sync(&mut self) -> Result<[u8; 32], Self::Error> {
        let root = self.tree.root_hash();
        Ok(root.0)
    }

    fn count(&self) -> usize {
        self.entries.len()
    }

    fn scan_all(&self) -> Result<KeyValueEntries, Self::Error> {
        let entries: KeyValueEntries = self.entries.iter().map(|(k, v)| (*k, *v)).collect();
        Ok(entries)
    }

    fn enable_incremental_mode(&mut self) {
        if !self.incremental_mode {
            self.tree.enable_incremental_mode();
            // Prime the cache
            let _ = self.tree.root_hash();
            self.incremental_mode = true;
        }
    }

    fn disable_incremental_mode(&mut self) {
        if self.incremental_mode {
            self.tree.disable_incremental_mode();
            self.incremental_mode = false;
        }
    }

    fn is_incremental_mode(&self) -> bool {
        self.incremental_mode
    }

    fn clear_caches(&mut self) {
        // Disable and re-enable to clear internal caches
        let was_incremental = self.incremental_mode;
        if was_incremental {
            self.tree.disable_incremental_mode();
        }
        // Force a rebuild to clear any cached state
        let _ = self.tree.root_hash();
        if was_incremental {
            self.tree.enable_incremental_mode();
            let _ = self.tree.root_hash();
        }
    }

    fn force_full_rebuild(&mut self) -> Result<[u8; 32], Self::Error> {
        // Temporarily disable incremental mode to force full rebuild
        let was_incremental = self.incremental_mode;
        if was_incremental {
            self.tree.disable_incremental_mode();
        }
        let root = self.tree.root_hash();
        if was_incremental {
            self.tree.enable_incremental_mode();
            let _ = self.tree.root_hash(); // Re-prime cache
        }
        Ok(root.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ubt_adapter_basic() {
        let mut db = UbtDatabase::create();
        
        let key = [1u8; 32];
        let value = [42u8; 32];
        
        db.insert(key, value).unwrap();
        assert_eq!(db.get(key).unwrap(), Some(value));
        assert_eq!(db.count(), 1);
        
        let root = db.sync().unwrap();
        assert_ne!(root, [0u8; 32]);
    }

    #[test]
    fn test_ubt_adapter_delete() {
        let mut db = UbtDatabase::create();
        
        let key = [1u8; 32];
        let value = [42u8; 32];
        
        db.insert(key, value).unwrap();
        assert!(db.delete(key).unwrap());
        assert!(!db.delete(key).unwrap());
    }

    #[test]
    fn test_ubt_adapter_scan() {
        let mut db = UbtDatabase::create();
        
        let key1 = [1u8; 32];
        let key2 = [2u8; 32];
        let value = [42u8; 32];
        
        db.insert(key1, value).unwrap();
        db.insert(key2, value).unwrap();
        
        let entries = db.scan_all().unwrap();
        assert_eq!(entries.len(), 2);
        assert!(entries[0].0 < entries[1].0);
    }
}
