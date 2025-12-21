//! Invariant checking for UBT simulation testing.
//!
//! Provides reference model and verification for simulation-based testing.
//! The key invariant: root hash from mutable tree must equal root hash from
//! fresh tree built from reference model.

use std::collections::BTreeMap;
use ubt::{Blake3Hasher, Hasher, StreamingTreeBuilder, TreeKey, B256};

/// A violation of an expected invariant during simulation.
#[derive(Debug, Clone)]
pub struct InvariantViolation {
    pub operation_index: usize,
    pub description: String,
    pub expected: String,
    pub actual: String,
}

impl std::fmt::Display for InvariantViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Invariant violation at op {}: {} (expected: {}, actual: {})",
            self.operation_index, self.description, self.expected, self.actual
        )
    }
}

impl std::error::Error for InvariantViolation {}

/// Operation types for UBT simulation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UbtOperation {
    Insert { key: [u8; 32], value: [u8; 32] },
    Delete { key: [u8; 32] },
    Get { key: [u8; 32] },
}

impl UbtOperation {
    pub fn key(&self) -> &[u8; 32] {
        match self {
            UbtOperation::Insert { key, .. } => key,
            UbtOperation::Delete { key } => key,
            UbtOperation::Get { key } => key,
        }
    }
}

/// Reference model for UBT state using BTreeMap.
///
/// Maintains expected state for verification against actual tree operations.
#[derive(Debug, Clone, Default)]
pub struct UbtReferenceModel {
    state: BTreeMap<[u8; 32], [u8; 32]>,
}

impl UbtReferenceModel {
    pub fn new() -> Self {
        Self {
            state: BTreeMap::new(),
        }
    }

    pub fn apply(&mut self, op: &UbtOperation) {
        match op {
            UbtOperation::Insert { key, value } => {
                if *value == [0u8; 32] {
                    self.state.remove(key);
                } else {
                    self.state.insert(*key, *value);
                }
            }
            UbtOperation::Delete { key } => {
                self.state.remove(key);
            }
            UbtOperation::Get { .. } => {}
        }
    }

    pub fn get(&self, key: &[u8; 32]) -> Option<&[u8; 32]> {
        self.state.get(key)
    }

    pub fn len(&self) -> usize {
        self.state.len()
    }

    pub fn is_empty(&self) -> bool {
        self.state.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = (&[u8; 32], &[u8; 32])> {
        self.state.iter()
    }

    pub fn contains(&self, key: &[u8; 32]) -> bool {
        self.state.contains_key(key)
    }

    pub fn clear(&mut self) {
        self.state.clear();
    }
}

/// Trait for Merkle root verification.
pub trait MerkleInvariantChecker {
    fn verify_root(
        &self,
        actual_root: B256,
        model: &UbtReferenceModel,
    ) -> Result<(), InvariantViolation>;

    fn verify_get(
        &self,
        key: &[u8; 32],
        actual_value: Option<B256>,
        model: &UbtReferenceModel,
    ) -> Result<(), InvariantViolation>;
}

/// UBT-specific Merkle invariant checker.
///
/// Uses StreamingTreeBuilder to rebuild tree from model and compare roots.
pub struct UbtMerkleChecker<H: Hasher = Blake3Hasher> {
    operation_index: usize,
    _marker: std::marker::PhantomData<H>,
}

impl<H: Hasher> Default for UbtMerkleChecker<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: Hasher> UbtMerkleChecker<H> {
    pub fn new() -> Self {
        Self {
            operation_index: 0,
            _marker: std::marker::PhantomData,
        }
    }

    pub fn set_operation_index(&mut self, index: usize) {
        self.operation_index = index;
    }

    fn build_root_from_model(&self, model: &UbtReferenceModel) -> B256 {
        if model.is_empty() {
            return B256::ZERO;
        }

        let mut entries: Vec<(TreeKey, B256)> = model
            .iter()
            .map(|(k, v)| {
                let key = TreeKey::from_bytes(B256::from_slice(k));
                let value = B256::from_slice(v);
                (key, value)
            })
            .collect();

        entries.sort_by(|a, b| (a.0.stem, a.0.subindex).cmp(&(b.0.stem, b.0.subindex)));

        let builder: StreamingTreeBuilder<H> = StreamingTreeBuilder::new();
        builder.build_root_hash(entries)
    }
}

impl<H: Hasher> MerkleInvariantChecker for UbtMerkleChecker<H> {
    fn verify_root(
        &self,
        actual_root: B256,
        model: &UbtReferenceModel,
    ) -> Result<(), InvariantViolation> {
        let expected_root = self.build_root_from_model(model);

        if actual_root != expected_root {
            return Err(InvariantViolation {
                operation_index: self.operation_index,
                description: "Root hash mismatch".to_string(),
                expected: format!("{:?}", expected_root),
                actual: format!("{:?}", actual_root),
            });
        }

        Ok(())
    }

    fn verify_get(
        &self,
        key: &[u8; 32],
        actual_value: Option<B256>,
        model: &UbtReferenceModel,
    ) -> Result<(), InvariantViolation> {
        let expected = model.get(key).map(|v| B256::from_slice(v));

        if actual_value != expected {
            return Err(InvariantViolation {
                operation_index: self.operation_index,
                description: format!("Get mismatch for key {:?}", &key[..4]),
                expected: format!("{:?}", expected),
                actual: format!("{:?}", actual_value),
            });
        }

        Ok(())
    }
}

/// Log of operations for replay and debugging.
#[derive(Debug, Clone, Default)]
pub struct OperationLog {
    operations: Vec<UbtOperation>,
}

impl OperationLog {
    pub fn new() -> Self {
        Self {
            operations: Vec::new(),
        }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            operations: Vec::with_capacity(capacity),
        }
    }

    pub fn record(&mut self, op: UbtOperation) {
        self.operations.push(op);
    }

    pub fn len(&self) -> usize {
        self.operations.len()
    }

    pub fn is_empty(&self) -> bool {
        self.operations.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = &UbtOperation> {
        self.operations.iter()
    }

    pub fn get(&self, index: usize) -> Option<&UbtOperation> {
        self.operations.get(index)
    }

    pub fn clear(&mut self) {
        self.operations.clear();
    }

    pub fn operations(&self) -> &[UbtOperation] {
        &self.operations
    }

    pub fn replay<F>(&self, mut f: F)
    where
        F: FnMut(usize, &UbtOperation),
    {
        for (i, op) in self.operations.iter().enumerate() {
            f(i, op);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ubt::UnifiedBinaryTree;

    #[test]
    fn test_reference_model_insert_get() {
        let mut model = UbtReferenceModel::new();
        let key = [1u8; 32];
        let value = [42u8; 32];

        model.apply(&UbtOperation::Insert { key, value });
        assert_eq!(model.get(&key), Some(&value));
        assert_eq!(model.len(), 1);
    }

    #[test]
    fn test_reference_model_delete() {
        let mut model = UbtReferenceModel::new();
        let key = [1u8; 32];
        let value = [42u8; 32];

        model.apply(&UbtOperation::Insert { key, value });
        model.apply(&UbtOperation::Delete { key });
        assert_eq!(model.get(&key), None);
        assert!(model.is_empty());
    }

    #[test]
    fn test_reference_model_insert_zero_deletes() {
        let mut model = UbtReferenceModel::new();
        let key = [1u8; 32];
        let value = [42u8; 32];

        model.apply(&UbtOperation::Insert { key, value });
        model.apply(&UbtOperation::Insert {
            key,
            value: [0u8; 32],
        });
        assert_eq!(model.get(&key), None);
    }

    #[test]
    fn test_merkle_checker_empty() {
        let checker: UbtMerkleChecker<Blake3Hasher> = UbtMerkleChecker::new();
        let model = UbtReferenceModel::new();
        assert!(checker.verify_root(B256::ZERO, &model).is_ok());
    }

    #[test]
    fn test_merkle_checker_single_entry() {
        let checker: UbtMerkleChecker<Blake3Hasher> = UbtMerkleChecker::new();
        let mut model = UbtReferenceModel::new();
        let key = [1u8; 32];
        let value = [42u8; 32];

        model.apply(&UbtOperation::Insert { key, value });

        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        tree.insert(TreeKey::from_bytes(B256::from_slice(&key)), B256::from_slice(&value));
        let root = tree.root_hash();

        assert!(checker.verify_root(root, &model).is_ok());
    }

    #[test]
    fn test_merkle_checker_mismatch() {
        let checker: UbtMerkleChecker<Blake3Hasher> = UbtMerkleChecker::new();
        let mut model = UbtReferenceModel::new();
        let key = [1u8; 32];
        let value = [42u8; 32];

        model.apply(&UbtOperation::Insert { key, value });

        let result = checker.verify_root(B256::ZERO, &model);
        assert!(result.is_err());
    }

    #[test]
    fn test_verify_get() {
        let checker: UbtMerkleChecker<Blake3Hasher> = UbtMerkleChecker::new();
        let mut model = UbtReferenceModel::new();
        let key = [1u8; 32];
        let value = [42u8; 32];

        model.apply(&UbtOperation::Insert { key, value });

        assert!(checker
            .verify_get(&key, Some(B256::from_slice(&value)), &model)
            .is_ok());
        assert!(checker.verify_get(&key, None, &model).is_err());
    }

    #[test]
    fn test_operation_log() {
        let mut log = OperationLog::new();
        let key = [1u8; 32];
        let value = [42u8; 32];

        log.record(UbtOperation::Insert { key, value });
        log.record(UbtOperation::Get { key });
        log.record(UbtOperation::Delete { key });

        assert_eq!(log.len(), 3);

        let mut count = 0;
        log.replay(|_, _| count += 1);
        assert_eq!(count, 3);
    }

    #[test]
    fn test_full_invariant_check() {
        let mut model = UbtReferenceModel::new();
        let mut tree: UnifiedBinaryTree<Blake3Hasher> = UnifiedBinaryTree::new();
        let mut checker: UbtMerkleChecker<Blake3Hasher> = UbtMerkleChecker::new();
        let mut log = OperationLog::new();

        for i in 0u8..10 {
            let mut key = [0u8; 32];
            key[0] = i;
            let value = [i + 1; 32];

            let op = UbtOperation::Insert { key, value };
            log.record(op.clone());

            model.apply(&op);
            tree.insert(TreeKey::from_bytes(B256::from_slice(&key)), B256::from_slice(&value));

            checker.set_operation_index(log.len() - 1);
            assert!(checker.verify_root(tree.root_hash(), &model).is_ok());
        }

        for i in 0u8..5 {
            let mut key = [0u8; 32];
            key[0] = i;

            let op = UbtOperation::Delete { key };
            log.record(op.clone());

            model.apply(&op);
            tree.delete(&TreeKey::from_bytes(B256::from_slice(&key)));

            checker.set_operation_index(log.len() - 1);
            assert!(checker.verify_root(tree.root_hash(), &model).is_ok());
        }
    }
}
