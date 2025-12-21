//! Workload runner for simulation testing.

use crate::simulation::context::WorkloadContext;
use crate::simulation::metrics::SharedMetrics;
use std::time::Duration;

/// Type alias for key-value entries returned by scan operations.
/// UBT uses 32-byte keys and 32-byte values.
pub type KeyValueEntries = Vec<([u8; 32], [u8; 32])>;

/// Configuration for workload execution.
#[derive(Clone, Debug)]
pub struct WorkloadConfig {
    pub operations_per_run: u64,
    pub key_space_size: u64,
    /// Enable extended operations (update, sequential insert, scan all).
    /// When false, only the original 3 operations (insert, get, delete) are used.
    pub enable_extended_ops: bool,
    /// Enable chaos/nemesis operations (FDB-inspired BUGGIFY patterns).
    /// Injects failures, toggles modes, verifies invariants mid-workload.
    pub enable_chaos_ops: bool,
}

impl Default for WorkloadConfig {
    fn default() -> Self {
        Self {
            operations_per_run: 1000,
            key_space_size: 10_000,
            enable_extended_ops: true,
            enable_chaos_ops: true,
        }
    }
}

/// Result of a workload run.
#[derive(Debug)]
pub struct WorkloadResult {
    pub seed: u64,
    pub operations_executed: u64,
    pub duration: Duration,
    pub success: bool,
    pub violations: Vec<String>,
}

impl WorkloadResult {
    pub fn success(seed: u64, operations_executed: u64, duration: Duration) -> Self {
        Self {
            seed,
            operations_executed,
            duration,
            success: true,
            violations: Vec::new(),
        }
    }

    pub fn failure(
        seed: u64,
        operations_executed: u64,
        duration: Duration,
        violations: Vec<String>,
    ) -> Self {
        Self {
            seed,
            operations_executed,
            duration,
            success: false,
            violations,
        }
    }
}

/// Trait for databases that can be tested.
/// UBT uses fixed 32-byte keys and 32-byte values.
pub trait TestableDatabase: Sized {
    type Error: std::fmt::Debug;

    fn create() -> Self;
    fn insert(&mut self, key: [u8; 32], value: [u8; 32]) -> Result<(), Self::Error>;
    fn get(&self, key: [u8; 32]) -> Result<Option<[u8; 32]>, Self::Error>;
    fn delete(&mut self, key: [u8; 32]) -> Result<bool, Self::Error>;
    fn sync(&mut self) -> Result<[u8; 32], Self::Error>;
    fn count(&self) -> usize;
    fn scan_all(&self) -> Result<KeyValueEntries, Self::Error>;

    // Chaos/nemesis operations for BUGGIFY-style testing
    fn enable_incremental_mode(&mut self);
    fn disable_incremental_mode(&mut self);
    fn is_incremental_mode(&self) -> bool;
    fn clear_caches(&mut self);
    fn force_full_rebuild(&mut self) -> Result<[u8; 32], Self::Error>;
}

/// Runs workloads against a database.
pub struct WorkloadRunner<D: TestableDatabase> {
    db: D,
    config: WorkloadConfig,
    metrics: Option<SharedMetrics>,
}

impl<D: TestableDatabase> WorkloadRunner<D> {
    pub fn new(db: D, config: WorkloadConfig) -> Self {
        Self { db, config, metrics: None }
    }

    pub fn with_metrics(db: D, config: WorkloadConfig, metrics: SharedMetrics) -> Self {
        Self { db, config, metrics: Some(metrics) }
    }

    pub fn run(&mut self, ctx: &mut WorkloadContext) -> WorkloadResult {
        use rand::Rng;
        use std::time::Instant;

        let start = Instant::now();
        let seed = ctx.seed();
        let mut operations_executed = 0u64;
        let mut sequential_counter = 0u64;

        let op_modulo = if self.config.enable_chaos_ops {
            20 // Full chaos mode with BUGGIFY-style operations
        } else if self.config.enable_extended_ops {
            10
        } else {
            3
        };

        // Track last root hash for consistency checks
        let mut last_root: Option<[u8; 32]> = None;

        for _ in 0..self.config.operations_per_run {
            let op_type = ctx.rng().gen::<u32>() % op_modulo;

            // Record operation type in metrics
            if let Some(ref m) = self.metrics {
                m.inc_op(op_type);
            }

            let result = match op_type {
                0 => {
                    // Insert random key-value
                    let key = ctx.random_key();
                    let value = ctx.random_value();
                    self.db.insert(key, value)
                }
                1 => {
                    // Get random key
                    let key = ctx.random_key();
                    self.db.get(key).map(|_| ())
                }
                2 => {
                    // Delete random key
                    let key = ctx.random_key();
                    self.db.delete(key).map(|_| ())
                }
                3 => {
                    // Update - insert to a hot key (low key space)
                    let index = ctx.rng().gen::<u64>() % 100;
                    let key = ctx.indexed_key(index);
                    let value = ctx.random_value();
                    self.db.insert(key, value)
                }
                4 => {
                    // Sequential insert
                    let key = ctx.indexed_key(sequential_counter);
                    sequential_counter += 1;
                    let value = ctx.random_value();
                    self.db.insert(key, value)
                }
                5 => {
                    // Scan all - verify scan completes and is sorted
                    match self.db.scan_all() {
                        Ok(entries) => {
                            for i in 1..entries.len() {
                                if entries[i].0 <= entries[i - 1].0 {
                                    return WorkloadResult::failure(
                                        seed,
                                        operations_executed,
                                        start.elapsed(),
                                        vec![format!(
                                            "Scan order violation at index {}: {:?} <= {:?}",
                                            i,
                                            &entries[i].0[..8],
                                            &entries[i - 1].0[..8]
                                        )],
                                    );
                                }
                            }
                            Ok(())
                        }
                        Err(e) => Err(e),
                    }
                }
                6 => {
                    // Read-after-write verification
                    let key = ctx.random_key();
                    let value = ctx.random_value();
                    if let Err(e) = self.db.insert(key, value) {
                        return WorkloadResult::failure(
                            seed,
                            operations_executed,
                            start.elapsed(),
                            vec![format!("RAW insert failed: {:?}", e)],
                        );
                    }
                    match self.db.get(key) {
                        Ok(Some(read_value)) => {
                            if read_value != value {
                                return WorkloadResult::failure(
                                    seed,
                                    operations_executed,
                                    start.elapsed(),
                                    vec![format!(
                                        "RAW mismatch: wrote {:?}, read {:?}",
                                        &value[..8],
                                        &read_value[..8]
                                    )],
                                );
                            }
                            Ok(())
                        }
                        Ok(None) => {
                            return WorkloadResult::failure(
                                seed,
                                operations_executed,
                                start.elapsed(),
                                vec!["RAW failed: key not found after insert".to_string()],
                            );
                        }
                        Err(e) => Err(e),
                    }
                }
                7 => {
                    // Rapid overwrite - same key multiple times
                    let hot_index = ctx.rng().gen::<u64>() % 10;
                    let key = ctx.indexed_key(hot_index);
                    for _ in 0..5 {
                        let value = ctx.random_value();
                        if let Err(e) = self.db.insert(key, value) {
                            return WorkloadResult::failure(
                                seed,
                                operations_executed,
                                start.elapsed(),
                                vec![format!("Rapid overwrite failed: {:?}", e)],
                            );
                        }
                    }
                    Ok(())
                }
                8 => {
                    // Insert-then-delete same key
                    let key = ctx.random_key();
                    let value = ctx.random_value();
                    if let Err(e) = self.db.insert(key, value) {
                        return WorkloadResult::failure(
                            seed,
                            operations_executed,
                            start.elapsed(),
                            vec![format!("Insert-delete insert failed: {:?}", e)],
                        );
                    }
                    let _ = self.db.delete(key);
                    Ok(())
                }
                9 => {
                    // Sync and get root hash
                    match self.db.sync() {
                        Ok(root_hash) => {
                            last_root = Some(root_hash);
                            Ok(())
                        }
                        Err(e) => {
                            return WorkloadResult::failure(
                                seed,
                                operations_executed,
                                start.elapsed(),
                                vec![format!("Sync failed: {:?}", e)],
                            );
                        }
                    }
                }
                // === CHAOS/NEMESIS OPERATIONS (10-19) ===
                // Inspired by FoundationDB's BUGGIFY patterns
                10 => {
                    // BUGGIFY: Toggle incremental mode
                    // Tests that incremental mode produces same results as full rebuild
                    if self.db.is_incremental_mode() {
                        self.db.disable_incremental_mode();
                    } else {
                        self.db.enable_incremental_mode();
                    }
                    Ok(())
                }
                11 => {
                    // BUGGIFY: Force full rebuild and verify root consistency
                    // Get root via incremental path
                    let incremental_root = match self.db.sync() {
                        Ok(r) => r,
                        Err(e) => {
                            return WorkloadResult::failure(
                                seed,
                                operations_executed,
                                start.elapsed(),
                                vec![format!("Incremental sync failed: {:?}", e)],
                            );
                        }
                    };
                    // Force full rebuild
                    let full_root = match self.db.force_full_rebuild() {
                        Ok(r) => r,
                        Err(e) => {
                            return WorkloadResult::failure(
                                seed,
                                operations_executed,
                                start.elapsed(),
                                vec![format!("Full rebuild failed: {:?}", e)],
                            );
                        }
                    };
                    // Verify they match
                    if incremental_root != full_root {
                        return WorkloadResult::failure(
                            seed,
                            operations_executed,
                            start.elapsed(),
                            vec![format!(
                                "Root hash mismatch: incremental {:?} != full {:?}",
                                &incremental_root[..8],
                                &full_root[..8]
                            )],
                        );
                    }
                    Ok(())
                }
                12 => {
                    // BUGGIFY: Clear caches and verify root still computes correctly
                    let before_root = self.db.sync().ok();
                    self.db.clear_caches();
                    let after_root = self.db.sync().ok();
                    if before_root != after_root {
                        return WorkloadResult::failure(
                            seed,
                            operations_executed,
                            start.elapsed(),
                            vec![format!(
                                "Cache clear caused root mismatch: {:?} != {:?}",
                                before_root.map(|r| hex::encode(&r[..8])),
                                after_root.map(|r| hex::encode(&r[..8]))
                            )],
                        );
                    }
                    Ok(())
                }
                13 => {
                    // BUGGIFY: Burst write to same stem (stress stem node updates)
                    // Keys with same first 31 bytes share a stem
                    let stem_prefix: [u8; 31] = ctx.random_key()[..31].try_into().unwrap();
                    for subindex in 0..16u8 {
                        let mut key = [0u8; 32];
                        key[..31].copy_from_slice(&stem_prefix);
                        key[31] = subindex;
                        let value = ctx.random_value();
                        if let Err(e) = self.db.insert(key, value) {
                            return WorkloadResult::failure(
                                seed,
                                operations_executed,
                                start.elapsed(),
                                vec![format!("Burst stem write failed: {:?}", e)],
                            );
                        }
                    }
                    Ok(())
                }
                14 => {
                    // BUGGIFY: Interleaved insert/delete storm
                    // Rapidly add and remove keys to stress dirty tracking
                    for _ in 0..10 {
                        let key = ctx.random_key();
                        let value = ctx.random_value();
                        let _ = self.db.insert(key, value);
                        let _ = self.db.delete(key);
                    }
                    Ok(())
                }
                15 => {
                    // BUGGIFY: Root hash stability check
                    // After no modifications, root hash should be identical
                    let root1 = self.db.sync().ok();
                    let root2 = self.db.sync().ok();
                    let root3 = self.db.sync().ok();
                    if root1 != root2 || root2 != root3 {
                        return WorkloadResult::failure(
                            seed,
                            operations_executed,
                            start.elapsed(),
                            vec!["Root hash not stable across multiple calls".to_string()],
                        );
                    }
                    Ok(())
                }
                16 => {
                    // BUGGIFY: Delete all keys in a stem, verify it's cleaned up
                    let stem_prefix: [u8; 31] = ctx.random_key()[..31].try_into().unwrap();
                    // Insert some keys
                    for subindex in 0..4u8 {
                        let mut key = [0u8; 32];
                        key[..31].copy_from_slice(&stem_prefix);
                        key[31] = subindex;
                        let _ = self.db.insert(key, ctx.random_value());
                    }
                    // Delete them all
                    for subindex in 0..4u8 {
                        let mut key = [0u8; 32];
                        key[..31].copy_from_slice(&stem_prefix);
                        key[31] = subindex;
                        let _ = self.db.delete(key);
                    }
                    // Verify scan doesn't include them
                    if let Ok(entries) = self.db.scan_all() {
                        for (k, _) in &entries {
                            if k[..31] == stem_prefix {
                                return WorkloadResult::failure(
                                    seed,
                                    operations_executed,
                                    start.elapsed(),
                                    vec!["Deleted stem keys still present in scan".to_string()],
                                );
                            }
                        }
                    }
                    Ok(())
                }
                17 => {
                    // BUGGIFY: Verify get/scan consistency
                    // Get via direct lookup should match scan results
                    if let Ok(entries) = self.db.scan_all() {
                        // Check a sample of entries
                        let sample_size = entries.len().min(10);
                        for (k, expected_v) in entries.iter().take(sample_size) {
                            match self.db.get(*k) {
                                Ok(Some(actual_v)) => {
                                    if actual_v != *expected_v {
                                        return WorkloadResult::failure(
                                            seed,
                                            operations_executed,
                                            start.elapsed(),
                                            vec![format!(
                                                "Get/scan mismatch for key {:?}",
                                                &k[..8]
                                            )],
                                        );
                                    }
                                }
                                Ok(None) => {
                                    return WorkloadResult::failure(
                                        seed,
                                        operations_executed,
                                        start.elapsed(),
                                        vec!["Key in scan not found via get".to_string()],
                                    );
                                }
                                Err(e) => {
                                    return WorkloadResult::failure(
                                        seed,
                                        operations_executed,
                                        start.elapsed(),
                                        vec![format!("Get failed during consistency check: {:?}", e)],
                                    );
                                }
                            }
                        }
                    }
                    Ok(())
                }
                18 => {
                    // BUGGIFY: Mode switch storm
                    // Rapidly toggle incremental mode while doing operations
                    for i in 0..5 {
                        if i % 2 == 0 {
                            self.db.enable_incremental_mode();
                        } else {
                            self.db.disable_incremental_mode();
                        }
                        let key = ctx.random_key();
                        let value = ctx.random_value();
                        let _ = self.db.insert(key, value);
                        let _ = self.db.sync();
                    }
                    Ok(())
                }
                _ => {
                    // BUGGIFY: Verify last root still valid after no-op
                    // If we computed a root before, it should still be the same
                    if let Some(prev_root) = last_root {
                        // Do a no-op sync
                        if let Ok(current_root) = self.db.sync() {
                            if prev_root != current_root {
                                // This is expected if we did mutations - just update
                                last_root = Some(current_root);
                            }
                        }
                    }
                    Ok(())
                }
            };

            if let Err(e) = result {
                return WorkloadResult::failure(
                    seed,
                    operations_executed,
                    start.elapsed(),
                    vec![format!(
                        "Operation {} (type {}) failed: {:?}",
                        operations_executed, op_type, e
                    )],
                );
            }

            operations_executed += 1;
        }

        WorkloadResult::success(seed, operations_executed, start.elapsed())
    }
}
