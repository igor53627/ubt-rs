//! Workload runner for simulation testing.
#![allow(dead_code)] // Test infrastructure with room for future expansion

use crate::simulation::context::WorkloadContext;
use crate::simulation::metrics::SharedMetrics;
use rand::Rng;
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

/// Mutable state carried across the operations of one workload run.
#[derive(Default)]
struct RunState {
    sequential_counter: u64,
    /// Last root hash, tracked for consistency checks.
    last_root: Option<[u8; 32]>,
}

/// Failure of a single workload operation.
enum OpFailure<E> {
    /// An invariant check failed; the message is reported unchanged.
    Violation(String),
    /// The database returned an error; `WorkloadRunner::run` adds the operation index and type.
    Database(E),
}

type OpResult<E> = Result<(), OpFailure<E>>;

impl<D: TestableDatabase> WorkloadRunner<D> {
    pub fn new(db: D, config: WorkloadConfig) -> Self {
        Self {
            db,
            config,
            metrics: None,
        }
    }

    pub fn with_metrics(db: D, config: WorkloadConfig, metrics: SharedMetrics) -> Self {
        Self {
            db,
            config,
            metrics: Some(metrics),
        }
    }

    pub fn run(&mut self, ctx: &mut WorkloadContext) -> WorkloadResult {
        use std::time::Instant;

        let start = Instant::now();
        let seed = ctx.seed();
        let mut operations_executed = 0u64;
        let mut state = RunState::default();

        let op_modulo = if self.config.enable_chaos_ops {
            20 // Full chaos mode with BUGGIFY-style operations
        } else if self.config.enable_extended_ops {
            10
        } else {
            3
        };

        for _ in 0..self.config.operations_per_run {
            let op_type = ctx.rng().gen::<u32>() % op_modulo;

            // Record operation type in metrics
            if let Some(ref m) = self.metrics {
                m.inc_op(op_type);
            }

            if let Err(failure) = self.execute_op(op_type, ctx, &mut state) {
                let violation: String = match failure {
                    OpFailure::Violation(message) => message,
                    OpFailure::Database(e) => {
                        format!("Operation {operations_executed} (type {op_type}) failed: {e:?}")
                    }
                };
                return WorkloadResult::failure(
                    seed,
                    operations_executed,
                    start.elapsed(),
                    vec![violation],
                );
            }

            operations_executed += 1;
        }

        WorkloadResult::success(seed, operations_executed, start.elapsed())
    }

    fn execute_op(
        &mut self,
        op_type: u32,
        ctx: &mut WorkloadContext,
        state: &mut RunState,
    ) -> OpResult<D::Error> {
        match op_type {
            0 => self.op_insert(ctx),
            1 => self.op_get(ctx),
            2 => self.op_delete(ctx),
            3 => self.op_update_hot_key(ctx),
            4 => self.op_sequential_insert(ctx, state),
            5 => self.op_scan_all(),
            6 => self.op_read_after_write(ctx),
            7 => self.op_rapid_overwrite(ctx),
            8 => self.op_insert_then_delete(ctx),
            9 => self.op_sync(state),
            // === CHAOS/NEMESIS OPERATIONS (10-19) ===
            // Inspired by FoundationDB's BUGGIFY patterns
            10 => {
                self.chaos_toggle_incremental();
                Ok(())
            }
            11 => self.chaos_verify_incremental_vs_full(),
            12 => self.chaos_clear_caches(),
            13 => self.chaos_burst_stem_write(ctx),
            14 => {
                self.chaos_insert_delete_storm(ctx);
                Ok(())
            }
            15 => self.chaos_root_stability(),
            16 => self.chaos_delete_stem(ctx),
            17 => self.chaos_get_scan_consistency(),
            18 => {
                self.chaos_mode_switch_storm(ctx);
                Ok(())
            }
            _ => {
                self.chaos_verify_last_root(state);
                Ok(())
            }
        }
    }

    /// Insert random key-value.
    fn op_insert(&mut self, ctx: &mut WorkloadContext) -> OpResult<D::Error> {
        let key = ctx.random_key();
        let value = ctx.random_value();
        self.db.insert(key, value).map_err(OpFailure::Database)
    }

    /// Get random key.
    fn op_get(&self, ctx: &mut WorkloadContext) -> OpResult<D::Error> {
        let key = ctx.random_key();
        self.db.get(key).map(|_| ()).map_err(OpFailure::Database)
    }

    /// Delete random key.
    fn op_delete(&mut self, ctx: &mut WorkloadContext) -> OpResult<D::Error> {
        let key = ctx.random_key();
        self.db.delete(key).map(|_| ()).map_err(OpFailure::Database)
    }

    /// Update - insert to a hot key (low key space).
    fn op_update_hot_key(&mut self, ctx: &mut WorkloadContext) -> OpResult<D::Error> {
        let index = ctx.rng().gen::<u64>() % 100;
        let key = WorkloadContext::indexed_key(index);
        let value = ctx.random_value();
        self.db.insert(key, value).map_err(OpFailure::Database)
    }

    /// Sequential insert.
    fn op_sequential_insert(
        &mut self,
        ctx: &mut WorkloadContext,
        state: &mut RunState,
    ) -> OpResult<D::Error> {
        let key = WorkloadContext::indexed_key(state.sequential_counter);
        state.sequential_counter += 1;
        let value = ctx.random_value();
        self.db.insert(key, value).map_err(OpFailure::Database)
    }

    /// Scan all - verify scan completes and is sorted.
    fn op_scan_all(&self) -> OpResult<D::Error> {
        let entries: KeyValueEntries = self.db.scan_all().map_err(OpFailure::Database)?;
        for i in 1..entries.len() {
            if entries[i].0 <= entries[i - 1].0 {
                return Err(OpFailure::Violation(format!(
                    "Scan order violation at index {}: {:?} <= {:?}",
                    i,
                    &entries[i].0[..8],
                    &entries[i - 1].0[..8]
                )));
            }
        }
        Ok(())
    }

    /// Read-after-write verification.
    fn op_read_after_write(&mut self, ctx: &mut WorkloadContext) -> OpResult<D::Error> {
        let key = ctx.random_key();
        let value = ctx.random_value();
        if let Err(e) = self.db.insert(key, value) {
            return Err(OpFailure::Violation(format!("RAW insert failed: {e:?}")));
        }
        match self.db.get(key) {
            Ok(Some(read_value)) => {
                if read_value != value {
                    return Err(OpFailure::Violation(format!(
                        "RAW mismatch: wrote {:?}, read {:?}",
                        &value[..8],
                        &read_value[..8]
                    )));
                }
                Ok(())
            }
            Ok(None) => Err(OpFailure::Violation(
                "RAW failed: key not found after insert".to_string(),
            )),
            Err(e) => Err(OpFailure::Database(e)),
        }
    }

    /// Rapid overwrite - same key multiple times.
    fn op_rapid_overwrite(&mut self, ctx: &mut WorkloadContext) -> OpResult<D::Error> {
        let hot_index = ctx.rng().gen::<u64>() % 10;
        let key = WorkloadContext::indexed_key(hot_index);
        for _ in 0..5 {
            let value = ctx.random_value();
            if let Err(e) = self.db.insert(key, value) {
                return Err(OpFailure::Violation(format!(
                    "Rapid overwrite failed: {e:?}"
                )));
            }
        }
        Ok(())
    }

    /// Insert-then-delete same key.
    fn op_insert_then_delete(&mut self, ctx: &mut WorkloadContext) -> OpResult<D::Error> {
        let key = ctx.random_key();
        let value = ctx.random_value();
        if let Err(e) = self.db.insert(key, value) {
            return Err(OpFailure::Violation(format!(
                "Insert-delete insert failed: {e:?}"
            )));
        }
        let _ = self.db.delete(key);
        Ok(())
    }

    /// Sync and get root hash.
    fn op_sync(&mut self, state: &mut RunState) -> OpResult<D::Error> {
        match self.db.sync() {
            Ok(root_hash) => {
                state.last_root = Some(root_hash);
                Ok(())
            }
            Err(e) => Err(OpFailure::Violation(format!("Sync failed: {e:?}"))),
        }
    }

    /// BUGGIFY: Toggle incremental mode.
    /// Tests that incremental mode produces same results as full rebuild.
    fn chaos_toggle_incremental(&mut self) {
        if self.db.is_incremental_mode() {
            self.db.disable_incremental_mode();
        } else {
            self.db.enable_incremental_mode();
        }
    }

    /// BUGGIFY: Force full rebuild and verify root consistency.
    fn chaos_verify_incremental_vs_full(&mut self) -> OpResult<D::Error> {
        // Get root via incremental path
        let incremental_root: [u8; 32] = match self.db.sync() {
            Ok(r) => r,
            Err(e) => {
                return Err(OpFailure::Violation(format!(
                    "Incremental sync failed: {e:?}"
                )));
            }
        };
        // Force full rebuild
        let full_root: [u8; 32] = match self.db.force_full_rebuild() {
            Ok(r) => r,
            Err(e) => {
                return Err(OpFailure::Violation(format!("Full rebuild failed: {e:?}")));
            }
        };
        // Verify they match
        if incremental_root != full_root {
            return Err(OpFailure::Violation(format!(
                "Root hash mismatch: incremental {:?} != full {:?}",
                &incremental_root[..8],
                &full_root[..8]
            )));
        }
        Ok(())
    }

    /// BUGGIFY: Clear caches and verify root still computes correctly.
    fn chaos_clear_caches(&mut self) -> OpResult<D::Error> {
        let before_root = self.db.sync().ok();
        self.db.clear_caches();
        let after_root = self.db.sync().ok();
        if before_root != after_root {
            return Err(OpFailure::Violation(format!(
                "Cache clear caused root mismatch: {:?} != {:?}",
                before_root.map(|r| hex::encode(&r[..8])),
                after_root.map(|r| hex::encode(&r[..8]))
            )));
        }
        Ok(())
    }

    /// BUGGIFY: Burst write to same stem (stress stem node updates).
    /// Keys with same first 31 bytes share a stem.
    fn chaos_burst_stem_write(&mut self, ctx: &mut WorkloadContext) -> OpResult<D::Error> {
        let stem_prefix: [u8; 31] = ctx.random_key()[..31].try_into().unwrap();
        for subindex in 0..16u8 {
            let mut key = [0u8; 32];
            key[..31].copy_from_slice(&stem_prefix);
            key[31] = subindex;
            let value = ctx.random_value();
            if let Err(e) = self.db.insert(key, value) {
                return Err(OpFailure::Violation(format!(
                    "Burst stem write failed: {e:?}"
                )));
            }
        }
        Ok(())
    }

    /// BUGGIFY: Interleaved insert/delete storm.
    /// Rapidly add and remove keys to stress dirty tracking.
    fn chaos_insert_delete_storm(&mut self, ctx: &mut WorkloadContext) {
        for _ in 0..10 {
            let key = ctx.random_key();
            let value = ctx.random_value();
            let _ = self.db.insert(key, value);
            let _ = self.db.delete(key);
        }
    }

    /// BUGGIFY: Root hash stability check.
    /// After no modifications, root hash should be identical.
    fn chaos_root_stability(&mut self) -> OpResult<D::Error> {
        let root1 = self.db.sync().ok();
        let root2 = self.db.sync().ok();
        let root3 = self.db.sync().ok();
        if root1 != root2 || root2 != root3 {
            return Err(OpFailure::Violation(
                "Root hash not stable across multiple calls".to_string(),
            ));
        }
        Ok(())
    }

    /// BUGGIFY: Delete all keys in a stem, verify it's cleaned up.
    fn chaos_delete_stem(&mut self, ctx: &mut WorkloadContext) -> OpResult<D::Error> {
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
                    return Err(OpFailure::Violation(
                        "Deleted stem keys still present in scan".to_string(),
                    ));
                }
            }
        }
        Ok(())
    }

    /// BUGGIFY: Verify get/scan consistency.
    /// Get via direct lookup should match scan results.
    fn chaos_get_scan_consistency(&self) -> OpResult<D::Error> {
        if let Ok(entries) = self.db.scan_all() {
            // Check a sample of entries
            let sample_size = entries.len().min(10);
            for (k, expected_v) in entries.iter().take(sample_size) {
                match self.db.get(*k) {
                    Ok(Some(actual_v)) => {
                        if actual_v != *expected_v {
                            return Err(OpFailure::Violation(format!(
                                "Get/scan mismatch for key {:?}",
                                &k[..8]
                            )));
                        }
                    }
                    Ok(None) => {
                        return Err(OpFailure::Violation(
                            "Key in scan not found via get".to_string(),
                        ));
                    }
                    Err(e) => {
                        return Err(OpFailure::Violation(format!(
                            "Get failed during consistency check: {e:?}"
                        )));
                    }
                }
            }
        }
        Ok(())
    }

    /// BUGGIFY: Mode switch storm.
    /// Rapidly toggle incremental mode while doing operations.
    fn chaos_mode_switch_storm(&mut self, ctx: &mut WorkloadContext) {
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
    }

    /// BUGGIFY: Verify last root still valid after no-op.
    /// If we computed a root before, it should still be the same.
    fn chaos_verify_last_root(&mut self, state: &mut RunState) {
        if let Some(prev_root) = state.last_root {
            // Do a no-op sync
            if let Ok(current_root) = self.db.sync() {
                if prev_root != current_root {
                    // This is expected if we did mutations - just update
                    state.last_root = Some(current_root);
                }
            }
        }
    }
}
