//! Simulation context providing deterministic randomness and timing.

use rand::{rngs::StdRng, Rng, SeedableRng};
use std::collections::BTreeMap;
use std::time::{Duration, Instant};

/// Context for a simulation worker providing deterministic primitives.
pub struct WorkloadContext {
    seed: u64,
    rng: StdRng,
    start_time: Instant,
    operation_count: u64,
    client_id: u32,
}

impl WorkloadContext {
    /// Create new context with given seed and client ID.
    pub fn new(seed: u64, client_id: u32) -> Self {
        Self {
            seed,
            rng: StdRng::seed_from_u64(seed),
            start_time: Instant::now(),
            operation_count: 0,
            client_id,
        }
    }

    /// Get the seed for reproducibility.
    pub fn seed(&self) -> u64 {
        self.seed
    }

    /// Get client ID for multi-client workloads.
    pub fn client_id(&self) -> u32 {
        self.client_id
    }

    /// Get mutable reference to seeded RNG - use this instead of rand::random().
    pub fn rng(&mut self) -> &mut StdRng {
        &mut self.rng
    }

    /// Get elapsed simulation time - use this instead of SystemTime::now().
    pub fn elapsed(&self) -> Duration {
        self.start_time.elapsed()
    }

    /// Generate next operation ID (monotonically increasing).
    pub fn next_op_id(&mut self) -> u64 {
        self.operation_count += 1;
        self.operation_count
    }

    /// Get total operations executed.
    pub fn total_ops(&self) -> u64 {
        self.operation_count
    }

    /// Generate a random 32-byte key (UBT uses fixed 32-byte keys).
    pub fn random_key(&mut self) -> [u8; 32] {
        let mut key = [0u8; 32];
        self.rng.fill(&mut key);
        key
    }

    /// Generate a random 32-byte value (UBT uses fixed 32-byte values).
    pub fn random_value(&mut self) -> [u8; 32] {
        let mut value = [0u8; 32];
        self.rng.fill(&mut value);
        value
    }

    /// Generate a deterministic key based on index (for predictable patterns).
    /// Pads the index to 32 bytes.
    pub fn indexed_key(&self, index: u64) -> [u8; 32] {
        let mut key = [0u8; 32];
        key[24..32].copy_from_slice(&index.to_be_bytes());
        key
    }

    /// Generate a deterministic value based on index.
    pub fn indexed_value(&self, index: u64) -> [u8; 32] {
        let mut value = [0u8; 32];
        value[0..8].copy_from_slice(&index.to_be_bytes());
        value[8..16].copy_from_slice(&self.seed.to_be_bytes());
        value
    }

    /// Choose random element from slice.
    pub fn choose<'a, T>(&mut self, items: &'a [T]) -> Option<&'a T> {
        if items.is_empty() {
            None
        } else {
            let idx = self.rng.gen_range(0..items.len());
            Some(&items[idx])
        }
    }

    /// Return true with given probability (0.0 to 1.0).
    pub fn chance(&mut self, probability: f64) -> bool {
        debug_assert!(
            (0.0..=1.0).contains(&probability),
            "probability must be between 0.0 and 1.0, got {}",
            probability
        );
        self.rng.gen::<f64>() < probability.clamp(0.0, 1.0)
    }
}

/// Deterministic map wrapper - always use BTreeMap for deterministic iteration.
pub type DeterministicMap<K, V> = BTreeMap<K, V>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_deterministic_rng() {
        let mut ctx1 = WorkloadContext::new(12345, 0);
        let mut ctx2 = WorkloadContext::new(12345, 0);

        let key1 = ctx1.random_key();
        let key2 = ctx2.random_key();
        assert_eq!(key1, key2, "Same seed should produce same keys");
    }

    #[test]
    fn test_different_seeds_differ() {
        let mut ctx1 = WorkloadContext::new(12345, 0);
        let mut ctx2 = WorkloadContext::new(54321, 0);

        let key1 = ctx1.random_key();
        let key2 = ctx2.random_key();
        assert_ne!(key1, key2, "Different seeds should produce different keys");
    }

    #[test]
    fn test_op_id_increments() {
        let mut ctx = WorkloadContext::new(1, 0);
        assert_eq!(ctx.next_op_id(), 1);
        assert_eq!(ctx.next_op_id(), 2);
        assert_eq!(ctx.next_op_id(), 3);
        assert_eq!(ctx.total_ops(), 3);
    }

    #[test]
    fn test_indexed_keys_deterministic() {
        let ctx = WorkloadContext::new(999, 0);
        let key0 = ctx.indexed_key(0);
        let key255 = ctx.indexed_key(255);

        assert_eq!(&key0[24..32], &[0, 0, 0, 0, 0, 0, 0, 0]);
        assert_eq!(&key255[24..32], &[0, 0, 0, 0, 0, 0, 0, 255]);
    }
}
