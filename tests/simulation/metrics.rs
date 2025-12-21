//! Prometheus metrics for simulation monitoring.

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::time::Instant;

/// Operation type counters for detailed observability.
#[derive(Debug)]
pub struct OpCounters {
    // Regular operations (0-9)
    pub insert: AtomicU64,
    pub get: AtomicU64,
    pub delete: AtomicU64,
    pub update_hot_key: AtomicU64,
    pub sequential_insert: AtomicU64,
    pub scan_all: AtomicU64,
    pub read_after_write: AtomicU64,
    pub rapid_overwrite: AtomicU64,
    pub insert_then_delete: AtomicU64,
    pub sync: AtomicU64,

    // Chaos operations (10-19) - BUGGIFY patterns
    pub chaos_toggle_incremental: AtomicU64,
    pub chaos_verify_incremental_vs_full: AtomicU64,
    pub chaos_clear_caches: AtomicU64,
    pub chaos_burst_stem_write: AtomicU64,
    pub chaos_insert_delete_storm: AtomicU64,
    pub chaos_root_stability: AtomicU64,
    pub chaos_delete_stem: AtomicU64,
    pub chaos_get_scan_consistency: AtomicU64,
    pub chaos_mode_switch_storm: AtomicU64,
    pub chaos_verify_last_root: AtomicU64,
}

impl Default for OpCounters {
    fn default() -> Self {
        Self::new()
    }
}

impl OpCounters {
    pub fn new() -> Self {
        Self {
            insert: AtomicU64::new(0),
            get: AtomicU64::new(0),
            delete: AtomicU64::new(0),
            update_hot_key: AtomicU64::new(0),
            sequential_insert: AtomicU64::new(0),
            scan_all: AtomicU64::new(0),
            read_after_write: AtomicU64::new(0),
            rapid_overwrite: AtomicU64::new(0),
            insert_then_delete: AtomicU64::new(0),
            sync: AtomicU64::new(0),
            chaos_toggle_incremental: AtomicU64::new(0),
            chaos_verify_incremental_vs_full: AtomicU64::new(0),
            chaos_clear_caches: AtomicU64::new(0),
            chaos_burst_stem_write: AtomicU64::new(0),
            chaos_insert_delete_storm: AtomicU64::new(0),
            chaos_root_stability: AtomicU64::new(0),
            chaos_delete_stem: AtomicU64::new(0),
            chaos_get_scan_consistency: AtomicU64::new(0),
            chaos_mode_switch_storm: AtomicU64::new(0),
            chaos_verify_last_root: AtomicU64::new(0),
        }
    }

    pub fn inc_op(&self, op_type: u32) {
        match op_type {
            0 => self.insert.fetch_add(1, Ordering::Relaxed),
            1 => self.get.fetch_add(1, Ordering::Relaxed),
            2 => self.delete.fetch_add(1, Ordering::Relaxed),
            3 => self.update_hot_key.fetch_add(1, Ordering::Relaxed),
            4 => self.sequential_insert.fetch_add(1, Ordering::Relaxed),
            5 => self.scan_all.fetch_add(1, Ordering::Relaxed),
            6 => self.read_after_write.fetch_add(1, Ordering::Relaxed),
            7 => self.rapid_overwrite.fetch_add(1, Ordering::Relaxed),
            8 => self.insert_then_delete.fetch_add(1, Ordering::Relaxed),
            9 => self.sync.fetch_add(1, Ordering::Relaxed),
            10 => self.chaos_toggle_incremental.fetch_add(1, Ordering::Relaxed),
            11 => self.chaos_verify_incremental_vs_full.fetch_add(1, Ordering::Relaxed),
            12 => self.chaos_clear_caches.fetch_add(1, Ordering::Relaxed),
            13 => self.chaos_burst_stem_write.fetch_add(1, Ordering::Relaxed),
            14 => self.chaos_insert_delete_storm.fetch_add(1, Ordering::Relaxed),
            15 => self.chaos_root_stability.fetch_add(1, Ordering::Relaxed),
            16 => self.chaos_delete_stem.fetch_add(1, Ordering::Relaxed),
            17 => self.chaos_get_scan_consistency.fetch_add(1, Ordering::Relaxed),
            18 => self.chaos_mode_switch_storm.fetch_add(1, Ordering::Relaxed),
            _ => self.chaos_verify_last_root.fetch_add(1, Ordering::Relaxed),
        };
    }

    pub fn to_prometheus(&self) -> String {
        format!(
            r#"# HELP ubt_sim_op_insert_total Insert operations
# TYPE ubt_sim_op_insert_total counter
ubt_sim_op_insert_total {}

# HELP ubt_sim_op_get_total Get operations
# TYPE ubt_sim_op_get_total counter
ubt_sim_op_get_total {}

# HELP ubt_sim_op_delete_total Delete operations
# TYPE ubt_sim_op_delete_total counter
ubt_sim_op_delete_total {}

# HELP ubt_sim_op_update_hot_key_total Update hot key operations
# TYPE ubt_sim_op_update_hot_key_total counter
ubt_sim_op_update_hot_key_total {}

# HELP ubt_sim_op_sequential_insert_total Sequential insert operations
# TYPE ubt_sim_op_sequential_insert_total counter
ubt_sim_op_sequential_insert_total {}

# HELP ubt_sim_op_scan_all_total Scan all operations
# TYPE ubt_sim_op_scan_all_total counter
ubt_sim_op_scan_all_total {}

# HELP ubt_sim_op_read_after_write_total Read-after-write operations
# TYPE ubt_sim_op_read_after_write_total counter
ubt_sim_op_read_after_write_total {}

# HELP ubt_sim_op_rapid_overwrite_total Rapid overwrite operations
# TYPE ubt_sim_op_rapid_overwrite_total counter
ubt_sim_op_rapid_overwrite_total {}

# HELP ubt_sim_op_insert_then_delete_total Insert-then-delete operations
# TYPE ubt_sim_op_insert_then_delete_total counter
ubt_sim_op_insert_then_delete_total {}

# HELP ubt_sim_op_sync_total Sync operations
# TYPE ubt_sim_op_sync_total counter
ubt_sim_op_sync_total {}

# HELP ubt_sim_chaos_toggle_incremental_total Toggle incremental mode
# TYPE ubt_sim_chaos_toggle_incremental_total counter
ubt_sim_chaos_toggle_incremental_total {}

# HELP ubt_sim_chaos_verify_incremental_vs_full_total Verify incremental vs full rebuild
# TYPE ubt_sim_chaos_verify_incremental_vs_full_total counter
ubt_sim_chaos_verify_incremental_vs_full_total {}

# HELP ubt_sim_chaos_clear_caches_total Clear caches and verify
# TYPE ubt_sim_chaos_clear_caches_total counter
ubt_sim_chaos_clear_caches_total {}

# HELP ubt_sim_chaos_burst_stem_write_total Burst write to same stem
# TYPE ubt_sim_chaos_burst_stem_write_total counter
ubt_sim_chaos_burst_stem_write_total {}

# HELP ubt_sim_chaos_insert_delete_storm_total Insert/delete storm
# TYPE ubt_sim_chaos_insert_delete_storm_total counter
ubt_sim_chaos_insert_delete_storm_total {}

# HELP ubt_sim_chaos_root_stability_total Root hash stability check
# TYPE ubt_sim_chaos_root_stability_total counter
ubt_sim_chaos_root_stability_total {}

# HELP ubt_sim_chaos_delete_stem_total Delete entire stem
# TYPE ubt_sim_chaos_delete_stem_total counter
ubt_sim_chaos_delete_stem_total {}

# HELP ubt_sim_chaos_get_scan_consistency_total Get/scan consistency check
# TYPE ubt_sim_chaos_get_scan_consistency_total counter
ubt_sim_chaos_get_scan_consistency_total {}

# HELP ubt_sim_chaos_mode_switch_storm_total Mode switch storm
# TYPE ubt_sim_chaos_mode_switch_storm_total counter
ubt_sim_chaos_mode_switch_storm_total {}

# HELP ubt_sim_chaos_verify_last_root_total Verify last root
# TYPE ubt_sim_chaos_verify_last_root_total counter
ubt_sim_chaos_verify_last_root_total {}
"#,
            self.insert.load(Ordering::Relaxed),
            self.get.load(Ordering::Relaxed),
            self.delete.load(Ordering::Relaxed),
            self.update_hot_key.load(Ordering::Relaxed),
            self.sequential_insert.load(Ordering::Relaxed),
            self.scan_all.load(Ordering::Relaxed),
            self.read_after_write.load(Ordering::Relaxed),
            self.rapid_overwrite.load(Ordering::Relaxed),
            self.insert_then_delete.load(Ordering::Relaxed),
            self.sync.load(Ordering::Relaxed),
            self.chaos_toggle_incremental.load(Ordering::Relaxed),
            self.chaos_verify_incremental_vs_full.load(Ordering::Relaxed),
            self.chaos_clear_caches.load(Ordering::Relaxed),
            self.chaos_burst_stem_write.load(Ordering::Relaxed),
            self.chaos_insert_delete_storm.load(Ordering::Relaxed),
            self.chaos_root_stability.load(Ordering::Relaxed),
            self.chaos_delete_stem.load(Ordering::Relaxed),
            self.chaos_get_scan_consistency.load(Ordering::Relaxed),
            self.chaos_mode_switch_storm.load(Ordering::Relaxed),
            self.chaos_verify_last_root.load(Ordering::Relaxed),
        )
    }

    pub fn total_chaos_ops(&self) -> u64 {
        self.chaos_toggle_incremental.load(Ordering::Relaxed)
            + self.chaos_verify_incremental_vs_full.load(Ordering::Relaxed)
            + self.chaos_clear_caches.load(Ordering::Relaxed)
            + self.chaos_burst_stem_write.load(Ordering::Relaxed)
            + self.chaos_insert_delete_storm.load(Ordering::Relaxed)
            + self.chaos_root_stability.load(Ordering::Relaxed)
            + self.chaos_delete_stem.load(Ordering::Relaxed)
            + self.chaos_get_scan_consistency.load(Ordering::Relaxed)
            + self.chaos_mode_switch_storm.load(Ordering::Relaxed)
            + self.chaos_verify_last_root.load(Ordering::Relaxed)
    }
}

/// Metrics collector for simulation runs.
///
/// These metrics can be exposed via a Prometheus endpoint for Grafana dashboards.
#[derive(Debug)]
pub struct Metrics {
    start_time: Instant,

    // Counters
    operations_total: AtomicU64,
    seeds_completed: AtomicU64,
    seeds_failed: AtomicU64,
    invariant_violations: AtomicU64,

    // Gauges
    active_workers: AtomicU64,
    seeds_remaining: AtomicU64,
    seeds_total: AtomicU64,

    // Per-operation counters
    pub op_counters: OpCounters,
}

impl Default for Metrics {
    fn default() -> Self {
        Self::new()
    }
}

impl Metrics {
    pub fn new() -> Self {
        Self {
            start_time: Instant::now(),
            operations_total: AtomicU64::new(0),
            seeds_completed: AtomicU64::new(0),
            seeds_failed: AtomicU64::new(0),
            invariant_violations: AtomicU64::new(0),
            active_workers: AtomicU64::new(0),
            seeds_remaining: AtomicU64::new(0),
            seeds_total: AtomicU64::new(0),
            op_counters: OpCounters::new(),
        }
    }

    pub fn inc_operations(&self, count: u64) {
        self.operations_total.fetch_add(count, Ordering::Relaxed);
    }

    pub fn inc_op(&self, op_type: u32) {
        self.op_counters.inc_op(op_type);
    }

    pub fn inc_seeds_completed(&self) {
        self.seeds_completed.fetch_add(1, Ordering::Relaxed);
    }

    pub fn inc_seeds_failed(&self) {
        self.seeds_failed.fetch_add(1, Ordering::Relaxed);
    }

    pub fn inc_invariant_violations(&self, count: u64) {
        self.invariant_violations
            .fetch_add(count, Ordering::Relaxed);
    }

    pub fn set_active_workers(&self, count: u64) {
        self.active_workers.store(count, Ordering::Relaxed);
    }

    pub fn set_seeds_remaining(&self, count: u64) {
        self.seeds_remaining.store(count, Ordering::Relaxed);
    }

    pub fn set_seeds_total(&self, count: u64) {
        self.seeds_total.store(count, Ordering::Relaxed);
    }

    pub fn dec_seeds_remaining(&self) {
        self.seeds_remaining.fetch_sub(1, Ordering::Relaxed);
    }

    pub fn worker_started(&self) {
        self.active_workers.fetch_add(1, Ordering::Relaxed);
    }

    pub fn worker_finished(&self) {
        let prev = self.active_workers.load(Ordering::Relaxed);
        if prev > 0 {
            self.active_workers.fetch_sub(1, Ordering::Relaxed);
        }
    }

    /// Get metrics in Prometheus text format.
    pub fn to_prometheus(&self) -> String {
        let uptime = self.start_time.elapsed().as_secs_f64();
        let ops = self.operations_total.load(Ordering::Relaxed);
        let completed = self.seeds_completed.load(Ordering::Relaxed);
        let failed = self.seeds_failed.load(Ordering::Relaxed);
        let violations = self.invariant_violations.load(Ordering::Relaxed);
        let workers = self.active_workers.load(Ordering::Relaxed);
        let remaining = self.seeds_remaining.load(Ordering::Relaxed);
        let total = self.seeds_total.load(Ordering::Relaxed);
        let chaos_total = self.op_counters.total_chaos_ops();

        let ops_per_sec = if uptime > 0.0 {
            ops as f64 / uptime
        } else {
            0.0
        };

        let progress_pct = if total > 0 {
            (completed as f64 / total as f64) * 100.0
        } else {
            0.0
        };

        let base_metrics = format!(
            r#"# HELP ubt_sim_operations_total Total operations executed
# TYPE ubt_sim_operations_total counter
ubt_sim_operations_total {}

# HELP ubt_sim_operations_per_second Current operations per second
# TYPE ubt_sim_operations_per_second gauge
ubt_sim_operations_per_second {:.2}

# HELP ubt_sim_seeds_completed Total seeds completed
# TYPE ubt_sim_seeds_completed counter
ubt_sim_seeds_completed {}

# HELP ubt_sim_seeds_failed Total seeds that found failures
# TYPE ubt_sim_seeds_failed counter
ubt_sim_seeds_failed {}

# HELP ubt_sim_seeds_total Total seeds to process
# TYPE ubt_sim_seeds_total gauge
ubt_sim_seeds_total {}

# HELP ubt_sim_progress_percent Simulation progress percentage
# TYPE ubt_sim_progress_percent gauge
ubt_sim_progress_percent {:.2}

# HELP ubt_sim_invariant_violations Total invariant violations found
# TYPE ubt_sim_invariant_violations counter
ubt_sim_invariant_violations {}

# HELP ubt_sim_active_workers Number of active worker threads
# TYPE ubt_sim_active_workers gauge
ubt_sim_active_workers {}

# HELP ubt_sim_seeds_remaining Seeds remaining to process
# TYPE ubt_sim_seeds_remaining gauge
ubt_sim_seeds_remaining {}

# HELP ubt_sim_uptime_seconds Simulation uptime in seconds
# TYPE ubt_sim_uptime_seconds gauge
ubt_sim_uptime_seconds {:.2}

# HELP ubt_sim_chaos_ops_total Total chaos/BUGGIFY operations executed
# TYPE ubt_sim_chaos_ops_total counter
ubt_sim_chaos_ops_total {}

"#,
            ops, ops_per_sec, completed, failed, total, progress_pct, violations, workers, remaining, uptime, chaos_total
        );

        format!("{}{}", base_metrics, self.op_counters.to_prometheus())
    }

    /// Get a snapshot of current metrics.
    pub fn snapshot(&self) -> MetricsSnapshot {
        MetricsSnapshot {
            operations_total: self.operations_total.load(Ordering::Relaxed),
            seeds_completed: self.seeds_completed.load(Ordering::Relaxed),
            seeds_failed: self.seeds_failed.load(Ordering::Relaxed),
            invariant_violations: self.invariant_violations.load(Ordering::Relaxed),
            active_workers: self.active_workers.load(Ordering::Relaxed),
            seeds_remaining: self.seeds_remaining.load(Ordering::Relaxed),
            seeds_total: self.seeds_total.load(Ordering::Relaxed),
            uptime_secs: self.start_time.elapsed().as_secs_f64(),
            chaos_ops_total: self.op_counters.total_chaos_ops(),
        }
    }
}

/// Point-in-time metrics snapshot.
#[derive(Debug, Clone)]
pub struct MetricsSnapshot {
    pub operations_total: u64,
    pub seeds_completed: u64,
    pub seeds_failed: u64,
    pub invariant_violations: u64,
    pub active_workers: u64,
    pub seeds_remaining: u64,
    pub seeds_total: u64,
    pub uptime_secs: f64,
    pub chaos_ops_total: u64,
}

impl MetricsSnapshot {
    pub fn operations_per_second(&self) -> f64 {
        if self.uptime_secs > 0.0 {
            self.operations_total as f64 / self.uptime_secs
        } else {
            0.0
        }
    }

    pub fn failure_rate(&self) -> f64 {
        if self.seeds_completed > 0 {
            self.seeds_failed as f64 / self.seeds_completed as f64
        } else {
            0.0
        }
    }

    pub fn progress_percent(&self) -> f64 {
        if self.seeds_total > 0 {
            (self.seeds_completed as f64 / self.seeds_total as f64) * 100.0
        } else {
            0.0
        }
    }
}

/// Shared metrics handle for multi-threaded access.
pub type SharedMetrics = Arc<Metrics>;

/// Create a new shared metrics instance.
pub fn create_shared_metrics() -> SharedMetrics {
    Arc::new(Metrics::new())
}

/// HTTP metrics server for Prometheus scraping.
pub mod server {
    use super::SharedMetrics;
    use std::io::{Read, Write};
    use std::net::TcpListener;
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::Arc;
    use std::thread;
    use std::time::Duration;

    pub struct MetricsServer {
        metrics: SharedMetrics,
        shutdown: Arc<AtomicBool>,
        handle: Option<thread::JoinHandle<()>>,
    }

    impl MetricsServer {
        pub fn start(port: u16, metrics: SharedMetrics) -> std::io::Result<Self> {
            let shutdown = Arc::new(AtomicBool::new(false));
            let shutdown_clone = Arc::clone(&shutdown);
            let metrics_clone = Arc::clone(&metrics);

            let listener = TcpListener::bind(format!("0.0.0.0:{}", port))?;
            listener.set_nonblocking(true)?;

            eprintln!("[METRICS] Prometheus endpoint listening on http://0.0.0.0:{}/metrics", port);

            let handle = thread::spawn(move || {
                Self::run_server(listener, metrics_clone, shutdown_clone);
            });

            Ok(Self {
                metrics,
                shutdown,
                handle: Some(handle),
            })
        }

        fn run_server(listener: TcpListener, metrics: SharedMetrics, shutdown: Arc<AtomicBool>) {
            while !shutdown.load(Ordering::Relaxed) {
                match listener.accept() {
                    Ok((mut stream, _addr)) => {
                        let mut buffer = [0u8; 1024];
                        if stream.read(&mut buffer).is_ok() {
                            let request = String::from_utf8_lossy(&buffer);
                            if request.contains("GET /metrics") || request.contains("GET / ") {
                                let body = metrics.to_prometheus();
                                let response = format!(
                                    "HTTP/1.1 200 OK\r\nContent-Type: text/plain; version=0.0.4\r\nContent-Length: {}\r\n\r\n{}",
                                    body.len(),
                                    body
                                );
                                let _ = stream.write_all(response.as_bytes());
                            } else {
                                let response = "HTTP/1.1 404 Not Found\r\nContent-Length: 0\r\n\r\n";
                                let _ = stream.write_all(response.as_bytes());
                            }
                        }
                    }
                    Err(ref e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                        thread::sleep(Duration::from_millis(100));
                    }
                    Err(e) => {
                        eprintln!("[METRICS] Connection error: {}", e);
                        thread::sleep(Duration::from_millis(100));
                    }
                }
            }
        }

        pub fn shutdown(&mut self) {
            self.shutdown.store(true, Ordering::Relaxed);
            if let Some(handle) = self.handle.take() {
                let _ = handle.join();
            }
        }

        pub fn metrics(&self) -> &SharedMetrics {
            &self.metrics
        }
    }

    impl Drop for MetricsServer {
        fn drop(&mut self) {
            self.shutdown();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_metrics_increment() {
        let metrics = Metrics::new();

        metrics.inc_operations(100);
        metrics.inc_operations(50);
        metrics.inc_seeds_completed();
        metrics.inc_seeds_completed();
        metrics.inc_seeds_failed();

        let snap = metrics.snapshot();
        assert_eq!(snap.operations_total, 150);
        assert_eq!(snap.seeds_completed, 2);
        assert_eq!(snap.seeds_failed, 1);
    }

    #[test]
    fn test_prometheus_format() {
        let metrics = Metrics::new();
        metrics.inc_operations(1000);
        metrics.inc_seeds_completed();
        metrics.set_seeds_total(100);

        let output = metrics.to_prometheus();
        assert!(output.contains("ubt_sim_operations_total 1000"));
        assert!(output.contains("ubt_sim_seeds_completed 1"));
        assert!(output.contains("ubt_sim_seeds_total 100"));
    }

    #[test]
    fn test_worker_tracking() {
        let metrics = Metrics::new();

        metrics.worker_started();
        metrics.worker_started();
        assert_eq!(metrics.snapshot().active_workers, 2);

        metrics.worker_finished();
        assert_eq!(metrics.snapshot().active_workers, 1);
    }

    #[test]
    fn test_op_counters() {
        let metrics = Metrics::new();

        metrics.inc_op(0);
        metrics.inc_op(0);
        metrics.inc_op(1);
        metrics.inc_op(10);
        metrics.inc_op(11);

        assert_eq!(metrics.op_counters.insert.load(Ordering::Relaxed), 2);
        assert_eq!(metrics.op_counters.get.load(Ordering::Relaxed), 1);
        assert_eq!(metrics.op_counters.chaos_toggle_incremental.load(Ordering::Relaxed), 1);
        assert_eq!(metrics.op_counters.chaos_verify_incremental_vs_full.load(Ordering::Relaxed), 1);
        assert_eq!(metrics.op_counters.total_chaos_ops(), 2);
    }

    #[test]
    fn test_chaos_ops_in_prometheus() {
        let metrics = Metrics::new();
        metrics.inc_op(10);
        metrics.inc_op(13);

        let output = metrics.to_prometheus();
        assert!(output.contains("ubt_sim_chaos_toggle_incremental_total 1"));
        assert!(output.contains("ubt_sim_chaos_burst_stem_write_total 1"));
        assert!(output.contains("ubt_sim_chaos_ops_total 2"));
    }
}
