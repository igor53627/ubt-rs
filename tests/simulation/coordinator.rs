//! Multi-threaded simulation coordinator.

use crate::simulation::context::WorkloadContext;
use crate::simulation::metrics::SharedMetrics;
use crate::simulation::workload::{WorkloadConfig, WorkloadResult};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Arc;
use std::thread;
use std::time::{Duration, Instant};

/// Statistics collected during simulation.
#[derive(Debug, Default)]
pub struct SimulationStats {
    pub seeds_completed: AtomicU64,
    pub seeds_failed: AtomicU64,
    pub total_operations: AtomicU64,
    pub violations_found: AtomicU64,
}

impl SimulationStats {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn record_result(&self, result: &WorkloadResult) {
        self.seeds_completed.fetch_add(1, Ordering::Relaxed);
        self.total_operations
            .fetch_add(result.operations_executed, Ordering::Relaxed);

        if !result.success {
            self.seeds_failed.fetch_add(1, Ordering::Relaxed);
            self.violations_found
                .fetch_add(result.violations.len() as u64, Ordering::Relaxed);
        }
    }

    pub fn snapshot(&self) -> StatsSnapshot {
        StatsSnapshot {
            seeds_completed: self.seeds_completed.load(Ordering::Relaxed),
            seeds_failed: self.seeds_failed.load(Ordering::Relaxed),
            total_operations: self.total_operations.load(Ordering::Relaxed),
            violations_found: self.violations_found.load(Ordering::Relaxed),
        }
    }
}

/// Point-in-time snapshot of stats.
#[derive(Debug, Clone)]
pub struct StatsSnapshot {
    pub seeds_completed: u64,
    pub seeds_failed: u64,
    pub total_operations: u64,
    pub violations_found: u64,
}

/// Configuration for the simulation coordinator.
#[derive(Clone, Debug)]
pub struct CoordinatorConfig {
    pub num_workers: usize,
    pub seed_start: u64,
    pub seed_end: u64,
    pub workload: WorkloadConfig,
    pub progress_interval: Duration,
    pub metrics_port: Option<u16>,
}

impl Default for CoordinatorConfig {
    fn default() -> Self {
        Self {
            num_workers: num_cpus::get(),
            seed_start: 0,
            seed_end: 10_000,
            workload: WorkloadConfig::default(),
            progress_interval: Duration::from_secs(10),
            metrics_port: None,
        }
    }
}

/// Result of simulation run.
#[derive(Debug)]
pub struct SimulationResult {
    pub stats: StatsSnapshot,
    pub failed_seeds: Vec<u64>,
    pub duration: Duration,
}

/// Coordinates multi-threaded simulation execution.
pub struct Coordinator {
    config: CoordinatorConfig,
    stats: Arc<SimulationStats>,
    shutdown: Arc<AtomicBool>,
    metrics: Option<SharedMetrics>,
}

impl Coordinator {
    pub fn new(config: CoordinatorConfig) -> Self {
        Self {
            config,
            stats: Arc::new(SimulationStats::new()),
            shutdown: Arc::new(AtomicBool::new(false)),
            metrics: None,
        }
    }

    pub fn with_metrics(config: CoordinatorConfig, metrics: SharedMetrics) -> Self {
        Self {
            config,
            stats: Arc::new(SimulationStats::new()),
            shutdown: Arc::new(AtomicBool::new(false)),
            metrics: Some(metrics),
        }
    }

    /// Get current stats.
    pub fn stats(&self) -> StatsSnapshot {
        self.stats.snapshot()
    }

    /// Signal shutdown to workers.
    pub fn shutdown(&self) {
        self.shutdown.store(true, Ordering::Relaxed);
    }

    /// Run simulation with UBT adapter.
    pub fn run_with_ubt_adapter(&self) -> SimulationResult {
        use crate::simulation::metrics::server::MetricsServer;
        use std::sync::Mutex;

        let start = Instant::now();
        let failed_seeds = Arc::new(Mutex::new(Vec::new()));

        let seeds: Vec<u64> = (self.config.seed_start..self.config.seed_end).collect();
        let total_seeds = seeds.len() as u64;
        let seed_queue = Arc::new(Mutex::new(seeds.into_iter()));

        // Initialize metrics
        let metrics = self.metrics.clone().unwrap_or_else(crate::simulation::metrics::create_shared_metrics);
        metrics.set_seeds_total(total_seeds);
        metrics.set_seeds_remaining(total_seeds);
        metrics.set_active_workers(self.config.num_workers as u64);

        // Start metrics server if port configured
        let mut metrics_server = if let Some(port) = self.config.metrics_port {
            match MetricsServer::start(port, Arc::clone(&metrics)) {
                Ok(server) => Some(server),
                Err(e) => {
                    eprintln!("[WARN] Failed to start metrics server on port {}: {}", port, e);
                    None
                }
            }
        } else {
            None
        };

        let mut handles = Vec::new();

        for worker_id in 0..self.config.num_workers {
            let queue = Arc::clone(&seed_queue);
            let stats = Arc::clone(&self.stats);
            let shutdown = Arc::clone(&self.shutdown);
            let failed = Arc::clone(&failed_seeds);
            let config = self.config.workload.clone();
            let worker_metrics = Arc::clone(&metrics);

            let handle = thread::spawn(move || {
                worker_loop(worker_id, queue, stats, shutdown, failed, config, worker_metrics);
            });
            handles.push(handle);
        }

        let stats_for_progress = Arc::clone(&self.stats);
        let metrics_for_progress = Arc::clone(&metrics);
        let shutdown_for_progress = Arc::clone(&self.shutdown);
        let interval = self.config.progress_interval;

        let progress_handle = thread::spawn(move || {
            while !shutdown_for_progress.load(Ordering::Relaxed) {
                thread::sleep(interval);
                let snap = stats_for_progress.snapshot();
                let pct = (snap.seeds_completed as f64 / total_seeds as f64) * 100.0;
                let msnap = metrics_for_progress.snapshot();
                eprintln!(
                    "[PROGRESS] {:.1}% ({}/{}) - {} ops ({:.0}/s) - {} chaos ops - {} failures",
                    pct,
                    snap.seeds_completed,
                    total_seeds,
                    snap.total_operations,
                    msnap.operations_per_second(),
                    msnap.chaos_ops_total,
                    snap.seeds_failed
                );

                if snap.seeds_completed >= total_seeds {
                    break;
                }
            }
        });

        for handle in handles {
            let _ = handle.join();
        }

        self.shutdown();
        let _ = progress_handle.join();

        // Shutdown metrics server
        if let Some(ref mut server) = metrics_server {
            server.shutdown();
        }

        let final_stats = self.stats.snapshot();
        let failed = failed_seeds.lock().unwrap().clone();

        SimulationResult {
            stats: final_stats,
            failed_seeds: failed,
            duration: start.elapsed(),
        }
    }
}

fn worker_loop(
    _worker_id: usize,
    queue: Arc<std::sync::Mutex<std::vec::IntoIter<u64>>>,
    stats: Arc<SimulationStats>,
    shutdown: Arc<AtomicBool>,
    failed_seeds: Arc<std::sync::Mutex<Vec<u64>>>,
    config: WorkloadConfig,
    metrics: SharedMetrics,
) {
    use crate::simulation::ubt_adapter::UbtDatabase;
    use crate::simulation::workload::{TestableDatabase, WorkloadRunner};

    metrics.worker_started();

    loop {
        if shutdown.load(Ordering::Relaxed) {
            break;
        }

        let seed = {
            let mut q = queue.lock().unwrap();
            q.next()
        };

        let seed = match seed {
            Some(s) => s,
            None => break,
        };

        let db = UbtDatabase::create();
        let mut runner = WorkloadRunner::with_metrics(db, config.clone(), Arc::clone(&metrics));
        let mut ctx = WorkloadContext::new(seed, 0);

        let result = runner.run(&mut ctx);

        // Update metrics
        metrics.inc_operations(result.operations_executed);
        metrics.dec_seeds_remaining();

        if result.success {
            metrics.inc_seeds_completed();
        } else {
            metrics.inc_seeds_failed();
            metrics.inc_invariant_violations(result.violations.len() as u64);
            failed_seeds.lock().unwrap().push(seed);
        }

        stats.record_result(&result);
    }

    metrics.worker_finished();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_coordinator_basic() {
        let config = CoordinatorConfig {
            num_workers: 2,
            seed_start: 0,
            seed_end: 100,
            workload: WorkloadConfig {
                operations_per_run: 100,
                ..Default::default()
            },
            progress_interval: Duration::from_secs(60),
            metrics_port: None,
        };

        let coordinator = Coordinator::new(config);
        let result = coordinator.run_with_ubt_adapter();

        assert_eq!(result.stats.seeds_completed, 100);
        assert!(result.failed_seeds.is_empty(), "UBT adapter should not fail");
    }

    #[test]
    fn test_coordinator_with_metrics() {
        let metrics = crate::simulation::metrics::create_shared_metrics();
        let config = CoordinatorConfig {
            num_workers: 2,
            seed_start: 0,
            seed_end: 50,
            workload: WorkloadConfig {
                operations_per_run: 100,
                ..Default::default()
            },
            progress_interval: Duration::from_secs(60),
            metrics_port: None,
        };

        let coordinator = Coordinator::with_metrics(config, Arc::clone(&metrics));
        let result = coordinator.run_with_ubt_adapter();

        assert_eq!(result.stats.seeds_completed, 50);

        let msnap = metrics.snapshot();
        assert_eq!(msnap.seeds_completed, 50);
        assert!(msnap.operations_total > 0);
        assert!(msnap.chaos_ops_total > 0);
    }

    #[test]
    fn test_stats_accumulate() {
        let stats = SimulationStats::new();

        let result1 = WorkloadResult::success(1, 100, Duration::from_millis(10));
        let result2 = WorkloadResult::success(2, 200, Duration::from_millis(20));

        stats.record_result(&result1);
        stats.record_result(&result2);

        let snap = stats.snapshot();
        assert_eq!(snap.seeds_completed, 2);
        assert_eq!(snap.total_operations, 300);
    }
}
