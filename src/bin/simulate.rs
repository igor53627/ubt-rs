//! CLI binary for running UBT simulation tests.
//!
//! Usage:
//!   cargo run --bin simulate -- --seeds 0..1000 --workers 4
//!   cargo run --bin simulate -- --seed 12345 --ops 10000
//!   cargo run --bin simulate -- --seeds 0..10000 --metrics-port 9090

use std::sync::Arc;
use std::time::Duration;

#[path = "../../tests/simulation/mod.rs"]
mod simulation;

use simulation::{
    Coordinator, CoordinatorConfig, UbtDatabase, WorkloadConfig, WorkloadContext, WorkloadRunner,
    TestableDatabase, create_shared_metrics,
};

fn main() {
    let args: Vec<String> = std::env::args().collect();

    if args.iter().any(|a| a == "--help" || a == "-h") {
        print_usage();
        return;
    }

    let single_seed = parse_arg(&args, "--seed").map(|s| s.parse::<u64>().expect("invalid seed"));
    let ops = parse_arg(&args, "--ops")
        .map(|s| s.parse::<u64>().expect("invalid ops"))
        .unwrap_or(1000);
    let workers = parse_arg(&args, "--workers")
        .map(|s| s.parse::<usize>().expect("invalid workers"))
        .unwrap_or(num_cpus::get());
    let metrics_port = parse_arg(&args, "--metrics-port")
        .map(|s| s.parse::<u16>().expect("invalid metrics port"));

    let (seed_start, seed_end) = if let Some(range) = parse_arg(&args, "--seeds") {
        parse_seed_range(&range)
    } else if let Some(seed) = single_seed {
        (seed, seed + 1)
    } else {
        (0, 10_000)
    };

    println!("=== UBT Simulation Testing ===");
    println!("Seeds: {}..{}", seed_start, seed_end);
    println!("Workers: {}", workers);
    println!("Ops per seed: {}", ops);
    if let Some(port) = metrics_port {
        println!("Metrics: http://0.0.0.0:{}/metrics", port);
    }
    println!();

    if let Some(seed) = single_seed {
        run_single_seed(seed, ops);
    } else {
        run_multi_seed(seed_start, seed_end, workers, ops, metrics_port);
    }
}

fn run_single_seed(seed: u64, ops: u64) {
    println!("Running single seed: {}", seed);

    let config = WorkloadConfig {
        operations_per_run: ops,
        ..Default::default()
    };

    let metrics = create_shared_metrics();
    let db = UbtDatabase::create();
    let mut runner = WorkloadRunner::with_metrics(db, config, Arc::clone(&metrics));
    let mut ctx = WorkloadContext::new(seed, 0);

    let result = runner.run(&mut ctx);

    if result.success {
        println!(
            "[PASS] Seed {} - {} ops in {:?}",
            seed, result.operations_executed, result.duration
        );

        let snap = metrics.snapshot();
        println!();
        println!("Operation breakdown:");
        println!("  Insert: {}", metrics.op_counters.insert.load(std::sync::atomic::Ordering::Relaxed));
        println!("  Get: {}", metrics.op_counters.get.load(std::sync::atomic::Ordering::Relaxed));
        println!("  Delete: {}", metrics.op_counters.delete.load(std::sync::atomic::Ordering::Relaxed));
        println!("  Chaos ops: {}", snap.chaos_ops_total);
    } else {
        println!(
            "[FAIL] Seed {} - {} ops in {:?}",
            seed, result.operations_executed, result.duration
        );
        for violation in &result.violations {
            println!("  Violation: {}", violation);
        }
        std::process::exit(1);
    }
}

fn run_multi_seed(seed_start: u64, seed_end: u64, workers: usize, ops: u64, metrics_port: Option<u16>) {
    let metrics = create_shared_metrics();

    let config = CoordinatorConfig {
        num_workers: workers,
        seed_start,
        seed_end,
        workload: WorkloadConfig {
            operations_per_run: ops,
            ..Default::default()
        },
        progress_interval: Duration::from_secs(5),
        metrics_port,
    };

    let coordinator = Coordinator::with_metrics(config, Arc::clone(&metrics));
    let result = coordinator.run_with_ubt_adapter();

    let msnap = metrics.snapshot();

    println!();
    println!("=== Simulation Complete ===");
    println!("Duration: {:?}", result.duration);
    println!("Seeds completed: {}", result.stats.seeds_completed);
    println!("Seeds failed: {}", result.stats.seeds_failed);
    println!("Total operations: {}", result.stats.total_operations);
    let duration_secs = result.duration.as_secs_f64();
    if duration_secs > 0.0 {
        println!(
            "Ops/sec: {:.0}",
            result.stats.total_operations as f64 / duration_secs
        );
    }
    println!();
    println!("Chaos operations: {}", msnap.chaos_ops_total);
    println!("  Toggle incremental: {}", metrics.op_counters.chaos_toggle_incremental.load(std::sync::atomic::Ordering::Relaxed));
    println!("  Verify incr vs full: {}", metrics.op_counters.chaos_verify_incremental_vs_full.load(std::sync::atomic::Ordering::Relaxed));
    println!("  Clear caches: {}", metrics.op_counters.chaos_clear_caches.load(std::sync::atomic::Ordering::Relaxed));
    println!("  Burst stem write: {}", metrics.op_counters.chaos_burst_stem_write.load(std::sync::atomic::Ordering::Relaxed));
    println!("  Insert/delete storm: {}", metrics.op_counters.chaos_insert_delete_storm.load(std::sync::atomic::Ordering::Relaxed));
    println!("  Root stability: {}", metrics.op_counters.chaos_root_stability.load(std::sync::atomic::Ordering::Relaxed));
    println!("  Delete stem: {}", metrics.op_counters.chaos_delete_stem.load(std::sync::atomic::Ordering::Relaxed));
    println!("  Get/scan consistency: {}", metrics.op_counters.chaos_get_scan_consistency.load(std::sync::atomic::Ordering::Relaxed));
    println!("  Mode switch storm: {}", metrics.op_counters.chaos_mode_switch_storm.load(std::sync::atomic::Ordering::Relaxed));
    println!("  Verify last root: {}", metrics.op_counters.chaos_verify_last_root.load(std::sync::atomic::Ordering::Relaxed));

    if !result.failed_seeds.is_empty() {
        println!();
        println!("Failed seeds:");
        for seed in &result.failed_seeds {
            println!("  {}", seed);
        }
        println!();
        println!("To reproduce a failure, run:");
        println!(
            "  cargo run --bin simulate -- --seed {} --ops {}",
            result.failed_seeds[0], ops
        );
        std::process::exit(1);
    }
}

fn parse_arg<'a>(args: &'a [String], name: &str) -> Option<&'a str> {
    args.iter()
        .position(|a| a == name)
        .and_then(|i| args.get(i + 1))
        .map(|s| s.as_str())
}

fn parse_seed_range(s: &str) -> (u64, u64) {
    let parts: Vec<&str> = s.split("..").collect();
    if parts.len() == 2 {
        let start = parts[0].parse().expect("invalid seed range start");
        let end = parts[1].parse().expect("invalid seed range end");
        (start, end)
    } else {
        panic!("invalid seed range format, expected START..END");
    }
}

fn print_usage() {
    println!("UBT Simulation Testing");
    println!();
    println!("USAGE:");
    println!("  simulate [OPTIONS]");
    println!();
    println!("OPTIONS:");
    println!("  --seed <N>           Run single seed for debugging");
    println!("  --seeds <S..E>       Seed range (default: 0..10000)");
    println!("  --ops <N>            Operations per seed (default: 1000)");
    println!("  --workers <N>        Worker threads (default: num_cpus)");
    println!("  --metrics-port <P>   Expose Prometheus metrics on port P");
    println!("  --help               Show this message");
    println!();
    println!("EXAMPLES:");
    println!("  simulate --seeds 0..1000 --workers 4");
    println!("  simulate --seed 12345 --ops 10000");
    println!("  simulate --seeds 0..100000 --metrics-port 9090");
    println!();
    println!("PROMETHEUS/GRAFANA:");
    println!("  # Start simulation with metrics endpoint");
    println!("  cargo run --release --bin simulate -- --seeds 0..1000000 --metrics-port 9090");
    println!();
    println!("  # Add to prometheus.yml:");
    println!("  scrape_configs:");
    println!("    - job_name: 'ubt-sim'");
    println!("      static_configs:");
    println!("        - targets: ['localhost:9090']");
}
