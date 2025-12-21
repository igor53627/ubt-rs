//! Simulation test harness for UBT.

mod simulation;

use simulation::{Coordinator, CoordinatorConfig, WorkloadConfig};
use std::time::Duration;

#[test]
fn test_simulation_small() {
    let config = CoordinatorConfig {
        num_workers: 2,
        seed_start: 0,
        seed_end: 10,
        workload: WorkloadConfig {
            operations_per_run: 100,
            ..Default::default()
        },
        progress_interval: Duration::from_secs(60),
        metrics_port: None,
    };

    let coordinator = Coordinator::new(config);
    let result = coordinator.run_with_ubt_adapter();

    assert_eq!(result.stats.seeds_completed, 10);
    assert!(
        result.failed_seeds.is_empty(),
        "Failed seeds: {:?}",
        result.failed_seeds
    );
}

#[test]
fn test_workload_runner_directly() {
    use simulation::{WorkloadContext, WorkloadRunner};
    use simulation::ubt_adapter::UbtDatabase;
    use simulation::workload::TestableDatabase;

    let db = UbtDatabase::create();
    let config = WorkloadConfig {
        operations_per_run: 500,
        key_space_size: 1000,
        enable_extended_ops: true,
        enable_chaos_ops: true,
    };
    
    let mut runner = WorkloadRunner::new(db, config);
    let mut ctx = WorkloadContext::new(42, 0);
    
    let result = runner.run(&mut ctx);
    assert!(result.success, "Violations: {:?}", result.violations);
    assert_eq!(result.operations_executed, 500);
}

#[test]
fn test_metrics_collection() {
    use std::sync::Arc;
    use simulation::{WorkloadContext, WorkloadRunner, create_shared_metrics};
    use simulation::ubt_adapter::UbtDatabase;
    use simulation::workload::TestableDatabase;

    let metrics = create_shared_metrics();
    let db = UbtDatabase::create();
    let config = WorkloadConfig {
        operations_per_run: 100,
        ..Default::default()
    };
    
    let mut runner = WorkloadRunner::with_metrics(db, config, Arc::clone(&metrics));
    let mut ctx = WorkloadContext::new(123, 0);
    
    let result = runner.run(&mut ctx);
    assert!(result.success);
    
    let snap = metrics.snapshot();
    assert!(snap.chaos_ops_total > 0, "Should have executed some chaos ops");
}
