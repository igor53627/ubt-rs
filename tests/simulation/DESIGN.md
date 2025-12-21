# UBT Simulation Testing Framework

Deterministic simulation testing inspired by [FoundationDB's simulation testing](https://apple.github.io/foundationdb/testing.html) and adapted from [mdbx-rs](https://github.com/paradigmxyz/reth-mdbx-rs).

## Philosophy

> "The most dangerous bugs occur in states you never imagined possible."

Instead of writing specific tests for scenarios we imagine, we generate random operation sequences with deterministic seeds. This finds edge cases that would take months to surface in production.

## Architecture

```text
+-----------------------------------------------------------------------+
|                        Simulation Coordinator                          |
|  (Spawns workers, aggregates stats, manages seeds)                     |
+-----------------------------------------------------------------------+
|  +-------------+  +-------------+  +-------------+  +-------------+   |
|  |  Worker 0   |  |  Worker 1   |  |  Worker 2   |  |  Worker N   |   |
|  |  Seed: 1000 |  |  Seed: 1001 |  |  Seed: 1002 |  |  Seed: ...  |   |
|  +------+------+  +------+------+  +------+------+  +------+------+   |
|         |                |                |                |          |
|         v                v                v                v          |
|  +-------------------------------------------------------------------+|
|  |                     Prometheus Metrics                             ||
|  |  - Operations/sec, Failures found, Seeds completed                 ||
|  +-------------------------------------------------------------------+|
+-----------------------------------------------------------------------+
```

## Core Components

### WorkloadContext
Provides deterministic randomness:
- Seeded PRNG (`StdRng`)
- 32-byte key/value generation
- Reproducible operation sequences

### TestableDatabase Trait
Abstraction for databases under test:
- `insert(key: [u8; 32], value: [u8; 32])`
- `get(key: [u8; 32]) -> Option<[u8; 32]>`
- `delete(key: [u8; 32]) -> bool`
- `sync() -> [u8; 32]` (returns root hash)
- `scan_all() -> Vec<(key, value)>`

### UbtDatabase Adapter
Wraps `UnifiedBinaryTree<Blake3Hasher>`:
- Implements `TestableDatabase`
- Calls `root_hash()` on sync
- Maintains parallel BTreeMap for scan operations

### Invariants

#### UbtReferenceModel
In-memory BTreeMap tracking expected state:
- Mirror of all insert/delete operations
- Used to verify correctness

#### MerkleInvariantChecker
Verifies Merkle tree properties:
- Root hash matches fresh rebuild from reference model
- Get results match expected values

## Usage

### Single seed (debugging)
```bash
cargo run --bin simulate -- --seed 12345 --ops 10000
```

### Multi-threaded simulation
```bash
cargo run --release --bin simulate -- --seeds 0..100000 --workers 8
```

### Reproduce a failure
```bash
cargo run --bin simulate -- --seed <failed_seed> --ops 1000
```

## Chaos/Nemesis Operations (BUGGIFY)

Inspired by [FoundationDB's BUGGIFY](https://transactional.blog/simulation/buggify) patterns, the simulation injects chaos to find edge-case bugs:

| Op | Name | Description |
|----|------|-------------|
| 10 | Toggle Incremental Mode | Switch between incremental/full rebuild |
| 11 | Verify Incremental vs Full | Force full rebuild and compare root hashes |
| 12 | Clear Caches | Clear internal caches, verify root unchanged |
| 13 | Burst Stem Write | Write 16 keys to same stem (stress stem nodes) |
| 14 | Insert/Delete Storm | Rapidly add and remove keys |
| 15 | Root Stability Check | Verify root hash is stable across multiple calls |
| 16 | Delete Entire Stem | Insert + delete all keys in stem, verify cleanup |
| 17 | Get/Scan Consistency | Verify direct get matches scan results |
| 18 | Mode Switch Storm | Toggle modes while doing operations |
| 19 | Track Root Changes | Monitor root hash across mutations |

### BUGGIFY Philosophy

From FDB: "BUGGIFY exists to bias the simulator towards doing dangerous, bug-finding things."

Key patterns:
- **Performing Minimal Work**: Test with minimal quorums, minimal cache, etc.
- **Forcing Error Handling**: Trigger rare error paths
- **Emphasizing Concurrency**: Add delays, toggle modes mid-operation
- **Randomizing Tuning Knobs**: Test with different configurations

## Determinism Rules

| Rule | Why |
|------|-----|
| Use `BTreeMap`, not `HashMap` | HashMap iteration is non-deterministic |
| Use `ctx.rng()`, not `rand::random()` | All randomness from seeded PRNG |
| Fixed 32-byte keys/values | Match UBT's native types |

## Observability

### Prometheus Metrics

The simulation exposes metrics via a built-in HTTP server for Prometheus scraping:

```bash
# Start simulation with metrics endpoint
cargo run --release --bin simulate -- --seeds 0..1000000 --metrics-port 9090
```

#### Available Metrics

| Metric | Type | Description |
|--------|------|-------------|
| `ubt_sim_operations_total` | counter | Total operations executed |
| `ubt_sim_operations_per_second` | gauge | Current ops/sec |
| `ubt_sim_seeds_completed` | counter | Seeds completed |
| `ubt_sim_seeds_failed` | counter | Seeds with failures |
| `ubt_sim_seeds_total` | gauge | Total seeds to process |
| `ubt_sim_progress_percent` | gauge | Completion percentage |
| `ubt_sim_active_workers` | gauge | Active worker threads |
| `ubt_sim_uptime_seconds` | gauge | Simulation uptime |
| `ubt_sim_chaos_ops_total` | counter | Total chaos operations |

#### Per-Operation Counters

Regular operations (0-9):
- `ubt_sim_op_insert_total`, `ubt_sim_op_get_total`, `ubt_sim_op_delete_total`
- `ubt_sim_op_update_hot_key_total`, `ubt_sim_op_sequential_insert_total`
- `ubt_sim_op_scan_all_total`, `ubt_sim_op_read_after_write_total`
- `ubt_sim_op_rapid_overwrite_total`, `ubt_sim_op_insert_then_delete_total`
- `ubt_sim_op_sync_total`

Chaos operations (10-19):
- `ubt_sim_chaos_toggle_incremental_total`
- `ubt_sim_chaos_verify_incremental_vs_full_total`
- `ubt_sim_chaos_clear_caches_total`
- `ubt_sim_chaos_burst_stem_write_total`
- `ubt_sim_chaos_insert_delete_storm_total`
- `ubt_sim_chaos_root_stability_total`
- `ubt_sim_chaos_delete_stem_total`
- `ubt_sim_chaos_get_scan_consistency_total`
- `ubt_sim_chaos_mode_switch_storm_total`
- `ubt_sim_chaos_verify_last_root_total`

### Prometheus Configuration

Add to `prometheus.yml`:

```yaml
scrape_configs:
  - job_name: 'ubt-sim'
    scrape_interval: 5s
    static_configs:
      - targets: ['localhost:9090']
```

### Grafana Dashboard

Import the dashboard from `tests/simulation/grafana/simulation-dashboard.json`.

The dashboard includes:
- **Progress**: Completion percentage stat
- **Failures Found**: Count of failed seeds (red if > 0)
- **Ops/sec**: Current throughput
- **Active Workers**: Thread count
- **Operations per Second**: Time series graph
- **Seeds Progress**: Completed vs failed over time
- **Chaos Operations (BUGGIFY)**: Stacked bar chart of chaos ops
- **Regular Operations**: Stacked bar chart of CRUD ops
- **Total Operations**: Running total
- **Uptime**: Simulation duration

### Quick Start

```bash
# Terminal 1: Start simulation
cargo run --release --bin simulate -- \
  --seeds 0..1000000 \
  --workers 8 \
  --metrics-port 9090

# Terminal 2: Test metrics endpoint
curl http://localhost:9090/metrics

# Terminal 3: Start Prometheus
prometheus --config.file=prometheus.yml

# Access Grafana at http://localhost:3000
# Import dashboard from tests/simulation/grafana/simulation-dashboard.json
```

## File Structure

```text
tests/simulation/
+-- mod.rs           # Module exports
+-- DESIGN.md        # This document
+-- context.rs       # WorkloadContext, deterministic RNG
+-- coordinator.rs   # Multi-threaded coordinator
+-- invariants.rs    # UbtReferenceModel, MerkleInvariantChecker
+-- metrics.rs       # Prometheus metrics + HTTP server
+-- ubt_adapter.rs   # TestableDatabase impl for UBT
+-- workload.rs      # WorkloadRunner, WorkloadConfig
+-- grafana/
    +-- simulation-dashboard.json  # Grafana dashboard
```

## Future Work

1. Integrate reference model verification into workload
2. Add Merkle proof generation/verification tests
3. Add incremental mode invariants (dual tree comparison)
