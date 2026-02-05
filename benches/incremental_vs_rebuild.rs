//! Benchmark: Incremental updates vs Full rebuilds
//!
//! This benchmark compares the performance of:
//! - Full rebuild: Recomputes entire tree on every root_hash() call
//! - Incremental mode: Caches intermediate nodes, only recomputes affected paths
//!
//! Results inform when to use each mode:
//! - Full rebuild: Best for bulk imports, initial tree population
//! - Incremental: Best for block-by-block updates with few changes per block

use alloy_primitives::B256;
use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use ubt::{Blake3Hasher, Stem, TreeKey, UnifiedBinaryTree};

fn generate_stems(count: usize) -> Vec<Stem> {
    (0..count)
        .map(|i| {
            let mut stem_bytes = [0u8; 31];
            stem_bytes[0] = (i >> 16) as u8;
            stem_bytes[1] = (i >> 8) as u8;
            stem_bytes[2] = i as u8;
            stem_bytes[15] = ((i * 7) % 256) as u8;
            Stem::new(stem_bytes)
        })
        .collect()
}

fn create_populated_tree(num_stems: usize) -> UnifiedBinaryTree<Blake3Hasher> {
    let mut tree = UnifiedBinaryTree::with_capacity(num_stems);
    let stems = generate_stems(num_stems);

    for (i, stem) in stems.iter().enumerate() {
        for j in 0..5 {
            let key = TreeKey::new(*stem, j as u8);
            tree.insert(key, B256::repeat_byte(((i + j) % 255 + 1) as u8));
        }
    }

    tree.root_hash().unwrap();
    tree
}

fn bench_single_update(c: &mut Criterion) {
    let mut group = c.benchmark_group("single_update");

    for num_stems in [1_000, 10_000, 50_000, 100_000] {
        group.throughput(Throughput::Elements(1));

        let tree_full = create_populated_tree(num_stems);
        group.bench_with_input(
            BenchmarkId::new("full_rebuild", num_stems),
            &tree_full,
            |b, tree| {
                b.iter_batched(
                    || tree.clone(),
                    |mut tree| {
                        let key = TreeKey::new(generate_stems(1)[0], 0);
                        tree.insert(key, B256::repeat_byte(0xFF));
                        black_box(tree.root_hash().unwrap())
                    },
                    criterion::BatchSize::SmallInput,
                )
            },
        );

        let mut tree_incr = tree_full.clone();
        tree_incr.enable_incremental_mode();
        tree_incr.root_hash().unwrap();

        group.bench_with_input(
            BenchmarkId::new("incremental", num_stems),
            &tree_incr,
            |b, tree| {
                b.iter_batched(
                    || tree.clone(),
                    |mut tree| {
                        let key = TreeKey::new(generate_stems(1)[0], 0);
                        tree.insert(key, B256::repeat_byte(0xFF));
                        black_box(tree.root_hash().unwrap())
                    },
                    criterion::BatchSize::SmallInput,
                )
            },
        );
    }

    group.finish();
}

fn bench_batch_update(c: &mut Criterion) {
    let mut group = c.benchmark_group("batch_update");

    for (num_stems, changes_per_batch) in [
        (10_000, 10),
        (10_000, 100),
        (10_000, 1_000),
        (50_000, 50),
        (50_000, 500),
        (100_000, 100),
        (100_000, 1_000),
    ] {
        let label = format!("{}stems_{}changes", num_stems, changes_per_batch);
        group.throughput(Throughput::Elements(changes_per_batch as u64));

        let tree_full = create_populated_tree(num_stems);
        let change_stems = generate_stems(num_stems);

        group.bench_with_input(
            BenchmarkId::new("full_rebuild", &label),
            &(tree_full.clone(), change_stems.clone()),
            |b, (tree, stems)| {
                b.iter_batched(
                    || tree.clone(),
                    |mut tree| {
                        for i in 0..changes_per_batch {
                            let key = TreeKey::new(stems[i % stems.len()], (i % 5) as u8);
                            tree.insert(key, B256::repeat_byte(0xAB));
                        }
                        black_box(tree.root_hash().unwrap())
                    },
                    criterion::BatchSize::SmallInput,
                )
            },
        );

        let mut tree_incr = tree_full.clone();
        tree_incr.enable_incremental_mode();
        tree_incr.root_hash().unwrap();

        group.bench_with_input(
            BenchmarkId::new("incremental", &label),
            &(tree_incr.clone(), change_stems.clone()),
            |b, (tree, stems)| {
                b.iter_batched(
                    || tree.clone(),
                    |mut tree| {
                        for i in 0..changes_per_batch {
                            let key = TreeKey::new(stems[i % stems.len()], (i % 5) as u8);
                            tree.insert(key, B256::repeat_byte(0xAB));
                        }
                        black_box(tree.root_hash().unwrap())
                    },
                    criterion::BatchSize::SmallInput,
                )
            },
        );
    }

    group.finish();
}

fn bench_block_simulation(c: &mut Criterion) {
    let mut group = c.benchmark_group("block_simulation");
    group.sample_size(50);

    let num_stems = 100_000;
    let changes_per_block = 500;

    group.throughput(Throughput::Elements(changes_per_block as u64));

    let tree_full = create_populated_tree(num_stems);
    let change_stems = generate_stems(num_stems);

    group.bench_with_input(
        BenchmarkId::new("full_rebuild", "100k_stems_500_changes"),
        &(tree_full.clone(), change_stems.clone()),
        |b, (tree, stems)| {
            b.iter_batched(
                || tree.clone(),
                |mut tree| {
                    for i in 0..changes_per_block {
                        let key = TreeKey::new(stems[i], (i % 5) as u8);
                        tree.insert(key, B256::repeat_byte(0xCD));
                    }
                    black_box(tree.root_hash().unwrap())
                },
                criterion::BatchSize::LargeInput,
            )
        },
    );

    let mut tree_incr = tree_full.clone();
    tree_incr.enable_incremental_mode();
    tree_incr.root_hash().unwrap();

    group.bench_with_input(
        BenchmarkId::new("incremental", "100k_stems_500_changes"),
        &(tree_incr.clone(), change_stems.clone()),
        |b, (tree, stems)| {
            b.iter_batched(
                || tree.clone(),
                |mut tree| {
                    for i in 0..changes_per_block {
                        let key = TreeKey::new(stems[i], (i % 5) as u8);
                        tree.insert(key, B256::repeat_byte(0xCD));
                    }
                    black_box(tree.root_hash().unwrap())
                },
                criterion::BatchSize::LargeInput,
            )
        },
    );

    group.finish();
}

fn bench_memory_overhead(c: &mut Criterion) {
    let mut group = c.benchmark_group("cache_population");

    for num_stems in [1_000, 10_000, 50_000] {
        group.throughput(Throughput::Elements(num_stems as u64));

        let tree = create_populated_tree(num_stems);

        group.bench_with_input(
            BenchmarkId::new("enable_and_populate", num_stems),
            &tree,
            |b, tree| {
                b.iter_batched(
                    || tree.clone(),
                    |mut tree| {
                        tree.enable_incremental_mode();
                        black_box(tree.root_hash().unwrap())
                    },
                    criterion::BatchSize::SmallInput,
                )
            },
        );
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_single_update,
    bench_batch_update,
    bench_block_simulation,
    bench_memory_overhead,
);
criterion_main!(benches);
