//! Benchmark: Stem hashing vs Tree building
//!
//! This benchmark measures where the bottleneck is during full rebuilds:
//! - Stem hashing: Computing the 8-level binary tree for each stem (256 leaves)
//! - Tree building: Building the upper tree from stem hashes
//!
//! Results inform whether parallelizing stem hashing (issue #7) is worthwhile.

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use std::collections::HashMap;
use ubt::{Blake3Hasher, Hasher, Stem, TreeKey};
use alloy_primitives::B256;

fn generate_test_data(num_stems: usize, values_per_stem: usize) -> Vec<(TreeKey, B256)> {
    let mut entries = Vec::with_capacity(num_stems * values_per_stem);
    
    for i in 0..num_stems {
        let mut stem_bytes = [0u8; 31];
        stem_bytes[0] = (i >> 16) as u8;
        stem_bytes[1] = (i >> 8) as u8;
        stem_bytes[2] = i as u8;
        stem_bytes[15] = ((i * 7) % 256) as u8;
        let stem = Stem::new(stem_bytes);
        
        for j in 0..values_per_stem {
            let subindex = (j % 256) as u8;
            let key = TreeKey::new(stem, subindex);
            let value = B256::repeat_byte(((i + j) % 255 + 1) as u8);
            entries.push((key, value));
        }
    }
    
    entries.sort_by(|a, b| (a.0.stem, a.0.subindex).cmp(&(b.0.stem, b.0.subindex)));
    entries
}

/// Groups `(TreeKey, B256)` entries by stem.
///
/// Precondition: `entries` must be sorted by `TreeKey.stem`, so that all
/// entries for a given stem are contiguous.
fn group_entries_by_stem(entries: &[(TreeKey, B256)]) -> Vec<(Stem, HashMap<u8, B256>)> {
    let mut stem_groups: Vec<(Stem, HashMap<u8, B256>)> = Vec::new();
    let mut current_stem: Option<Stem> = None;
    let mut current_values: HashMap<u8, B256> = HashMap::new();
    
    for (key, value) in entries {
        match current_stem {
            Some(stem) if stem == key.stem => {
                current_values.insert(key.subindex, *value);
            }
            Some(stem) => {
                if !current_values.is_empty() {
                    stem_groups.push((stem, std::mem::take(&mut current_values)));
                }
                current_stem = Some(key.stem);
                current_values.insert(key.subindex, *value);
            }
            None => {
                current_stem = Some(key.stem);
                current_values.insert(key.subindex, *value);
            }
        }
    }
    if let Some(stem) = current_stem {
        if !current_values.is_empty() {
            stem_groups.push((stem, current_values));
        }
    }
    
    stem_groups
}

fn compute_stem_hash(hasher: &Blake3Hasher, values: &HashMap<u8, B256>) -> B256 {
    let mut data = [B256::ZERO; 256];
    for (&idx, &value) in values {
        data[idx as usize] = hasher.hash_32(&value);
    }

    for level in 1..=8 {
        let pairs = 256 >> level;
        for i in 0..pairs {
            let left = data[i * 2];
            let right = data[i * 2 + 1];
            data[i] = hasher.hash_64(&left, &right);
        }
    }

    let subtree_root = data[0];
    
    let mut input = [0u8; 64];
    input[31] = 0x00;
    input[32..].copy_from_slice(subtree_root.as_slice());
    hasher.hash_raw(&input)
}

fn build_tree_hash(hasher: &Blake3Hasher, stem_hashes: &[(Stem, B256)], depth: usize) -> B256 {
    if stem_hashes.is_empty() {
        return B256::ZERO;
    }

    if stem_hashes.len() == 1 {
        return stem_hashes[0].1;
    }

    if depth >= 248 {
        panic!("Tree depth exceeded");
    }

    let split_point = stem_hashes.partition_point(|(s, _)| !s.bit_at(depth));
    let (left, right) = stem_hashes.split_at(split_point);

    let left_hash = build_tree_hash(hasher, left, depth + 1);
    let right_hash = build_tree_hash(hasher, right, depth + 1);

    if left_hash.is_zero() && right_hash.is_zero() {
        B256::ZERO
    } else if left_hash.is_zero() {
        right_hash
    } else if right_hash.is_zero() {
        left_hash
    } else {
        hasher.hash_64(&left_hash, &right_hash)
    }
}

fn bench_stem_hashing(c: &mut Criterion) {
    let mut group = c.benchmark_group("stem_hashing");
    let hasher = Blake3Hasher;
    
    for num_stems in [1_000, 10_000, 100_000] {
        let entries = generate_test_data(num_stems, 5);
        let stem_groups = group_entries_by_stem(&entries);
        
        group.throughput(Throughput::Elements(num_stems as u64));
        group.bench_with_input(
            BenchmarkId::new("stems", num_stems),
            &stem_groups,
            |b, groups| {
                b.iter(|| {
                    let mut stem_hashes = Vec::with_capacity(groups.len());
                    for (stem, values) in groups {
                        let hash = compute_stem_hash(&hasher, values);
                        stem_hashes.push((*stem, hash));
                    }
                    black_box(stem_hashes)
                })
            },
        );
    }
    
    group.finish();
}

fn bench_tree_building(c: &mut Criterion) {
    let mut group = c.benchmark_group("tree_building");
    let hasher = Blake3Hasher;
    
    for num_stems in [1_000, 10_000, 100_000] {
        let mut stem_hashes: Vec<(Stem, B256)> = Vec::with_capacity(num_stems);
        for i in 0..num_stems {
            let mut stem_bytes = [0u8; 31];
            stem_bytes[0] = (i >> 16) as u8;
            stem_bytes[1] = (i >> 8) as u8;
            stem_bytes[2] = i as u8;
            stem_bytes[15] = ((i * 7) % 256) as u8;
            let stem = Stem::new(stem_bytes);
            let hash = B256::repeat_byte(((i % 255) + 1) as u8);
            stem_hashes.push((stem, hash));
        }
        stem_hashes.sort_by(|a, b| a.0.cmp(&b.0));
        
        group.throughput(Throughput::Elements(num_stems as u64));
        group.bench_with_input(
            BenchmarkId::new("stems", num_stems),
            &stem_hashes,
            |b, hashes| {
                b.iter(|| {
                    black_box(build_tree_hash(&hasher, hashes, 0))
                })
            },
        );
    }
    
    group.finish();
}

fn bench_full_rebuild(c: &mut Criterion) {
    let mut group = c.benchmark_group("full_rebuild");
    let hasher = Blake3Hasher;
    
    for num_stems in [1_000, 10_000, 50_000] {
        let entries = generate_test_data(num_stems, 5);
        
        group.throughput(Throughput::Elements(num_stems as u64));
        group.bench_with_input(
            BenchmarkId::new("stems", num_stems),
            &entries,
            |b, entries| {
                b.iter(|| {
                    let stem_groups = group_entries_by_stem(entries);
                    
                    let mut stem_hashes = Vec::with_capacity(stem_groups.len());
                    for (stem, values) in &stem_groups {
                        let hash = compute_stem_hash(&hasher, values);
                        stem_hashes.push((*stem, hash));
                    }
                    stem_hashes.sort_by(|a, b| a.0.cmp(&b.0));
                    
                    black_box(build_tree_hash(&hasher, &stem_hashes, 0))
                })
            },
        );
    }
    
    group.finish();
}

criterion_group!(
    benches,
    bench_stem_hashing,
    bench_tree_building,
    bench_full_rebuild,
);
criterion_main!(benches);
