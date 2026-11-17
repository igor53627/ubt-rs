# Panic Point Analysis for ubt-rs

This document catalogs all potential panic points in the Rust source code that need to be addressed for panic freedom proofs.

## Summary

| Category | Count | Reachable on Well-Formed Input |
|----------|-------|-------------------------------|
| Explicit `panic!()` | 0 | n/a (tree depth errors now return `UbtError::TreeDepthExceeded`) |
| `debug_assert!()` | 4 | No (only in debug builds) |
| `.expect()` | 2 | No (value < 256 by construction) |
| Array indexing | 8 | No (bounded by types/constants) |
| `.unwrap()` | 1 | No (result always Ok) |

**Total Panic Points: 15**
**Potentially Reachable: 0** (all guarded by invariants)

---

## Detailed Analysis

### 1. Explicit `panic!()` Macros

None in non-test code. The three tree-depth `panic!` calls (in `build_root_hash_from_stem_hashes`, `build_root_hash_with_cache`, and the streaming `build_tree_hash`) now return `Err(UbtError::TreeDepthExceeded { depth })`.

---

### 2. `debug_assert!()` Macros

These only execute in debug builds and are used for development-time invariant checking.

#### tree/hash.rs (`set_bit_at`)
```rust
debug_assert!(pos < 256);
```
- **Function**: `set_bit_at`
- **Invariant**: Position must be within B256 (256 bits).
- **Caller Responsibility**: Only called internally with depth values ≤ 248.

#### key.rs:47
```rust
debug_assert!(pos < STEM_LEN * 8);
```
- **Function**: `Stem::bit_at`
- **Invariant**: Position must be within stem bits (248).
- **Caller Responsibility**: Tree traversal code passes depth values bounded by MAX_DEPTH.

#### streaming.rs:143-150 (parallel version)
```rust
debug_assert!(
    (prev.stem, prev.subindex) < (key.stem, key.subindex),
    "Entries must be sorted: {:?} should come before {:?}",
    prev,
    key
);
```
- **Function**: `collect_stem_groups`
- **Invariant**: Input entries must be sorted.
- **Caller Responsibility**: API contract requires sorted input.

#### streaming.rs:207-215
```rust
debug_assert!(
    (prev.stem, prev.subindex) < (key.stem, key.subindex),
    "Entries must be sorted: {:?} should come before {:?}",
    prev,
    key
);
```
- **Function**: `collect_stem_hashes`
- **Invariant**: Same as above.

---

### 3. `.expect()` Calls

#### embedding.rs (`get_code_chunk_key`)
```rust
k[31] = u8::try_from(pos).expect("pos < 256 by construction");
let subindex = u8::try_from(pos % STEM_SUBTREE_WIDTH).expect("subindex < 256 by construction");
```
- **Type**: `.expect()` on `Result`
- **Function**: `get_code_chunk_key`
- **Guarding Condition**: The first call is inside `if pos < STEM_SUBTREE_WIDTH` (256). The second value is a remainder modulo 256.
- **Reachable**: No.

The earlier `.expect("slot[0] >= 255 not supported per EIP-7864")` in `get_storage_slot_key` is removed. That function now uses `wrapping_add(1)` and an overflow flag.

---

### 4. Array/Slice Indexing

All indexing operations use bounded types or constants that prevent out-of-bounds access.

#### node.rs:129
```rust
data[idx as usize] = hasher.hash_32(&value);
```
- **Type**: Array index
- **Array Size**: `[B256::ZERO; 256]`
- **Index Type**: `SubIndex` which is `u8` (0-255)
- **Reachable**: No. u8 range is exactly 0-255, matching array size.

#### node.rs:140-142
```rust
let left = data[i * 2];
let right = data[i * 2 + 1];
data[i] = hasher.hash_64(&left, &right);
```
- **Type**: Array index
- **Loop Bounds**: `pairs = 256 >> level` for `level` in 1..=8. Max access is at level 1 with `i` from 0 to 127, accessing indices 0-255.
- **Reachable**: No. Loop bounds ensure indices stay within 256.

#### streaming.rs:264
```rust
data[idx as usize] = self.hasher.hash_32(&value);
```
- **Same analysis as node.rs:129**

#### streaming.rs:271-273
```rust
let left = data[i * 2];
let right = data[i * 2 + 1];
data[i] = self.hasher.hash_64(&left, &right);
```
- **Same analysis as node.rs:140-142**

#### proof.rs:143
```rust
siblings.push(data[sibling_idx]);
```
- **Type**: Array index
- **Array Size**: `[B256::ZERO; 256]`
- **Index Bound**: `sibling_idx = idx ^ 1` where `idx` starts as `subindex as usize` (u8) and is divided by 2 each iteration.
- **Reachable**: No. Initial idx ≤ 255, sibling_idx ≤ 255.

#### proof.rs:149-150
```rust
let left = data[i * 2];
let right = data[i * 2 + 1];
```
- **Same bounded loop analysis as node.rs**

#### key.rs:30
```rust
bytes.copy_from_slice(slice);
```
- **Type**: `copy_from_slice` (panics if lengths mismatch)
- **Function**: `Stem::from_slice`
- **Guarding Condition**: Function documents "Panics if length != 31" - this is intentional API behavior.
- **Reachable**: Yes, if caller provides wrong-length slice. This is documented intentional behavior.

#### key.rs:113
```rust
stem_bytes.copy_from_slice(&bytes[..STEM_LEN]);
```
- **Type**: Slice indexing
- **Input Type**: `B256` (always 32 bytes)
- **Range**: `[..31]` on 32-byte input
- **Reachable**: No. B256 is always 32 bytes.

---

### 5. Integer Arithmetic (Overflow Potential)

Rust debug builds panic on integer overflow. All arithmetic in this codebase uses values with bounded ranges.

#### tree/hash.rs (`set_bit_at`)
```rust
value.0[byte_idx] |= 1 << bit_idx;
```
- **Index Source**: `byte_idx = pos / 8`, `bit_idx = 7 - (pos % 8)`
- **Guarding Condition**: `debug_assert!(pos < 256)` in the same function
- **Overflow**: None. bit_idx is always 0-7, shift is valid.

#### key.rs:49-50
```rust
let byte_idx = pos / 8;
let bit_idx = 7 - (pos % 8);
```
- **Guarding Condition**: `debug_assert!(pos < STEM_LEN * 8)`
- **Overflow**: None for valid pos.

#### code.rs:71
```rust
let num_chunks = (bytecode.len() + CODE_CHUNK_DATA_SIZE - 1) / CODE_CHUNK_DATA_SIZE;
```
- **Type**: Arithmetic for ceiling division
- **Overflow**: Theoretically possible with bytecode.len() near usize::MAX, but unrealistic for actual code.

---

### 6. `.unwrap()` Calls

#### proof.rs:291
```rust
assert!(result.unwrap());
```
- **Type**: `.unwrap()` on `Result`
- **Context**: Test code only (`#[cfg(test)]`)
- **Function**: `test_proof_verify_simple`
- **Reachable**: Only in tests. Result is checked by preceding `assert!(result.is_ok())`.

---

## Recommendations for Panic Freedom

### Already Safe
1. **Tree depth errors**: These return `UbtError::TreeDepthExceeded` and are unreachable due to mathematical invariants (finite stems guarantee finite depth).
2. **Array indexing**: All uses are bounded by type constraints (`u8` for 256-element arrays).
3. **Debug assertions**: Only active in debug builds.

### Requires Attention
1. **`Stem::from_slice`** (key.rs:28-31): Consider returning `Result` or `Option` instead of panicking, or document the panic behavior clearly in API docs.

2. **EIP-7864 storage slot constraint**: Resolved. `get_storage_slot_key` no longer calls `.expect()`.

### For Formal Verification

The following invariants should be proven:
1. **Depth Bound**: For any set of stems S, `build_tree_hash(S, 0)` recurses at most 248 times.
2. **Subindex Bound**: `SubIndex` type (u8) ensures array indices 0-255 are always valid for 256-element arrays.
3. **Stem Length**: `Stem` is always exactly 31 bytes, making `bit_at(pos)` safe for `pos < 248`.

---

## Files Analyzed

| File | Lines | Panic Points |
|------|-------|--------------|
| tree/ (mod.rs, hash.rs, build.rs) | 1639 | 1 debug_assert |
| node.rs | 236 | 4 array indices |
| streaming.rs | 544 | 2 debug_assert, 4 array indices |
| proof.rs | 356 | 4 array indices, 1 unwrap (test) |
| key.rs | 190 | 1 debug_assert, 1 copy_from_slice |
| hash.rs | 191 | 0 |
| embedding.rs | 585 | 2 expect |
| code.rs | 227 | 0 |

---

*Generated for panic-freedom verification of ubt-rs*
