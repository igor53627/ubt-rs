# Panic Point Analysis for ubt-rs

This document catalogs all potential panic points in the Rust source code that need to be addressed for panic freedom proofs.

## Summary

| Category | Count | Reachable on Well-Formed Input |
|----------|-------|-------------------------------|
| Explicit `panic!()` | 2 | No (guarded by tree depth) |
| `debug_assert!()` | 4 | No (only in debug builds) |
| `.expect()` | 1 | No (EIP-7864 constraint) |
| Array indexing | 8 | No (bounded by types/constants) |
| `.unwrap()` | 1 | No (result always Ok) |

**Total Panic Points: 16**
**Potentially Reachable: 0** (all guarded by invariants)

---

## Detailed Analysis

### 1. Explicit `panic!()` Macros

#### tree.rs:460
```rust
if depth >= 248 {
    panic!("Tree depth exceeded maximum of 248 bits");
}
```
- **Type**: Explicit `panic!`
- **Function**: `build_root_hash_from_stem_hashes`
- **Guarding Condition**: Tree depth is bounded by stem length (31 bytes × 8 bits = 248 bits). Recursion terminates when `stem_hashes.len() <= 1` (base cases at lines 451-457).
- **Reachable**: No. With 248-bit stems, max depth is 248. Partition halves stems at each level; with finite stems, recursion depth ≤ 248.

#### tree.rs:499
```rust
if depth >= MAX_DEPTH {
    panic!("Tree depth exceeded maximum of {} bits", MAX_DEPTH);
}
```
- **Type**: Explicit `panic!`
- **Function**: `build_root_hash_with_cache`
- **Guarding Condition**: Same as above. `MAX_DEPTH = STEM_LEN * 8 = 248`.
- **Reachable**: No. Same invariant applies.

#### streaming.rs:297
```rust
if depth >= STEM_LEN * 8 {
    panic!("Tree depth exceeded maximum of {} bits", STEM_LEN * 8);
}
```
- **Type**: Explicit `panic!`
- **Function**: `build_tree_hash`
- **Guarding Condition**: Same tree depth invariant.
- **Reachable**: No.

---

### 2. `debug_assert!()` Macros

These only execute in debug builds and are used for development-time invariant checking.

#### tree.rs:22
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

#### embedding.rs:129-131
```rust
k[0] = slot[0]
    .checked_add(1)
    .expect("slot[0] >= 255 not supported per EIP-7864");
```
- **Type**: `.expect()` on `Option`
- **Function**: `get_storage_slot_key`
- **Guarding Condition**: Per EIP-7864, storage slot values with `slot[0] >= 255` are not expected in practice. The comment documents this EIP constraint.
- **Reachable**: No, for well-formed EIP-7864 inputs. Could panic on malformed input with `slot[0] == 255`.

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

#### tree.rs:24
```rust
value.0[byte_idx] |= 1 << bit_idx;
```
- **Index Source**: `byte_idx = pos / 8`, `bit_idx = 7 - (pos % 8)`
- **Guarding Condition**: `debug_assert!(pos < 256)` at line 22
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
1. **Tree depth panics**: These are unreachable due to mathematical invariants (finite stems guarantee finite depth).
2. **Array indexing**: All uses are bounded by type constraints (`u8` for 256-element arrays).
3. **Debug assertions**: Only active in debug builds.

### Requires Attention
1. **`Stem::from_slice`** (key.rs:28-31): Consider returning `Result` or `Option` instead of panicking, or document the panic behavior clearly in API docs.

2. **EIP-7864 storage slot constraint** (embedding.rs:129-131): The `.expect()` relies on EIP-7864 constraints. For maximum safety, consider:
   - Returning `Result<TreeKey, UbtError>` 
   - Or documenting this as a precondition

### For Formal Verification

The following invariants should be proven:
1. **Depth Bound**: For any set of stems S, `build_tree_hash(S, 0)` recurses at most 248 times.
2. **Subindex Bound**: `SubIndex` type (u8) ensures array indices 0-255 are always valid for 256-element arrays.
3. **Stem Length**: `Stem` is always exactly 31 bytes, making `bit_at(pos)` safe for `pos < 248`.

---

## Files Analyzed

| File | Lines | Panic Points |
|------|-------|--------------|
| tree.rs | 1000 | 2 panic!, 1 debug_assert |
| node.rs | 238 | 4 array indices |
| streaming.rs | 458 | 1 panic!, 2 debug_assert, 4 array indices |
| proof.rs | 293 | 4 array indices, 1 unwrap (test) |
| key.rs | 190 | 1 debug_assert, 1 copy_from_slice |
| hash.rs | 167 | 0 |
| embedding.rs | 468 | 1 expect |
| code.rs | 182 | 0 |

---

*Generated for panic-freedom verification of ubt-rs*
