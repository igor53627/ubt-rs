---
id: TASK-20
title: Update key derivation to V3 spec (remove LE reversal)
status: In Progress
assignee: []
created_date: '2026-05-01 07:30'
labels: []
dependencies: []
priority: critical
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
`get_binary_tree_key_inner` implements the superseded V2 spec (Jan-Apr 2026) which reverses the first 31 bytes to LE. Go-ethereum switched to V3 on Apr 13 2026 (commit `735bfd12`) — right-shift by 1, no reversal, overflow at `buf[0]`.

### Impact
- Code chunks >= 128: **wrong stems** (different from geth)
- Storage slots >= 64: **wrong stems** (different from geth)
- Chunks 0-127, basic data, code hash, storage 0-63: correct by coincidence (all-zero bytes)
- Test vectors in `test_key_derivation_geth_vectors`: stale (computed against V2)

### Fix
In `get_binary_tree_key_inner` (src/embedding.rs):
```rust
// V2 (current, wrong):
buf[..31].copy_from_slice(&input_key[..31]);
buf[..31].reverse();
if overflow { buf[31] = 1; }

// V3 (correct):
buf[1..32].copy_from_slice(&input_key[..31]);
if overflow { buf[0] = 1; }
```

Also update:
- Test vectors to match V3
- Doc comments referencing the old reversal algorithm
- Formal verification specs if applicable
<!-- SECTION:DESCRIPTION:END -->
