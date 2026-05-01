---
id: TASK-19
title: Compact binary serialization codec
status: In Progress
assignee: []
created_date: '2026-05-01 06:00'
labels: []
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Implement a compact binary encoding for UBT nodes, suitable for persistent NodeStore backends and wire-compatible with go-ethereum's bintrie serialization format.

### Wire Format

**StemNode** (variable length):
```
[1B type=0x02] [31B stem] [32B bitmap] [N×32B values]
```
- Bitmap: 256 bits, bit i set = subindex i has a value
- Values: in ascending subindex order, only for set bits
- Total: 64 + N×32 bytes

### Scope
- `src/codec.rs` module with encode/decode functions
- `InvalidEncoding` error variant
- Round-trip tests, edge cases, property tests
- Export from lib.rs, document in README
<!-- SECTION:DESCRIPTION:END -->
