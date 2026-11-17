---
id: TASK-19
title: Compact binary serialization codec
status: Done
assignee: []
created_date: '2026-05-01 06:00'
labels: []
dependencies: []
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Implement a compact binary encoding for UBT nodes, suitable for persistent NodeStore backends.

Note (2026-11-17): the implemented format is not wire-compatible with the go-ethereum bintrie serialization. go-ethereum uses stem tag 1, internal tag 2, an MSB-first bitmap, and (since commit a15778c5) grouped internal nodes.

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
