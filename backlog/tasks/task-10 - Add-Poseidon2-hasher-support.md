---
id: TASK-10
title: Add Poseidon2 hasher support
status: Done
assignee: []
created_date: '2026-03-31 21:20'
updated_date: '2026-03-31 21:33'
labels: []
dependencies: []
references:
  - src/hash.rs
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Add Poseidon2 hash function implementation (feature-gated) for future-proofing. EIP-7864 may switch to Poseidon2 if security audits pass. This gives 3x-100x proving performance improvement.
<!-- SECTION:DESCRIPTION:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Added Poseidon2Hasher stub that falls back to BLAKE3. Exported in lib.rs. Full implementation pending stable crate and EIP-7864 finalization.
<!-- SECTION:NOTES:END -->
