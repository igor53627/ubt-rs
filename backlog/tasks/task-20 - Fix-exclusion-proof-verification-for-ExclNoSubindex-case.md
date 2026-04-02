---
id: TASK-20
title: Fix exclusion proof verification for ExclNoSubindex case
status: Completed
assignee: [Gemini]
created_date: '2026-04-01'
updated_date: '2026-04-02'
labels:
  - formal-verification
  - bug
  - P1
dependencies: []
references:
  - formal/simulations/tree.v
  - PR #3 review thread (roborev)
priority: high
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
The `verify_exclusion_proof` function in `formal/simulations/tree.v` incorrectly handles the `ExclNoSubindex` case. It always uses `zero_hash` instead of reconstructing the stem hash from the provided `ep_stem_proof` witness.

**Bug Details:**
- Current: `let stem_hash := hash_stem (tk_stem (ep_key proof)) zero_hash in`
- Problem: `ep_case` and `ep_stem_proof` fields are completely ignored
- Impact: Exclusion proofs for stems that exist but don't have a specific subindex can never verify

**Expected Behavior:**
For `ExclNoSubindex` case:
```coq
let stem_root := compute_root_from_witness zero32 (ep_stem_proof proof) in
let stem_hash := hash_stem (tk_stem (ep_key proof)) stem_root in
```

Reference: GitHub PR #3 roborev review comment
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria

<!-- SECTION:CRITERIA:BEGIN -->
- [x] Fix `verify_exclusion_proof` to handle both `ExclNoStem` and `ExclNoSubindex` cases
- [x] Update `verify_exclusion_proof_b` boolean version accordingly
- [x] Update or add proof lemmas that depend on these definitions
- [x] Verify fix against Rust implementation behavior
- [x] Close roborev review thread on PR #3
<!-- SECTION:CRITERIA:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
**Complexity:** High - requires formal verification expertise

**Files to modify:**
- `formal/simulations/tree.v` - Main definition changes (lines ~1437-1455)
- Affected theorems will need re-proving

**Related definitions:**
- `ExclusionProof` record (lines ~1406-1425)
- `ExclusionCase` inductive type
- `verify_exclusion_proof` and `verify_exclusion_proof_b`
- All theorems using these definitions

**Warning:** This is a breaking change to the formal model. Any proofs using `verify_exclusion_proof` will need to be updated.
<!-- SECTION:NOTES:END -->
