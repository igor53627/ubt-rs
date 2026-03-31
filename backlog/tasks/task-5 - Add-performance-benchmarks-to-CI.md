---
id: TASK-5
title: Add performance benchmarks to CI
status: Done
assignee: []
created_date: '2026-03-31 20:55'
updated_date: '2026-03-31 21:22'
labels: []
dependencies: []
priority: medium
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Add criterion benchmarks to CI to track performance regressions
<!-- SECTION:DESCRIPTION:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
Added benchmarks step to CI with --test flag for smoke testing. Uses continue-on-error to not block merges.
<!-- SECTION:NOTES:END -->
