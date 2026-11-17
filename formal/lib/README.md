# UBT M Monad Interpreter Integration

This directory contains the M monad interpreter library for UBT's linking layer.

## Structure

```
formal/lib/
+-- MInterpreter.v          # Core stepping semantics (general-purpose M monad interpreter)
+-- StdlibHashMap.v         # HashMap as association list
+-- README.md               # This file
```

## Usage

`MInterpreter.v` and `StdlibHashMap.v` are the local copies of the general-purpose library and are the only copies in this repository.

The git submodule `formal/lib/rocq-of-rust-interp` (upstream `https://github.com/igor53627/rocq-of-rust-interp`) is removed. The upstream repository no longer exists, and no `.v` file imported `RocqInterp`.

`formal/Makefile` does not compile the files in this directory and does not map a logical path to it. No `.v` file in `specs/`, `simulations/`, `proofs/`, or `linking/` imports them. The linking layer uses its own modules (`linking/MRun.v`, `linking/hashmap_bridge.v`, `linking/ubt_stepping.v`) that follow the same design.

Both files require the RocqOfRust library (`RocqOfRust.RocqOfRust`, `RocqOfRust.links.M`; `MInterpreter.v` also requires `RocqOfRust.simulations.M`).

## Extension Points for UBT

The library provides parameters that UBT implements in `linking/ubt_stepping.v`:

### step_primitive_ext
Project-specific primitive stepping (not needed for core UBT operations; `ubt_step_primitive_ext` returns `None`).

### step_closure_ext
UBT implements this (`ubt_step_closure_ext`) for:
- `StemNode::new` - Stem node constructor
- `or_insert_with` - HashMap entry default factory

Closure stepping for `rust_get`, `rust_insert`, `rust_delete`, and `rust_root_hash` is listed as remaining work in `linking/ubt_stepping.v`.

### TraitRegistry
`MInterpreter.v` defines a `TraitRegistry` module for trait implementations. UBT's trait registry for the `Hasher` trait is in `linking/interpreter.v`.

## See Also

- [linking/interpreter.v](../linking/interpreter.v) - UBT-specific stepping implementation
- [linking/ubt_stepping.v](../linking/ubt_stepping.v) - UBT implementation of the extension points
- Issue #60 (old repository numbering; no longer resolves) - Axiom reduction roadmap
