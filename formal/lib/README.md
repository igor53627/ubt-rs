# UBT M Monad Interpreter Integration

This directory contains the M monad interpreter library for UBT's linking layer.

## Structure

```
formal/lib/
├── rocq-of-rust-interp/    # Git submodule: general-purpose M monad interpreter
│   └── src/
│       ├── MInterpreter.v  # Core stepping semantics
│       ├── StdlibHashMap.v # HashMap as association list
│       ├── StdlibVec.v     # Vec as Rocq list
│       └── ...
├── MInterpreter.v          # [DEPRECATED] Local copy, use submodule instead
├── StdlibHashMap.v         # [DEPRECATED] Local copy, use submodule instead
└── README.md               # This file
```

## Usage

The general-purpose library is now at https://github.com/igor53627/rocq-of-rust-interp

Import in your .v files:
```coq
Require Import RocqInterp.MInterpreter.
Require Import RocqInterp.StdlibHashMap.
```

The Makefile includes the library path via `-Q lib/rocq-of-rust-interp/src RocqInterp`.

## Extension Points for UBT

The library provides parameters that UBT implements in `linking/interpreter.v`:

### step_primitive_ext
Project-specific primitive stepping (not needed for core UBT operations).

### step_closure_ext  
UBT implements this for:
- `rust_get` - Tree get operation
- `rust_insert` - Tree insert operation  
- `rust_delete` - Tree delete operation
- `rust_root_hash` - Root hash computation

### TraitRegistry
UBT registers trait implementations for:
- `Hash` trait on node types
- Iterator traits for tree traversal

## Migration from Local Copy

The local `MInterpreter.v` and `StdlibHashMap.v` files are identical to the library.
They are kept for backward compatibility but should be considered deprecated.

To migrate existing code:
```coq
(* Old *)
Require Import UBT.Lib.MInterpreter.

(* New *)
Require Import RocqInterp.MInterpreter.
```

## Submodule Management

Update to latest library version:
```bash
cd formal/lib/rocq-of-rust-interp
git pull origin main
cd ../../..
git add formal/lib/rocq-of-rust-interp
git commit -m "Update rocq-of-rust-interp submodule"
```

Initialize submodule after clone:
```bash
git submodule update --init --recursive
```

## See Also

- [rocq-of-rust-interp](https://github.com/igor53627/rocq-of-rust-interp) - The general-purpose library
- [linking/interpreter.v](../linking/interpreter.v) - UBT-specific stepping implementation
- [Issue #60](https://github.com/igor53627/ubt-rs/issues/60) - Axiom reduction roadmap
