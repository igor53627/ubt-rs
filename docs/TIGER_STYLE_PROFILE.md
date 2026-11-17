# TigerStyle Profile

This file is the project profile that [TigerStyle](https://github.com/kvrail/tigerstyle/blob/main/TIGER_STYLE.md) requires ("Adopting the guide"). It states which rules of the guide are in force in this repository, the mechanism for each rule, the resource limits with their reactions, and the exceptions. Where this file and the guide disagree, this file wins for a project-profile rule or a local convention. A baseline requirement of the guide (limits, errors, security) is never waived here.

Scope: the library crate `ubt` (`src/`, without `src/bin/`). The `simulate` binary, `tests/`, `benches/` and `fuzz/` are test tooling. They follow the local conventions (function length, formatting). They do not follow the library rules on panics and integer casts.

## 1. What applies

| Block of the guide           | In force | Reason                                                                                                           |
|------------------------------|----------|------------------------------------------------------------------------------------------------------------------|
| Limits and errors            | Yes      | Common core                                                                                                      |
| Security: trust boundaries   | Yes      | The crate decodes bytes (`codec`), verifies proofs (`proof`) and takes entry streams and code                    |
| Security: limits as defense  | Yes      | Decoders and `dechunkify_code` take lengths and counts from the caller                                           |
| Security: memory, arithmetic | Yes      | Common core                                                                                                      |
| Security: supply chain       | Yes      | The crate has dependencies                                                                                       |
| Security: secrets            | No       | The crate handles no keys, passwords or tokens                                                                   |
| Security: cryptography       | Partly   | The crate calls hash functions through the `Hasher` trait. It has no encryption, no signatures and no randomness |
| Security: authority          | No       | A library with no files, no network and no privileges                                                            |
| Control flow                 | Yes      | The root computation is recursive                                                                                |
| Assertions                   | Yes      |                                                                                                                  |
| Memory                       | Yes      | "Where the runtime manages memory, budget it" (Rust ownership, heap collections)                                 |
| Concurrency                  | Yes      | The `parallel` feature hashes stems on rayon threads                                                             |
| Numbers                      | Yes      |                                                                                                                  |
| Performance                  | Partly   | No latency or throughput requirement is stated. "Let no showstopper through" holds                               |
| Dependencies and tooling     | Yes      |                                                                                                                  |
| Functions, naming, comments  | Yes      | Rust conventions first (`rustfmt`, the Rust API guidelines), then the guide                                      |

## 2. Profile decisions

| Topic            | Decision                                                                                                                                                                        | Reason                                                                                    |
|------------------|---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|-------------------------------------------------------------------------------------------|
| Memory           | The runtime manages memory. Collections grow with the data of the caller. A length or count that comes from outside is compared with a maximum before memory is reserved for it | A tree library cannot know the state size at startup                                      |
| Recursion        | Bounded recursion. Each recursive function carries `depth` and compares it with `MAX_DEPTH` (248) before each further call                                                      | The recursion follows the stem bits, and a stem has 248 bits                              |
| Concurrency      | Shared read-only state. Rayon closures borrow the tree immutably and return values. The single-threaded caller applies the results. No locks, no interior mutability            | The borrow checker then proves the absence of data races                                  |
| Assertions       | `assert!` only. `debug_assert!` and its variants are banned, because a default release build removes them. A failed assertion panics. The crate does not catch panics           | "Keep assertions on in production"                                                        |
| Failed assertion | The state of the tree is suspect after a panic. A caller that catches the panic must discard the tree and build it again from the stored values                                 | "Never continue on suspect state"                                                         |
| Boundary errors  | A function that takes bytes, proofs or entry streams from outside returns `Result<_, UbtError>`. It does not assert on that input                                               | "Return errors at the boundary; assert behind it"                                         |
| Panics           | No `unwrap`, `expect`, `panic!`, `todo!`, `unimplemented!` or `unreachable!` in library code outside tests                                                                      | A panic is reserved for a broken internal invariant, and `assert!` states the invariant   |
| Integers         | No `as` casts in library code. Use `From` for a lossless conversion and `TryFrom` for a conversion that can fail                                                                | "Convert platform-sized types such as `usize` with a checked cast"                        |
| Unsafe code      | Forbidden                                                                                                                                                                       | The crate has no need for it                                                              |
| Hash tables      | `std::collections::HashMap` and `HashSet` with the default `RandomState` (a keyed hash)                                                                                         | Stems come from outside. "Use keyed hashing for hash tables whose keys come from outside" |
| Dependencies     | Each dependency has a reason in section 6. `Cargo.lock` is committed. `cargo deny` runs in CI                                                                                   | "Own the exceptions"                                                                      |
| Second reviewer  | The repository has one maintainer. CodeRabbit reviews each pull request                                                                                                         | Recorded as an exception in section 7                                                     |

## 3. Limits and reactions

| Limit                         | Value and unit                                         | Scope                            | Checked                                                            | On excess                                            |
|-------------------------------|--------------------------------------------------------|----------------------------------|--------------------------------------------------------------------|------------------------------------------------------|
| Recursion depth               | 248 levels (`MAX_DEPTH`)                               | Per root computation             | Before each further call (`merkle.rs`, `tree/hash.rs`)             | `UbtError::TreeDepthExceeded`                        |
| Stem subtree                  | 256 leaves, 8 levels                                   | Per stem node                    | By the types: `SubIndex` is `u8`, the hash buffer is `[B256; 256]` | Cannot occur                                         |
| Encoded stem node             | 64 to 8256 bytes, equal to 64 + 32 x (set bitmap bits) | Per `decode_stem_node` call      | Before the values are read                                         | `UbtError::InvalidEncoding`                          |
| Encoded internal, leaf, empty | 65, 33 and 1 bytes, exact                              | Per decode call                  | Before the fields are read                                         | `UbtError::InvalidEncoding`                          |
| Proof stem siblings           | 8 hashes, exact                                        | Per `ProofNode::Stem`            | In `Proof::compute_root`, before the hashes are used               | `UbtError::InvalidProof`                             |
| Leading PUSHDATA count        | 31 bytes                                               | Per code chunk                   | Checked conversion in `chunkify_code`                              | The count is set to 31 (PUSH data covers the chunk)  |
| Reserved memory for code      | 31 bytes x (number of chunks)                          | Per `dechunkify_code` call       | Before the allocation; `code_size` is a claim of the caller        | The result has only the bytes that the chunks supply |
| Order of streamed entries     | Strictly ascending `(stem, subindex)`                  | Per `StreamingTreeBuilder` build | At each entry, in every build                                      | `UbtError::EntriesNotSorted`                         |
| Function length               | 70 lines                                               | Per function, all targets        | `clippy::too_many_lines`, in CI                                    | The build fails                                      |
| Line length                   | 100 columns                                            | Per line, all Rust files         | `rustfmt` (`max_width = 100`), in CI                               | `cargo fmt --check` fails (see 7)                    |

Resources with no limit in the crate:

| Resource                     | Owner of the bound | Note                                                                                                   |
|------------------------------|--------------------|--------------------------------------------------------------------------------------------------------|
| Number of stems and values   | The caller         | The tree holds all stems in memory. The caller decides how much state it loads                         |
| Entries of a streaming build | The caller         | `StreamingTreeBuilder` keeps the values of one stem and one hash for each stem                         |
| Hash caches                  | The tree           | `stem_hash_cache` has one entry for each stem. `node_hash_cache` has at most two entries for each stem |

## 4. Threat model

- **What the crate protects**: the root hash is a function of the tree contents only, and a verification result is true only for data that is in the tree.
- **Where trust changes hands**: `codec::decode_*` (bytes from storage or the network), `Proof::verify` and `Proof::compute_root` (a proof from an untrusted prover), `StreamingTreeBuilder` (an entry stream with a required order), `chunkify_code` and `dechunkify_code` (contract code and a claimed code size), and a `Hasher` or `NodeStore` implementation that the caller supplies.
- **What the attacker controls**: every byte that reaches a decoder, every field of a proof, and the keys and values that go into the tree. The attacker has the source code.
- **What the crate does not defend**: a `Hasher` or `NodeStore` implementation that breaks its documented contract; memory exhaustion by a caller that inserts without a bound; timing side channels (the tree holds public state).

## 5. Automated checks

| Rule                          | Check                                                                                                                 | Where it runs                       |
|-------------------------------|-----------------------------------------------------------------------------------------------------------------------|-------------------------------------|
| Formatting, 100 columns       | `cargo fmt --check`                                                                                                   | Rust CI                             |
| Function length, 70 lines     | `clippy.toml` `too-many-lines-threshold = 70` with `clippy::too_many_lines` (pedantic)                                | Rust CI, all targets                |
| No `debug_assert!`            | `clippy.toml` `disallowed-macros`                                                                                     | Rust CI, all targets                |
| No panic paths, no `as` casts | `src/lib.rs`: `clippy::unwrap_used`, `expect_used`, `panic`, `todo`, `unimplemented`, `unreachable`, `as_conversions` | Rust CI, library outside tests      |
| No unsafe code                | `src/lib.rs`: `#![forbid(unsafe_code)]`                                                                               | Every build                         |
| All warnings are errors       | `cargo clippy --all-targets --all-features -- -D warnings`, pedantic group on                                         | Rust CI                             |
| Every public item has docs    | `#![warn(missing_docs)]`                                                                                              | Rust CI                             |
| Dependencies                  | `cargo deny check`                                                                                                    | Rust CI (see 7)                     |
| Malformed input               | Unit tests of the decoders and the proof verifier; fuzz targets in `fuzz/`                                            | Rust CI; fuzzing on request (see 8) |
| Agreement with go-ethereum    | Root-hash vectors in `src/geth_compat.rs`                                                                             | Rust CI                             |

## 6. Dependencies

| Dependency         | Kind               | Reason                                                                    |
|--------------------|--------------------|---------------------------------------------------------------------------|
| `alloy-primitives` | Required           | `B256`, `Address` and `U256` are the types of the Ethereum Rust ecosystem |
| `sha2`             | Required           | SHA-256, the hash function of go-ethereum `trie/bintrie`                  |
| `blake3`           | Required           | BLAKE3, the default hasher of the crate                                   |
| `thiserror`        | Required           | `Display` and `Error` for `UbtError`                                      |
| `hex`              | Required           | `Debug` output of `Stem` and `TreeKey`                                    |
| `rayon`            | Feature `parallel` | Parallel stem hashing                                                     |
| `serde`            | Feature `serde`    | Serialization of keys and proofs                                          |
| `rand`, `num_cpus` | Feature `simulate` | The `simulate` binary only                                                |

## 7. Exceptions

| Exception                                     | Scope                                                              | Reason                                                            | Owner     |
|-----------------------------------------------|--------------------------------------------------------------------|-------------------------------------------------------------------|-----------|
| Lines longer than 100 columns                 | String literals, doc links and comments that `rustfmt` cannot wrap | `rustfmt` on the stable toolchain does not report them            | igor53627 |
| No second human reviewer                      | All pull requests                                                  | One maintainer. CodeRabbit reviews each pull request              | igor53627 |
| `cargo deny` does not fail the build          | `.github/workflows/rust.yml`                                       | `continue-on-error` because of an upstream CVSS 4.0 parse problem | igor53627 |
| Panics, `unwrap` and `as` casts are permitted | `tests/`, `benches/`, `fuzz/`, `src/bin/`, `#[cfg(test)]` modules  | Test tooling. A panic there is a test failure                     | igor53627 |

## 8. Open questions

- `Proof::verify` does not bind a proof to its key, and the proof path has no length limit ([#19](https://github.com/igor53627/ubt-rs/issues/19)). This is a baseline defect ("Carry no security debt"), not a profile choice.
- `clippy::arithmetic_side_effects` and `clippy::indexing_slicing` are not enforced. The library has 41 and 52 sites. Most of them index a fixed-size array with a value that the types bound (`[B256; 256]` with a `u8`).
- Fuzzing runs only on request (`.github/workflows/fuzz.yml`, `workflow_dispatch`). The guide asks for continuous fuzzing of every parser.
- The repository has no `SECURITY.md`, and private vulnerability reporting is off.
- `store_mut()` lets a caller change the store behind the hash caches ([#8](https://github.com/igor53627/ubt-rs/issues/8)).
- Incremental mode is slower than a full rebuild ([#6](https://github.com/igor53627/ubt-rs/issues/6)).
