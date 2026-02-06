# UBT Integration Testing: Rust vs OCaml

This document describes the integration testing approach for comparing the Rust implementation against the OCaml extracted code from Rocq/Coq.

## Overview

The integration tests validate that structural tree operations (get, insert, delete) produce identical results in both implementations. Hash functions are explicitly excluded since:
- Rust uses Blake3
- OCaml extraction uses placeholder stubs

## Test Data Format

Test cases are defined in a simple text format:

```
# Comments start with #

TEST <test_name>
OP INSERT [stem_bytes] <subindex> [value_bytes]
OP DELETE [stem_bytes] <subindex>
QUERY [stem_bytes] <subindex>
EXPECT <None|Some([bytes])>
```

### Example

```
TEST single_insert_get
OP INSERT [1,2,3,4,5] 10 [42,43,44,45]
QUERY [1,2,3,4,5] 10
EXPECT Some([42,43,44,45,0,0,...])
```

## Results Format

Both Rust and OCaml output results in the same format:

```
# UBT <Language> Test Results

TEST <test_name>
RESULT stem=[bytes],subidx=<n> = <None|Some([bytes])>
```

## Running Tests

### Prerequisites

1. Rust toolchain
2. OCaml with `ocamlfind` and `str` library
3. Extracted OCaml code (`formal/extraction/extracted.ml`)

### Quick Run

```bash
./scripts/integration-test.sh
```

### Manual Steps

```bash
# 1. Export test data from Rust
UBT_TEST_DATA_PATH=target/test_data.txt \
UBT_RESULTS_PATH=target/rust_results.txt \
cargo test --test integration_export test_export_integration_data

# 2. Build OCaml runner
cd formal/extraction
ocamlfind ocamlopt -package str -linkpkg extracted.ml integration_runner.ml -o integration_runner

# 3. Run OCaml tests
./integration_runner < ../../target/test_data.txt > ../../target/ocaml_results.txt

# 4. Compare
diff target/rust_results.txt target/ocaml_results.txt
```

## Test Cases

| Test Name | Description |
|-----------|-------------|
| `empty_tree_get` | Get from empty tree returns None |
| `single_insert_get` | Insert then get same key |
| `get_different_stem` | Get non-existent stem returns None |
| `same_stem_different_subindex` | Different subindex returns None |
| `multiple_inserts_same_stem` | Multiple values in same subtree |
| `delete_removes_value` | Delete makes get return None |
| `insert_preserves_others` | Insert doesn't affect other keys |
| `overwrite_value` | Second insert overwrites first |
| `delete_nonexistent` | Delete non-existent doesn't affect others |
| `large_values` | Full 32-byte keys and values |

## Adding New Tests

1. Add test case to `tests/integration_export.rs` in `generate_test_cases()`
2. Run `./scripts/integration-test.sh` to verify

## CI Integration

Add to GitHub Actions workflow:

```yaml
integration-test:
  runs-on: ubuntu-latest
  steps:
    - uses: actions/checkout@v4
    - uses: dtolnay/rust-toolchain@stable
      with:
        toolchain: 1.85.0
    - uses: ocaml/setup-ocaml@v3
      with:
        ocaml-compiler: 5.1
    - run: opam install str
    - run: cd formal && make extract
    - run: ./scripts/integration-test.sh
```

## Limitations

1. **Hash Functions**: Not compared (different implementations)
2. **Root Hash**: Not compared (depends on hash function)
3. **Merkle Proofs**: Not compared (depends on hash function)
4. **Performance**: Not measured (focus is correctness)

## Architecture

```
                    +-------------------+
                    |  Test Generator   |
                    |  (Rust)           |
                    +--------+----------+
                             |
                             v
                    +-------------------+
                    |  test_data.txt    |
                    +--------+----------+
                             |
            +----------------+----------------+
            |                                 |
            v                                 v
    +---------------+                 +---------------+
    | Rust Runner   |                 | OCaml Runner  |
    | (tree.rs)     |                 | (Extracted)   |
    +-------+-------+                 +-------+-------+
            |                                 |
            v                                 v
    +---------------+                 +---------------+
    | rust_results  |                 | ocaml_results |
    +-------+-------+                 +-------+-------+
            |                                 |
            +----------------+----------------+
                             |
                             v
                    +-------------------+
                    |  Comparison       |
                    |  (diff)           |
                    +-------------------+
```
