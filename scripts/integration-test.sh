#!/bin/bash
# UBT Integration Test: Rust vs OCaml Comparison
#
# This script runs the same test cases on both Rust and OCaml implementations
# and compares the structural operation results (get, insert, delete).
# Hash functions are excluded from comparison since Rust uses Blake3
# and OCaml uses placeholder stubs.
#
# Usage:
#   ./scripts/integration-test.sh          # Auto-detect (local or remote)
#   ./scripts/integration-test.sh local    # Force local OCaml
#   ./scripts/integration-test.sh remote   # Force remote OCaml (ubuntu-64@orb)

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
cd "$PROJECT_ROOT"

# Determine if we should use remote or local OCaml
USE_REMOTE="${1:-auto}"
if [ "$USE_REMOTE" = "auto" ]; then
    if command -v ocamlopt &> /dev/null; then
        USE_REMOTE="local"
    else
        USE_REMOTE="remote"
    fi
fi

REMOTE_HOST="${REMOTE_HOST:-ubuntu-64@orb}"
REMOTE_PATH="${REMOTE_PATH:-~/ubt-rs}"

# Output directories
mkdir -p target/integration

TEST_DATA="target/integration/test_data.txt"
RUST_RESULTS="target/integration/rust_results.txt"
OCAML_RESULTS="target/integration/ocaml_results.txt"
COMPARISON="target/integration/comparison.txt"

echo "=== UBT Integration Test ==="
echo "Mode: $USE_REMOTE"
echo ""

# Step 1: Generate test data and run Rust tests
echo "[1/4] Running Rust tests and exporting data..."
UBT_TEST_DATA_PATH="$TEST_DATA" \
UBT_RESULTS_PATH="$RUST_RESULTS" \
cargo test --test integration_export test_export_integration_data -- --nocapture 2>/dev/null

if [ ! -f "$RUST_RESULTS" ]; then
    echo "[FAIL] Rust test export failed"
    exit 1
fi
echo "  --> Rust results: $RUST_RESULTS"

# Step 2: Build and run OCaml test runner
echo ""
echo "[2/4] Building OCaml integration runner..."

if [ "$USE_REMOTE" = "remote" ]; then
    # Sync to remote (include target/integration for test data)
    echo "  Syncing to remote: $REMOTE_HOST"
    rsync -az \
        --exclude '.git/' \
        --exclude 'target/debug/' \
        --exclude 'target/release/' \
        --exclude '*.vo' \
        --exclude '*.vok' \
        --exclude '*.vos' \
        --exclude '*.glob' \
        . "$REMOTE_HOST:$REMOTE_PATH/" > /dev/null

    # Build and run on remote
    echo "  Building on remote..."
    ssh "$REMOTE_HOST" "cd $REMOTE_PATH/formal/extraction && \
        if [ -f extracted.ml ]; then \
            echo '  Using extracted.ml from Rocq extraction'; \
            ocamlopt -I +str str.cmxa extracted.ml integration_runner.ml -o integration_runner; \
        else \
            echo '  [!] extracted.ml not found, using standalone version'; \
            ocamlopt -I +str str.cmxa integration_runner_standalone.ml -o integration_runner; \
        fi" || {
        echo "[FAIL] Remote OCaml build failed"
        exit 1
    }

    # Run on remote and copy results
    echo ""
    echo "[3/4] Running OCaml tests on remote..."
    ssh "$REMOTE_HOST" "cd $REMOTE_PATH && formal/extraction/integration_runner < $TEST_DATA" > "$OCAML_RESULTS"
else
    # Local build
    cd formal/extraction

    # Try to use extracted.ml if available, otherwise use standalone version
    if [ -f "extracted.ml" ]; then
        echo "  Using extracted.ml from Rocq extraction"
        RUNNER_SRC="integration_runner.ml"
        DEPS="extracted.ml"
    else
        echo "  [!] extracted.ml not found, using standalone version"
        RUNNER_SRC="integration_runner_standalone.ml"
        DEPS=""
    fi

    # Build the integration runner
    # Uses str library for regex parsing
    if [ -n "$DEPS" ]; then
        ocamlfind ocamlopt -package str -linkpkg $DEPS $RUNNER_SRC -o integration_runner 2>/dev/null || \
        ocamlopt str.cmxa $DEPS $RUNNER_SRC -o integration_runner 2>/dev/null || {
            echo "[FAIL] OCaml build failed"
            exit 1
        }
    else
        ocamlfind ocamlopt -package str -linkpkg $RUNNER_SRC -o integration_runner 2>/dev/null || \
        ocamlopt str.cmxa $RUNNER_SRC -o integration_runner 2>/dev/null || {
            echo "[FAIL] OCaml build failed"
            exit 1
        }
    fi
    echo "  --> Built: integration_runner"

    cd "$PROJECT_ROOT"

    # Step 3: Run OCaml tests
    echo ""
    echo "[3/4] Running OCaml tests..."
    formal/extraction/integration_runner < "$TEST_DATA" > "$OCAML_RESULTS"
fi

echo "  --> OCaml results: $OCAML_RESULTS"

# Step 4: Compare results
echo ""
echo "[4/4] Comparing results..."

# Normalize results for comparison (remove comments, normalize whitespace)
normalize_results() {
    grep -v "^#" "$1" | grep -v "^$" | sort
}

RUST_NORMALIZED=$(normalize_results "$RUST_RESULTS")
OCAML_NORMALIZED=$(normalize_results "$OCAML_RESULTS")

if [ "$RUST_NORMALIZED" = "$OCAML_NORMALIZED" ]; then
    echo ""
    echo "========================================"
    echo "[PASS] All results match!"
    echo "========================================"
    echo ""
    echo "Rust and OCaml implementations produce identical results"
    echo "for structural operations (get, insert, delete)."
    exit 0
else
    echo ""
    echo "========================================"
    echo "[FAIL] Results differ!"
    echo "========================================"
    echo ""
    
    # Show diff
    echo "Differences:"
    diff -u <(normalize_results "$RUST_RESULTS") <(normalize_results "$OCAML_RESULTS") > "$COMPARISON" || true
    cat "$COMPARISON"
    
    echo ""
    echo "Full comparison saved to: $COMPARISON"
    exit 1
fi
