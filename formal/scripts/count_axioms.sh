#!/bin/bash
# Count axioms and admits in Rocq/Coq proof files
# Output format suitable for CI comparison

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
FORMAL_DIR="$(dirname "$SCRIPT_DIR")"

cd "$FORMAL_DIR"

# Directories to scan (exclude src/ as it's auto-generated)
DIRS="specs simulations proofs linking"

echo "=== UBT Formal Verification Audit ==="
echo ""

# Count Admitted proofs
echo "--- Admitted Proofs ---"
ADMITTED_COUNT=0
for dir in $DIRS; do
    if [ -d "$dir" ]; then
        MATCHES=$(grep -rn 'Admitted\.' "$dir"/*.v 2>/dev/null || true)
        if [ -n "$MATCHES" ]; then
            echo "$MATCHES"
            COUNT=$(echo "$MATCHES" | wc -l)
            ADMITTED_COUNT=$((ADMITTED_COUNT + COUNT))
        fi
    fi
done
echo ""
echo "Total Admitted: $ADMITTED_COUNT"
echo ""

# Count Axiom declarations
echo "--- Axiom Declarations ---"
AXIOM_COUNT=0
for dir in $DIRS; do
    if [ -d "$dir" ]; then
        MATCHES=$(grep -rn '^Axiom\|^  Axiom' "$dir"/*.v 2>/dev/null || true)
        if [ -n "$MATCHES" ]; then
            echo "$MATCHES"
            COUNT=$(echo "$MATCHES" | wc -l)
            AXIOM_COUNT=$((AXIOM_COUNT + COUNT))
        fi
    fi
done
echo ""
echo "Total Axioms: $AXIOM_COUNT"
echo ""

# Count Parameter declarations (often used like axioms)
echo "--- Parameter Declarations ---"
PARAM_COUNT=0
for dir in $DIRS; do
    if [ -d "$dir" ]; then
        MATCHES=$(grep -rn '^Parameter\|^  Parameter' "$dir"/*.v 2>/dev/null || true)
        if [ -n "$MATCHES" ]; then
            echo "$MATCHES"
            COUNT=$(echo "$MATCHES" | wc -l)
            PARAM_COUNT=$((PARAM_COUNT + COUNT))
        fi
    fi
done
echo ""
echo "Total Parameters: $PARAM_COUNT"
echo ""

# Count admit tactics (lowercase, inside proofs)
echo "--- admit. Tactics ---"
ADMIT_COUNT=0
for dir in $DIRS; do
    if [ -d "$dir" ]; then
        MATCHES=$(grep -rn '\badmit\.' "$dir"/*.v 2>/dev/null || true)
        if [ -n "$MATCHES" ]; then
            echo "$MATCHES"
            COUNT=$(echo "$MATCHES" | wc -l)
            ADMIT_COUNT=$((ADMIT_COUNT + COUNT))
        fi
    fi
done
echo ""
echo "Total admit tactics: $ADMIT_COUNT"
echo ""

# Summary in machine-readable format
echo "=== Machine-Readable Summary ==="
echo "ADMITTED:$ADMITTED_COUNT"
echo "AXIOMS:$AXIOM_COUNT"
echo "PARAMETERS:$PARAM_COUNT"
echo "ADMITS:$ADMIT_COUNT"

# Categorize axioms by type
echo ""
echo "=== Axiom Categories ==="
echo ""

echo "Crypto axioms (hash functions):"
grep -rh 'Axiom.*hash\|Parameter.*hash' $DIRS/*.v 2>/dev/null | head -20 || echo "  (none)"

echo ""
echo "Type axioms (decidability, etc):"
grep -rh 'Axiom.*dec\|Axiom.*eq' $DIRS/*.v 2>/dev/null | head -20 || echo "  (none)"

echo ""
echo "=== End Audit ==="
