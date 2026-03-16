#!/usr/bin/env bash

# Test script for Vera examples
# Runs equivalence checking on all pairs of .sv files within each examples/ subdirectory

set -euo pipefail

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Solver to use (default: cvc5)
SOLVER="${VERA_SOLVER:-cvc5}"

# Number of parallel jobs (default: number of CPUs)
JOBS="${VERA_JOBS:-0}"  # 0 means use all CPUs in parallel

# Temporary directory for test results
TEMP_DIR=$(mktemp -d)
trap 'rm -rf "$TEMP_DIR"' EXIT

# Get the script directory and project root
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$SCRIPT_DIR"

echo "Testing Vera examples with solver: $SOLVER"
echo "========================================"
echo

# Find all directories containing .sv files (at any depth)
mapfile -t all_dirs < <(find . -name "*.sv" -exec dirname {} \; | sort -u)

# Collect all test pairs and write to a file
test_pairs_file="$TEMP_DIR/test_pairs.txt"
> "$test_pairs_file"

for dir in "${all_dirs[@]}"; do
    [ -d "$dir" ] || continue

    # Get all .sv files in this specific directory only
    mapfile -t files < <(find "$dir" -maxdepth 1 -name "*.sv" | sort)

    # Skip if fewer than 2 files
    [ ${#files[@]} -lt 2 ] && continue

    # Generate all pairs (i, j) where i < j
    for ((i=0; i<${#files[@]}; i++)); do
        for ((j=i+1; j<${#files[@]}; j++)); do
            echo "${files[$i]}|${files[$j]}" >> "$test_pairs_file"
        done
    done
done

total_tests=$(wc -l < "$test_pairs_file")
echo "Found $total_tests test pairs"
echo

dune build
VERA="$PROJECT_ROOT/_build/default/bin/main.exe"
export VERA SOLVER SCRIPT_DIR RED GREEN YELLOW NC

vera_compare() {
    local in1=$(realpath "$1")
    local in2=$(realpath "$2")
    local label1="${in1#"$SCRIPT_DIR/"}"
    local label2="${in2#"$SCRIPT_DIR/"}"
    # Vera creates a temp file in CWD for the SMT query. If we don't
    # go into the tempdir then these files will clobber each other.
    cd $(mktemp -d)
    local output=$("$VERA" compare --solver="$SOLVER" "$in1" "$in2" 2>&1)
    case "$output" in
        *"Equivalent (UNSAT)"*) echo -e "${GREEN}PASS${NC}: $label1 vs $label2" ;;
        *"Non-equivalent (SAT)"*) echo -e "${RED}FAIL${NC}: $label1 vs $label2" ;;
        *) echo -e "${RED}ERROR${NC}: $label1 vs $label2:\n$output" ;;
    esac
}
export -f vera_compare

parallel --colsep '\|' \
	 -j "$JOBS" \
	 --halt soon,fail=1 \
	 vera_compare < "$test_pairs_file"
