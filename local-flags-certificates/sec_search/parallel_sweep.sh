#!/usr/bin/env bash
# Parallel sweep using nauty's residue-class enumeration split.
#
# Usage:
#   parallel_sweep.sh <gen-cmd> <output-prefix> <bound> [n-workers]
#
# <gen-cmd> is something like:
#   "geng -d4 -D4 -c 16"
#   "genbg -c -d4 -D4 11 11"
# We append " <i>/<N>" to each worker's invocation.
#
# Example:
#   parallel_sweep.sh "/tmp/nauty2_8_8/geng -d4 -D4 -c 16" /tmp/par_n16 20 8
#   parallel_sweep.sh "/tmp/nauty2_8_8/genbg -c -d4 -D4 11 11" /tmp/par_bip22 16 8

set -euo pipefail

if [ $# -lt 3 ]; then
    echo "Usage: $0 <gen-cmd> <output-prefix> <bound> [n-workers]" >&2
    exit 1
fi

GEN_CMD=$1
PREFIX=$2
BOUND=$3
N=${4:-8}

SWEEP_PY=local-flags-certificates/sec_search/sweep.py
SWEEP_C=local-flags-certificates/sec_search/fast_check

# Pick C consumer if available (much faster), else Python fast path.
if [ -x "$SWEEP_C" ]; then
    USE_C=1
    echo "  consumer: C fast_check (-O3 DSATUR + bitset L²)" >&2
else
    USE_C=0
    SWEEP_FLAGS="--fast --csv --bound $BOUND --every 500000 --exact-on-counterexample"
    case "$GEN_CMD" in
        *genbg*) SWEEP_FLAGS="$SWEEP_FLAGS --bipartite" ;;
    esac
    echo "  consumer: Python sweep.py --fast" >&2
fi

START=$(date +%s)
echo "=== parallel_sweep.sh ===" >&2
echo "  gen:    $GEN_CMD <res>/$N" >&2
echo "  prefix: $PREFIX" >&2
echo "  bound:  $BOUND" >&2
echo "  N:      $N workers" >&2

# Launch N workers in parallel
PIDS=()
for i in $(seq 0 $((N-1))); do
    if [ "$USE_C" -eq 1 ]; then
        (
            $GEN_CMD $i/$N 2>/dev/null \
                | "$SWEEP_C" "$BOUND" --csv --every 500000 \
                > "${PREFIX}_w${i}.csv" 2> "${PREFIX}_w${i}.log"
            echo "WORKER $i DONE $(date +%s)" >> "${PREFIX}_w${i}.log"
        ) &
    else
        (
            $GEN_CMD $i/$N 2>/dev/null \
                | python3 -u "$SWEEP_PY" $SWEEP_FLAGS \
                > "${PREFIX}_w${i}.csv" 2> "${PREFIX}_w${i}.log"
            echo "WORKER $i DONE $(date +%s)" >> "${PREFIX}_w${i}.log"
        ) &
    fi
    PIDS+=($!)
done
echo "  launched workers ${PIDS[*]}" >&2

# Wait for all
for pid in "${PIDS[@]}"; do
    wait "$pid"
done
END=$(date +%s)
ELAPSED=$((END - START))

# Aggregate
TOTAL_GRAPHS=0
TOTAL_CANDS=0
for i in $(seq 0 $((N-1))); do
    g=$(wc -l < "${PREFIX}_w${i}.csv")
    g=$((g - 1))
    c=$(grep -c "CANDIDATE COUNTEREXAMPLE" "${PREFIX}_w${i}.log" 2>/dev/null) || c=0
    TOTAL_GRAPHS=$((TOTAL_GRAPHS + g))
    TOTAL_CANDS=$((TOTAL_CANDS + c))
done

echo "" >&2
echo "=== aggregate ===" >&2
echo "  total graphs: $TOTAL_GRAPHS" >&2
echo "  total candidates: $TOTAL_CANDS" >&2
echo "  wall time:    ${ELAPSED}s" >&2
echo "  rate:         $((TOTAL_GRAPHS / (ELAPSED > 0 ? ELAPSED : 1))) g/s" >&2
if [ "$TOTAL_CANDS" -eq 0 ]; then
    echo "  RESULT: NO counterexamples found (all χ'_s ≤ $BOUND)" >&2
else
    echo "  RESULT: $TOTAL_CANDS CANDIDATE COUNTEREXAMPLES" >&2
    for i in $(seq 0 $((N-1))); do
        grep "CANDIDATE COUNTEREXAMPLE" "${PREFIX}_w${i}.log" 2>/dev/null || true
    done
fi
