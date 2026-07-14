#!/usr/bin/env bash
# Master sweep v2: stricter than v1, with full process-tree cleanup.
#
# Each case must FULLY COMPLETE in ≤ 30 min wall time. Timeouts are
# treated as "skip this and larger n", not "report partial".
#
# CAVEAT: Δ=16 EN bound is 320 but fast_check.c has 256-bit colour
# bitsets. Most small-n 16-regular graphs have χ'_s well below 256,
# so this is a non-issue in practice. A graph needing >256 colours
# would be flagged as "unresolved" and need SAT verification.

set -u

NAUTY=/tmp/nauty2_8_8
TOOL=local-flags-certificates/sec_search/fast_check
PARSWEEP=local-flags-certificates/sec_search/parallel_sweep.sh
OUT=/tmp/d9to16_results
TIMEOUT=1800   # 30 min per case strict cap (well under 1h)
mkdir -p $OUT

# ---- robust cleanup: kill entire descendant tree + any leftover workers ----
descendants() {
    local pid=$1
    local kids
    kids=$(pgrep -P $pid 2>/dev/null)
    for c in $kids; do
        descendants $c
        echo $c
    done
}
emergency_cleanup() {
    local kids
    kids=$(descendants $$ 2>/dev/null | tr '\n' ' ')
    [ -n "$kids" ] && kill -9 $kids 2>/dev/null
    # Belt-and-suspenders: catch any orphans by name
    pkill -9 -f "/tmp/nauty2_8_8/geng" 2>/dev/null
    pkill -9 -f "/tmp/nauty2_8_8/genbg" 2>/dev/null
    pkill -9 -f "fast_check " 2>/dev/null
    pkill -9 -f "parallel_sweep" 2>/dev/null
}
trap 'echo "  TRAP: cleaning up at $(date)" >&2; emergency_cleanup' EXIT INT TERM HUP

SUMMARY=$OUT/SUMMARY_v2
: > $SUMMARY
echo "=== run_d9_d16_v2.sh start $(date) (30-min cap, skip on timeout) ===" | tee -a $SUMMARY

run_bounded() {
    local label=$1 cmd=$2 csv=$3 log=$4 cleanup_pat=$5
    local start end elapsed
    start=$(date +%s)
    bash -c "$cmd" >/dev/null 2>&1 &
    local pid=$!
    while kill -0 $pid 2>/dev/null; do
        end=$(date +%s)
        elapsed=$((end - start))
        if [ $elapsed -gt $TIMEOUT ]; then
            echo "  ${label}: TIMEOUT (>${TIMEOUT}s) — discarding, skip larger n" | tee -a $SUMMARY
            kill -TERM $pid 2>/dev/null
            sleep 2
            kill -9 $pid 2>/dev/null
            # Per-pattern pkill: generator + consumer + orchestrator
            pkill -9 -f "$cleanup_pat" 2>/dev/null
            pkill -9 -f "fast_check " 2>/dev/null
            pkill -9 -f "parallel_sweep" 2>/dev/null
            sleep 2
            return 124
        fi
        sleep 5
    done
    wait $pid
    end=$(date +%s)
    elapsed=$((end - start))
    # Recover true total from log
    local total=0
    if [ -f "$log" ]; then
        total=$(grep -oE "total graphs: [0-9]+" "$log" | grep -oE '[0-9]+' | head -1)
        [ -z "$total" ] && total=0
    fi
    local cands=0
    if [ -f "$log" ]; then
        cands=$(grep -c "CANDIDATE COUNTEREXAMPLE" "$log" 2>/dev/null)
        [ -z "$cands" ] && cands=0
    fi
    echo "  ${label}: ${total} graphs, ${cands} cands, ${elapsed}s" | tee -a $SUMMARY
    return 0
}

# Run a sequence of n values, stopping at first timeout
run_general_series() {
    local delta=$1; shift
    local ns="$*"
    local bound=$(( (delta * delta * 5 + 3) / 4 ))
    echo "" | tee -a $SUMMARY
    echo "===== Δ=$delta general (EN ≤ $bound) =====" | tee -a $SUMMARY
    for n in $ns; do
        local m=$((delta * n / 2))
        [ $m -gt 256 ] && { echo "  n=$n m=$m > 256 — skip" | tee -a $SUMMARY; break; }
        [ $n -le $delta ] && continue
        local prefix=$OUT/d${delta}_general_v2_n${n}
        local cmd="$PARSWEEP \"$NAUTY/geng -d$delta -D$delta -c $n\" $prefix $bound 8 > ${prefix}.log 2>&1"
        run_bounded "Δ=$delta gen n=$n" "$cmd" "${prefix}_w0.csv" "${prefix}.log" "geng -d$delta"
        rc=$?
        rm -f ${prefix}_w*.csv 2>/dev/null
        [ $rc -eq 124 ] && break
    done
}
run_bipartite_series() {
    local delta=$1; shift
    local splits="$*"
    local fbound=$(( delta * delta ))
    echo "" | tee -a $SUMMARY
    echo "===== Δ=$delta bipartite (Faudree ≤ $fbound) =====" | tee -a $SUMMARY
    for n1 in $splits; do
        local m=$((delta * n1))
        [ $m -gt 256 ] && { echo "  ${n1}+${n1} m=$m > 256 — skip" | tee -a $SUMMARY; break; }
        local prefix=$OUT/d${delta}_bipartite_v2_n${n1}${n1}
        local cmd="$PARSWEEP \"$NAUTY/genbg -c -d$delta -D$delta $n1 $n1\" $prefix $fbound 8 > ${prefix}.log 2>&1"
        run_bounded "Δ=$delta bip ${n1}+${n1}" "$cmd" "${prefix}_w0.csv" "${prefix}.log" "genbg -c -d$delta"
        rc=$?
        rm -f ${prefix}_w*.csv 2>/dev/null
        [ $rc -eq 124 ] && break
    done
}

# Δ=9: Conservative — exclude n=16 general (was 50min timeout) and
# 13+13 bipartite (also 50min timeout)
run_general_series 9 10 12 14
run_bipartite_series 9 9 10 11 12

# Δ=10: skip n=16 general and 14+14 bipartite (both 50-min timeouts)
run_general_series 10 12 14
run_bipartite_series 10 10 11 12 13

# Δ=11: gen n=16 was 270s ✓. Try n=18 (was timeout in v1)? Skip.
run_general_series 11 12 14 16
run_bipartite_series 11 11 12 13

# Δ=12: untried. Try modest n.
run_general_series 12 14 16
run_bipartite_series 12 12 13 14

# Δ=13: untried.
run_general_series 13 14 16
run_bipartite_series 13 13 14

# Δ=14: untried; general needs n ≥ 16.
run_general_series 14 16 18
run_bipartite_series 14 14 15

# Δ=15
run_general_series 15 16 18
run_bipartite_series 15 15 16

# Δ=16: K_{16,16} is the only bipartite that fits.
run_general_series 16 18 20
run_bipartite_series 16 16

echo "" | tee -a $SUMMARY
echo "=== run_d9_d16_v2.sh done $(date) ===" | tee -a $SUMMARY
