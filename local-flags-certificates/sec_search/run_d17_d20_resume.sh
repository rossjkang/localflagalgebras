#!/usr/bin/env bash
# Resume script for Δ=17..20 sweep, picking up after the kill at 2026-05-16 ~07:13 CEST.
#
# Already-completed cases (preserved in /tmp/d17to20_results/SUMMARY):
#   Δ=17 gen: n=18, n=20 done; n=22 TIMEOUT
#   Δ=18 gen: n=20, n=22 done; n=24 TIMEOUT
#   Δ=19 gen: n=20, n=22 done
# Skipped (n=22 timeout/skip already implied for Δ=17, n=24/26 for Δ=18).
#
# Bipartite previously used `genbg` (capped at n1+n2≤32), silently producing
# 0 graphs for ALL Δ≥17 cases. This script uses `genbgL` (MAXN1=30) instead.

set -u

NAUTY=/tmp/nauty2_8_8
TOOL=local-flags-certificates/sec_search/fast_check
PARSWEEP=local-flags-certificates/sec_search/parallel_sweep.sh
OUT=/tmp/d17to20_results
TIMEOUT=1800
mkdir -p $OUT

descendants() {
    local pid=$1 kids
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
    pkill -9 -f "/tmp/nauty2_8_8/geng" 2>/dev/null
    pkill -9 -f "/tmp/nauty2_8_8/genbgL" 2>/dev/null
    pkill -9 -f "fast_check " 2>/dev/null
    pkill -9 -f "parallel_sweep" 2>/dev/null
}
trap 'emergency_cleanup' EXIT INT TERM HUP

SUMMARY=$OUT/SUMMARY
echo "" | tee -a $SUMMARY
echo "=== run_d17_d20_resume.sh start $(date) ===" | tee -a $SUMMARY

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
            echo "  ${label}: TIMEOUT (>${TIMEOUT}s) — skip larger n" | tee -a $SUMMARY
            kill -TERM $pid 2>/dev/null; sleep 2
            kill -9 $pid 2>/dev/null
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

run_general_series() {
    local delta=$1; shift
    local ns="$*"
    local bound=$(( (delta * delta * 5 + 3) / 4 ))
    echo "" | tee -a $SUMMARY
    echo "===== Δ=$delta general (EN ≤ $bound) =====" | tee -a $SUMMARY
    for n in $ns; do
        local m=$((delta * n / 2))
        [ $m -gt 512 ] && { echo "  n=$n m=$m > 512 — skip" | tee -a $SUMMARY; break; }
        [ $n -le $delta ] && continue
        local prefix=$OUT/d${delta}_general_n${n}
        local cmd="$PARSWEEP \"$NAUTY/geng -d$delta -D$delta -c $n\" $prefix $bound 8 > ${prefix}.log 2>&1"
        run_bounded "Δ=$delta gen n=$n" "$cmd" "${prefix}_w0.csv" "${prefix}.log" "geng -d$delta"
        rc=$?
        rm -f ${prefix}_w*.csv 2>/dev/null
        [ $rc -eq 124 ] && break
    done
}

run_bipartite_series_L() {
    local delta=$1; shift
    local splits="$*"
    local fbound=$(( delta * delta ))
    echo "" | tee -a $SUMMARY
    echo "===== Δ=$delta bipartite (Faudree ≤ $fbound) [genbgL] =====" | tee -a $SUMMARY
    for n1 in $splits; do
        local m=$((delta * n1))
        [ $m -gt 512 ] && { echo "  ${n1}+${n1} m=$m > 512 — skip" | tee -a $SUMMARY; break; }
        local prefix=$OUT/d${delta}_bipartite_L_n${n1}${n1}
        local cmd="$PARSWEEP \"$NAUTY/genbgL -c -d$delta -D$delta $n1 $n1\" $prefix $fbound 8 > ${prefix}.log 2>&1"
        run_bounded "Δ=$delta bip ${n1}+${n1}" "$cmd" "${prefix}_w0.csv" "${prefix}.log" "genbgL -c -d$delta"
        rc=$?
        rm -f ${prefix}_w*.csv 2>/dev/null
        [ $rc -eq 124 ] && break
    done
}

# Bipartite redos (all previously broken).
run_bipartite_series_L 17 17 18 19 20
run_bipartite_series_L 18 18 19 20 21

# Δ=19 gen: resume from n=24.
run_general_series 19 24 26
run_bipartite_series_L 19 19 20 21 22

# Δ=20: not yet started.
run_general_series 20 22 24 26
run_bipartite_series_L 20 20 21 22 23

echo "" | tee -a $SUMMARY
echo "=== run_d17_d20_resume.sh done $(date) ===" | tee -a $SUMMARY
