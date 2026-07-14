#!/usr/bin/env bash
# Master sweep for Δ=9..16, both general and bipartite,
# per-case wall-time budget of 50 minutes.
#
# For each (Δ, type), tries increasing n; records the largest n that
# completes within budget. Skips n where m > 256 (tool capacity).

set -u

NAUTY=/tmp/nauty2_8_8
TOOL=local-flags-certificates/sec_search/fast_check
PARSWEEP=local-flags-certificates/sec_search/parallel_sweep.sh
OUT=/tmp/d9to16_results
TIMEOUT=3000   # 50 min per case
mkdir -p $OUT

SUMMARY=$OUT/SUMMARY
: > $SUMMARY
echo "=== run_d9_d16.sh start $(date) ===" | tee -a $SUMMARY

# Run cmd with a wall timeout, kill on overrun.
# $1 = label, $2 = cmd, $3 = csv path, $4 = log path
# $5 = bound (for SAT-pipeline cleanup pattern)
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
            echo "  ${label}: TIMEOUT at ${elapsed}s — killing" | tee -a $SUMMARY
            kill -TERM $pid 2>/dev/null
            sleep 2
            kill -9 $pid 2>/dev/null
            pkill -9 -f "$cleanup_pat" 2>/dev/null
            sleep 2
            local g=0
            if [ -f "$csv" ]; then g=$(($(wc -l < "$csv") - 1)); fi
            echo "  ${label}: partial $g graphs" | tee -a $SUMMARY
            return 124
        fi
        sleep 10
    done
    wait $pid
    end=$(date +%s)
    elapsed=$((end - start))
    local g=0 cands=0
    if [ -f "$csv" ]; then g=$(($(wc -l < "$csv") - 1)); fi
    if [ -f "$log" ]; then
        cands=$(grep -c "CANDIDATE COUNTEREXAMPLE" "$log" 2>/dev/null)
        [ -z "$cands" ] && cands=0
    fi
    echo "  ${label}: $g graphs, $cands cands, ${elapsed}s" | tee -a $SUMMARY
    return 0
}

# Pick n-list for Δ-regular general (n even if Δ odd, n ≥ Δ+1, m ≤ 256).
ns_general() {
    local d=$1
    local ns=""
    local parity=$((d % 2))
    for n in 10 12 14 16 18 20 22 24; do
        [ $n -le $d ] && continue
        [ $parity -eq 1 ] && [ $((n % 2)) -ne 0 ] && continue
        local m=$((d * n / 2))
        [ $m -gt 256 ] && break
        ns="$ns $n"
    done
    echo "$ns"
}

# For bipartite Δ=d, try splits d+d, (d+1)+(d+1), ..., up to m ≤ 256.
splits_bipartite() {
    local d=$1
    local splits=""
    for n1 in $d $((d+1)) $((d+2)) $((d+3)) $((d+4)) $((d+5)); do
        local m=$((d * n1))
        [ $m -gt 256 ] && break
        splits="$splits $n1"
    done
    echo "$splits"
}

en_bound() { echo $(( ($1 * $1 * 5 + 3) / 4 )); }  # ceil(1.25·Δ²)

for delta in 9 10 11 12 13 14 15 16; do
    bound=$(en_bound $delta)
    echo "" | tee -a $SUMMARY
    echo "===== Δ=$delta general (EN ≤ $bound) =====" | tee -a $SUMMARY
    for n in $(ns_general $delta); do
        CSV=$OUT/d${delta}_general_n${n}.csv
        LOG=$OUT/d${delta}_general_n${n}.log
        cmd="$PARSWEEP \"$NAUTY/geng -d$delta -D$delta -c $n\" $OUT/d${delta}_general_n${n} $bound 8 > $LOG 2>&1"
        run_bounded "Δ=$delta gen n=$n" "$cmd" "$OUT/d${delta}_general_n${n}_w0.csv" "$LOG" "geng -d$delta"
        rc=$?
        # Clean up the big CSVs to save disk
        rm -f $OUT/d${delta}_general_n${n}_w*.csv 2>/dev/null
        [ $rc -eq 124 ] && break
    done

    fbound=$(( delta * delta ))
    echo "===== Δ=$delta bipartite (Faudree ≤ $fbound) =====" | tee -a $SUMMARY
    for n1 in $(splits_bipartite $delta); do
        CSV=$OUT/d${delta}_bipartite_n${n1}${n1}_w0.csv
        LOG=$OUT/d${delta}_bipartite_n${n1}${n1}.log
        cmd="$PARSWEEP \"$NAUTY/genbg -c -d$delta -D$delta $n1 $n1\" $OUT/d${delta}_bipartite_n${n1}${n1} $fbound 8 > $LOG 2>&1"
        run_bounded "Δ=$delta bip ${n1}+${n1}" "$cmd" "$CSV" "$LOG" "genbg -c -d$delta"
        rc=$?
        rm -f $OUT/d${delta}_bipartite_n${n1}${n1}_w*.csv 2>/dev/null
        [ $rc -eq 124 ] && break
    done
done

echo "" | tee -a $SUMMARY
echo "=== run_d9_d16.sh done $(date) ===" | tee -a $SUMMARY
