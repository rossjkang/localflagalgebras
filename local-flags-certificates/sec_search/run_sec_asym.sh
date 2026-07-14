#!/usr/bin/env bash
# Asymmetric Faudree sweep: bipartite graphs with deg(X) = Δ_X,
# deg(Y) = Δ_Y where Δ_X < Δ_Y. Conjecture: χ'_s ≤ Δ_X · Δ_Y.
# Symmetric case Δ_X = Δ_Y is already covered (see run_d9_d16_v2.sh
# and run_d17_d20_resume.sh).
#
# Panel and rationale: the development notes
#
# Requires genbgL (MAXN1=30) and fast_check (EBS_WORDS=8, 512-bit).
# 30-min per-case strict cap; on TIMEOUT, skip remaining (larger)
# (n_X, n_Y) splits for that (Δ_X, Δ_Y) row.

set -u

NAUTY=/tmp/nauty2_8_8
TOOL=local-flags-certificates/sec_search/fast_check
PARSWEEP=local-flags-certificates/sec_search/parallel_sweep.sh
OUT=/tmp/sec_asym_results
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
    pkill -9 -f "/tmp/nauty2_8_8/genbgL" 2>/dev/null
    pkill -9 -f "fast_check " 2>/dev/null
    pkill -9 -f "parallel_sweep" 2>/dev/null
}
trap 'emergency_cleanup' EXIT INT TERM HUP

SUMMARY=$OUT/SUMMARY
: > $SUMMARY
echo "=== run_sec_asym.sh start $(date) ===" | tee -a $SUMMARY

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
            echo "  ${label}: TIMEOUT (>${TIMEOUT}s) — skip larger splits" | tee -a $SUMMARY
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

# run_asym_row Δ_X Δ_Y "nX1:nY1 nX2:nY2 ..."
run_asym_row() {
    local dx=$1 dy=$2; shift 2
    local pairs="$*"
    local bound=$(( dx * dy ))
    echo "" | tee -a $SUMMARY
    echo "===== Δ_X=$dx, Δ_Y=$dy (Faudree-asym ≤ $bound) =====" | tee -a $SUMMARY
    for p in $pairs; do
        local nx=${p%:*} ny=${p#*:}
        local m=$((dx * nx))
        local m_check=$((dy * ny))
        if [ $m -ne $m_check ]; then
            echo "  ${nx}x${ny}: INFEASIBLE (Δ_X·n_X=$m, Δ_Y·n_Y=$m_check) — skip" | tee -a $SUMMARY
            continue
        fi
        if [ $m -gt 512 ]; then
            echo "  ${nx}x${ny}: m=$m > 512 (tool cap) — skip" | tee -a $SUMMARY
            break
        fi
        local n12=$((nx + ny))
        if [ $n12 -gt 60 ]; then
            echo "  ${nx}x${ny}: n_X+n_Y=$n12 > 60 (genbgL cap) — skip" | tee -a $SUMMARY
            break
        fi
        local prefix=$OUT/asym_d${dx}_${dy}_n${nx}x${ny}
        local cmd="$PARSWEEP \"$NAUTY/genbgL -c -d${dx}:${dy} -D${dx}:${dy} ${nx} ${ny}\" $prefix $bound 8 > ${prefix}.log 2>&1"
        run_bounded "Δ=${dx}/${dy} ${nx}x${ny}" "$cmd" "${prefix}_w0.csv" "${prefix}.log" "genbgL -c -d${dx}:${dy}"
        rc=$?
        rm -f ${prefix}_w*.csv 2>/dev/null
        [ $rc -eq 124 ] && break
    done
}

# Panel (Δ_X < Δ_Y), with smallest few feasible (n_X, n_Y) splits per row.
# Feasibility: Δ_X·n_X = Δ_Y·n_Y. Smallest = K_{Δ_Y, Δ_X}.

# Δ_X = 2
run_asym_row 2 3 "3:2 6:4 9:6 12:8 15:10 18:12"
run_asym_row 2 4 "4:2 8:4 12:6 16:8 20:10 24:12"
run_asym_row 2 5 "5:2 10:4 15:6 20:8 25:10"

# Δ_X = 3
run_asym_row 3 4 "4:3 8:6 12:9 16:12 20:15 24:18"
run_asym_row 3 5 "5:3 10:6 15:9 20:12 25:15"
run_asym_row 3 6 "6:3 12:6 18:9 24:12"

# Δ_X = 4
run_asym_row 4 5 "5:4 10:8 15:12 20:16 25:20"
run_asym_row 4 6 "6:4 12:8 18:12 24:16"
run_asym_row 4 7 "7:4 14:8 21:12 28:16"

# Δ_X = 5
run_asym_row 5 6 "6:5 12:10 18:15 24:20"
run_asym_row 5 7 "7:5 14:10 21:15"
run_asym_row 5 8 "8:5 16:10 24:15"

# Δ_X = 6
run_asym_row 6 7 "7:6 14:12 21:18"
run_asym_row 6 8 "8:6 16:12 24:18"
run_asym_row 6 9 "9:6 18:12 27:18"

# Δ_X = 7
run_asym_row 7 8 "8:7 16:14 24:21"
run_asym_row 7 9 "9:7 18:14 27:21"

# Δ_X = 8
run_asym_row 8 9 "9:8 18:16 27:24"
run_asym_row 8 10 "10:8 20:16 30:24"

echo "" | tee -a $SUMMARY
echo "=== run_sec_asym.sh done $(date) ===" | tee -a $SUMMARY
