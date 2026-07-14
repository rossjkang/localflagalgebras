#!/usr/bin/env bash
# Single-row asymmetric sweep — extracted from run_sec_asym_resume.sh.
# Usage: run_one_row.sh <Δ_X> <Δ_Y> "split1 split2 ..."
# Writes results to /tmp/sec_asym_one_row/{SUMMARY,*.log,*.csv}

set -u

if [ $# -lt 3 ]; then
    echo "usage: $0 <dx> <dy> \"n1x:n1y n2x:n2y ...\"" >&2
    exit 64
fi

DX=$1
DY=$2
SPLITS=$3

NAUTY=/tmp/nauty2_8_8
TOOL=local-flags-certificates/sec_search/fast_check
PARSWEEP=local-flags-certificates/sec_search/parallel_sweep.sh
OUT=/tmp/sec_asym_one_row
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
echo "=== run_one_row.sh Δ_X=$DX Δ_Y=$DY start $(date) ===" | tee -a $SUMMARY

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
            return 124
        fi
        sleep 5
    done
    wait $pid
    end=$(date +%s)
    elapsed=$((end - start))
    local count=0
    [ -f "$csv" ] && count=$(wc -l < "$csv" | tr -d ' ')
    local total
    total=$(grep -oE "[0-9]+ graphs" "$log" 2>/dev/null | tail -1 | awk '{print $1}')
    : ${total:=?}
    echo "  ${label}: graphs=${total} candidates=${count} ${elapsed}s" | tee -a $SUMMARY
    return 0
}

run_asym_row() {
    local dx=$1 dy=$2; shift 2
    local splits="$@"
    local bound=$((dx*dy))
    echo "===== Δ_X=$dx, Δ_Y=$dy (Faudree-asym ≤ $bound) =====" | tee -a $SUMMARY
    for split in $splits; do
        local nx=${split%:*} ny=${split##*:}
        local m=$((dx*nx)) m_check=$((dy*ny))
        if [ $m -ne $m_check ]; then
            echo "  ${nx}x${ny}: INFEASIBLE (Δ_X·n_X=$m, Δ_Y·n_Y=$m_check) — skip" | tee -a $SUMMARY
            continue
        fi
        local m=$((dx*nx))
        if [ $m -gt 512 ]; then
            echo "  ${nx}x${ny}: m=$m > 512 (tool cap) — skip" | tee -a $SUMMARY
            break
        fi
        if [ $nx -gt 30 ]; then
            echo "  ${nx}x${ny}: n_X=$nx > 30 (genbgL MAXN1 cap) — skip" | tee -a $SUMMARY
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

run_asym_row $DX $DY "$SPLITS"

echo "" | tee -a $SUMMARY
echo "=== run_one_row.sh done $(date) ===" | tee -a $SUMMARY
