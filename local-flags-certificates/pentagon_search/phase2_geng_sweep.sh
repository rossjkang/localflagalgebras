#!/usr/bin/env bash
# Phase 2 — geng enumeration sweep over (Delta, n) slices.
#
# For each (Delta, n) pair below, runs
#   geng -t -c -d{D} -D{D} {n}
# and pipes through pentagon_counter.py to compute the max ratio
#     P(G) / (|G| * Delta^4).
#
# Slice sizes were probed first; this script restricts to slices
# that fit in a 1-hour wall-clock budget per slice.
#
# Special focus: (Delta=5, n=16) — the Clebsch slice. Confirm or refute
# Clebsch's 12/625 = 0.01920 as the exhaustive maximum.
#
# Probed slice sizes (geng -t -c -dD -DD -u n):
#   D=3 n=10..30: 6, 22, 110, 792, 7805, 97546, ... [grows ~10x per 2n]
#   D=4 n=10,12,14,16,18: 2, 12, 220, 16828, ~big (>50k)
#   D=5 n=12,14,16: small..388
#   D=6,7: enumerable at small n

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
GENG="${GENG:-geng}"
COUNTER="${COUNTER:-$SCRIPT_DIR/pentagon_counter.py}"
LOGDIR="$SCRIPT_DIR/phase2_logs"
RESULTS="$SCRIPT_DIR/phase2_results.tsv"
mkdir -p "$LOGDIR"

if [[ ! -x "$GENG" ]]; then
    echo "ERROR: geng binary not found at $GENG" >&2
    exit 1
fi

# Header
{
    printf "Delta\tn\tnum_graphs\tmax_P\tmax_ratio_num\tmax_ratio_den\tmax_ratio_float\tmax_g6\tmax_girth\twall_sec\n"
} > "$RESULTS"

run_slice() {
    local D=$1 n=$2
    local label="d${D}_n${n}"
    local logfile="$LOGDIR/${label}.log"
    local t0=$(python3 -c "import time; print(time.time())")

    # geng -t -c -d{D} -D{D}: triangle-free, connected, min/max degree = D.
    # Pipe g6 lines into pentagon_counter.py.
    local out
    out=$("$GENG" -t -c -d"$D" -D"$D" "$n" 2>/dev/null | \
        python3 "$COUNTER" --label "$label" --verbose --top-k 10 2> "$logfile")
    local t1=$(python3 -c "import time; print(time.time())")
    local wall=$(python3 -c "print(f'{$t1 - $t0:.2f}')")

    local count=$(echo "$out" | sed -n 's/.*count=\([0-9]*\).*/\1/p')
    local maxP=$(echo "$out" | sed -n 's/.*max_P=\([0-9]*\).*/\1/p')
    local rn=$(echo "$out" | sed -n 's/.*max_ratio_num=\([0-9]*\).*/\1/p')
    local rd=$(echo "$out" | sed -n 's/.*max_ratio_den=\([0-9]*\).*/\1/p')
    local g6=$(echo "$out" | sed -n 's/.*max_g6=\([^ ]*\).*/\1/p')
    local girth=$(echo "$out" | sed -n 's/.*max_girth=\([0-9]*\).*/\1/p')
    local rfloat
    if [[ -z "$rd" || "$rd" == "0" ]]; then
        rfloat="0.000000"
    else
        rfloat=$(python3 -c "print(f'{$rn / $rd:.6f}')" 2>/dev/null || echo "0.000000")
    fi

    printf "%d\t%d\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n" \
        "$D" "$n" "$count" "$maxP" "$rn" "$rd" "$rfloat" "$g6" "$girth" "$wall" \
        >> "$RESULTS"

    printf "  D=%d n=%-3d count=%-7s max_P=%-6s ratio=%-7s=%s g6=%-22s girth=%s wall=%ss\n" \
        "$D" "$n" "$count" "$maxP" "${rn}/${rd}" "$rfloat" "$g6" "$girth" "$wall"
}

echo "# Phase 2 — geng enumeration sweep"
echo "# Started: $(date)"
echo "# Results -> $RESULTS"
echo

# --- Delta = 3 : cubic TF, n=10..22 ---
# Slice sizes: 6, 22, 110, 792, 7805, 97546, ~1.7M (extrapolated)
# n=20 takes ~46s for raw enumeration; n=22 is ~1.7M graphs ~ 15min counter
echo "## Delta = 3 (cubic TF, connected)"
for n in 10 12 14 16 18 20 22; do
    run_slice 3 "$n"
done
echo

# --- Delta = 4 : n=10..16, then targeted small ---
# Slice sizes: 2, 12, 220, 16828, big at 18
echo "## Delta = 4"
for n in 10 12 14 16; do
    run_slice 4 "$n"
done
# n=18 may be 50k+; let it run if time permits
run_slice 4 18
echo

# --- Delta = 5 : n=12..20 (n=16 is Clebsch slice — PRIMARY TARGET) ---
echo "## Delta = 5 (n=16 is Clebsch slice)"
for n in 12 14 16 18; do
    run_slice 5 "$n"
done
# n=20: explore — Clebsch beater?
run_slice 5 20
echo

# --- Delta = 6 : n=14..20 ---
echo "## Delta = 6"
for n in 14 16 18 20; do
    run_slice 6 "$n"
done
echo

# --- Delta = 7 : n=16..20 ---
echo "## Delta = 7"
for n in 16 18 20; do
    run_slice 7 "$n"
done
echo

echo "# Finished: $(date)"
echo "# Full TSV: $RESULTS"
