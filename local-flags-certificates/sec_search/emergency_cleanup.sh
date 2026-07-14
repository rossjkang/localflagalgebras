#!/usr/bin/env bash
# Emergency cleanup: kill all SEC search processes regardless of who started them.
# Use after a SIGKILL'd master script left orphans (traps don't fire on SIGKILL).
#
# Safe to run when no sweep is active — just reports "nothing to do".

set -u

echo "=== emergency_cleanup.sh $(date) ==="
echo "BEFORE:"
ps aux | grep -iE "geng|genbg|fast_check|parallel_sweep|run_d9" \
       | grep -v grep | awk '{print "  ", $2, $11, $12, $13, $14}' | head -20

# Multiple specific patterns (avoid regex alternation issues on macOS pkill)
for pat in \
    "/tmp/nauty2_8_8/geng" \
    "/tmp/nauty2_8_8/genbg" \
    "fast_check " \
    "parallel_sweep.sh" \
    "run_d9_d16" \
    "run_d9_d16_v2"; do
    pkill -9 -f "$pat" 2>/dev/null
done

# Loop in case workers respawn on parent death (rare)
sleep 1
remaining=$(ps aux | grep -iE "geng|genbg|fast_check|parallel_sweep|run_d9" \
            | grep -v grep | wc -l | tr -d ' ')
if [ "$remaining" -gt 0 ]; then
    echo "Second pass needed; killing $remaining remaining..."
    for pat in \
        "/tmp/nauty2_8_8/geng" \
        "/tmp/nauty2_8_8/genbg" \
        "fast_check " \
        "parallel_sweep.sh" \
        "run_d9_d16"; do
        pkill -9 -f "$pat" 2>/dev/null
    done
    sleep 1
fi

echo ""
echo "AFTER:"
ps aux | grep -iE "geng|genbg|fast_check|parallel_sweep|run_d9" \
       | grep -v grep | awk '{print "  ", $2, $11, $12, $13, $14}' | head -5
remaining=$(ps aux | grep -iE "geng|genbg|fast_check|parallel_sweep|run_d9" \
            | grep -v grep | wc -l | tr -d ' ')
if [ "$remaining" -eq 0 ]; then
    echo "  (none — clean)"
fi
