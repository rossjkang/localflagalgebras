#!/usr/bin/env python3
"""Sweep χ'_s over a stream of graph6-encoded graphs from stdin.

Reads each graph6 line, computes χ'_s via SAT, emits CSV.
Reports graphs whose χ'_s exceeds a target bound (for counterexample search).

Usage:
  ./geng -d4 -D4 -c 10 | python3 sweep.py --bound 20 > out.csv
  ./genbg 5 5 -d4 -D4 -c | python3 sweep.py --bipartite --bound 16 > out_bip.csv
"""

import argparse
import sys
import time
from pathlib import Path

import networkx as nx

sys.path.insert(0, str(Path(__file__).resolve().parent))
from compute_chi_s import (chi_s, strong_adjacency_pairs,
                           verify_colouring, _solve_k_colouring,
                           is_k_strong_colourable)
from fast_check import is_chi_s_at_most_fast


def parse_graph6(line: str) -> nx.Graph:
    line = line.strip()
    if not line:
        return None
    return nx.from_graph6_bytes(line.encode("ascii"))


def is_chi_s_at_most(G: nx.Graph, k: int) -> bool:
    """Single SAT call: is χ'_s(G) ≤ k? Faster than computing exact χ'_s."""
    edges, sp = strong_adjacency_pairs(G)
    n_e = len(edges)
    if n_e == 0:
        return True
    if len(sp) == n_e * (n_e - 1) // 2:
        return n_e <= k
    return is_k_strong_colourable(n_e, sp, k)


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--bound", type=int, required=True,
                   help="test χ'_s ≤ bound (counterexample = χ'_s > bound)")
    p.add_argument("--exact-on-counterexample", action="store_true",
                   help="compute exact χ'_s for any candidate counterexample "
                        "(default: just confirm > bound)")
    p.add_argument("--bipartite", action="store_true",
                   help="informational; sweep doesn't enforce bipartite-ness")
    p.add_argument("--csv", action="store_true", help="emit CSV header")
    p.add_argument("--every", type=int, default=100,
                   help="stderr progress every N graphs")
    p.add_argument("--time-limit", type=float, default=None)
    p.add_argument("--fast", action="store_true",
                   help="use greedy DSATUR pre-filter (skips SAT for easy cases)")
    args = p.parse_args()
    stats = {} if args.fast else None

    if args.csv:
        print("graph6,n,m,delta,girth,chi_s_le_bound,test_time_s")

    t_start = time.time()
    count = 0
    counterexamples = []

    for line in sys.stdin:
        if args.time_limit and (time.time() - t_start) > args.time_limit:
            print(f"# halted by time limit after {count} graphs", file=sys.stderr)
            break
        G = parse_graph6(line)
        if G is None:
            continue
        n = G.number_of_nodes()
        m = G.number_of_edges()
        delta = max((d for _, d in G.degree()), default=0)
        try:
            girth_val = nx.girth(G)
        except (nx.NetworkXNoCycle, AttributeError):
            girth_val = -1
        t0 = time.time()
        if args.fast:
            ok = is_chi_s_at_most_fast(G, args.bound, stats)
        else:
            ok = is_chi_s_at_most(G, args.bound)
        dt = time.time() - t0

        if not ok:
            # CANDIDATE COUNTEREXAMPLE: confirm via exact χ'_s computation.
            chi_exact = None
            if args.exact_on_counterexample:
                chi_exact = chi_s(G)
            counterexamples.append((line.strip(), n, m, delta, chi_exact))
            print(f"!!! CANDIDATE COUNTEREXAMPLE: g6={line.strip()} n={n} m={m} "
                  f"delta={delta} chi_s>{args.bound}"
                  + (f" exact={chi_exact}" if chi_exact else "") + " !!!",
                  file=sys.stderr)

        if args.csv:
            print(f"{line.strip()},{n},{m},{delta},{girth_val},"
                  f"{'true' if ok else 'false'},{dt:.3f}")
        count += 1
        if count % args.every == 0:
            elapsed = time.time() - t_start
            print(f"# {count} graphs done, {len(counterexamples)} candidates, "
                  f"elapsed={elapsed:.1f}s, rate={count/elapsed:.1f}g/s",
                  file=sys.stderr)

    elapsed = time.time() - t_start
    print(f"# done: {count} graphs in {elapsed:.1f}s "
          f"(rate {count/max(elapsed,0.001):.1f} g/s)", file=sys.stderr)
    if args.fast and stats:
        print(f"# decision-path stats: {stats}", file=sys.stderr)
    if counterexamples:
        print(f"# {len(counterexamples)} CANDIDATE COUNTEREXAMPLES (χ'_s > {args.bound})",
              file=sys.stderr)
        for g6, n, m, delta, chi in counterexamples:
            ce = f" exact={chi}" if chi else ""
            print(f"  g6={g6} n={n} m={m} Δ={delta}{ce}", file=sys.stderr)
    else:
        print(f"# NO counterexamples found (all χ'_s ≤ {args.bound})",
              file=sys.stderr)


if __name__ == "__main__":
    main()
