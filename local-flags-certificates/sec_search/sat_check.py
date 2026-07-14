#!/usr/bin/env python3
"""SAT-based replacement for fast_check.

Usage: cat graph6.lines | sat_check.py <bound> [--csv] [--every N]

Same I/O contract as fast_check (graph6 stdin → CSV stdout / CANDIDATE
stderr), but uses pysat/Glucose3 instead of DSATUR backtracking. Much
faster on tight asymmetric instances where DSATUR backtracks heavily.

For each graph G of m edges, encodes "is there a strong edge colouring
with ≤ bound colours?" as SAT:
  Vars: x_{e,c} for each edge e of G, colour c ∈ {0..bound-1}.
  At-least-one: ∨_c x_{e,c}  for each e.
  Strong-adj clauses: ¬x_{e,c} ∨ ¬x_{f,c}  for each strong-adjacent (e,f), c.

(At-most-one not encoded explicitly — the strong-adj clauses prevent
multiple colours per edge from being useful, and dropping AMO speeds
up encoding considerably.)

Wait, that's wrong — without AMO, we *could* assign multiple colours to
one edge. But for "is χ'_s ≤ k" we only care about existence of a
valid proper colouring, and Glucose's model will pick at least one
true x_{e,c}; we just take the first. Keep AMO for safety.
"""

import argparse
import sys
import time
from itertools import combinations
from pysat.solvers import Glucose3


def graph6_to_edges(s):
    """Decode a graph6 string to a list of edges + n.

    Supports the standard graph6 format (small n header, then row-major
    upper-triangle bits, 6 bits per byte starting at 63).
    """
    if not s:
        return 0, []
    s = s.strip()
    if not s:
        return 0, []
    # First char is n (or '>' for header — we don't expect headers in our pipe).
    i = 0
    c0 = ord(s[0])
    if c0 == 0x7e:  # 126: extended n encoding
        # 3 or 6 bytes; first byte after 126 is either 126 again (8-byte) or
        # 3 bytes of N (6+12+18 bits packed).
        if len(s) > 1 and ord(s[1]) == 0x7e:
            # 8-byte: 126 126 N1 N2 N3 N4 N5 N6
            n = 0
            for k in range(6):
                n = (n << 6) | (ord(s[2 + k]) - 63)
            i = 8
        else:
            # 4-byte: 126 N1 N2 N3
            n = 0
            for k in range(3):
                n = (n << 6) | (ord(s[1 + k]) - 63)
            i = 4
    else:
        n = c0 - 63
        i = 1
    # Remaining bytes encode the bit-vector of the upper-triangle in row-major
    # order, big-endian within each byte (6 bits per byte, MSB first).
    bits = []
    for ch in s[i:]:
        v = ord(ch) - 63
        for k in range(5, -1, -1):
            bits.append((v >> k) & 1)
    edges = []
    idx = 0
    for j in range(1, n):
        for ii in range(j):
            if idx < len(bits) and bits[idx] == 1:
                edges.append((ii, j))
            idx += 1
    return n, edges


def strong_adj_pairs(n, edges):
    """Return list of (i,j) with i<j where edges[i], edges[j] are at
    G-distance ≤ 2 (share a vertex or have endpoints joined by an edge)."""
    # Build adjacency set for quick distance-2 check
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    m = len(edges)
    pairs = []
    for i in range(m):
        u1, v1 = edges[i]
        for j in range(i + 1, m):
            u2, v2 = edges[j]
            # Share a vertex?
            if u1 == u2 or u1 == v2 or v1 == u2 or v1 == v2:
                pairs.append((i, j))
                continue
            # Distance 2?
            if (u2 in adj[u1] or v2 in adj[u1]
                    or u2 in adj[v1] or v2 in adj[v1]):
                pairs.append((i, j))
    return pairs


def is_strongly_k_colourable(m, strong_pairs, k):
    """SAT-decide: does G admit a strong edge colouring with ≤ k colours?"""
    if m == 0:
        return True
    if k <= 0:
        return False
    if k == 1:
        return len(strong_pairs) == 0 and m <= 1

    def var(e, c):
        return e * k + c + 1

    solver = Glucose3()
    # At-least-one: each edge gets ≥ 1 colour.
    for e in range(m):
        solver.add_clause([var(e, c) for c in range(k)])
    # At-most-one (pairwise — fine for small k).
    for e in range(m):
        for c1, c2 in combinations(range(k), 2):
            solver.add_clause([-var(e, c1), -var(e, c2)])
    # Strong-adjacency: no two strong-adjacent edges share a colour.
    for (i, j) in strong_pairs:
        for c in range(k):
            solver.add_clause([-var(i, c), -var(j, c)])
    sat = solver.solve()
    solver.delete()
    return sat


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("bound", type=int)
    ap.add_argument("--csv", action="store_true",
                    help="emit per-graph CSV to stdout")
    ap.add_argument("--every", type=int, default=100,
                    help="progress report frequency")
    args = ap.parse_args()
    bound = args.bound

    if args.csv:
        print("graph6,n,m,bound,passed_path")
        sys.stdout.flush()

    count = 0
    candidates = 0
    t0 = time.monotonic()

    for line in sys.stdin:
        line = line.rstrip("\n").rstrip("\r")
        if not line:
            continue
        n, edges = graph6_to_edges(line)
        m = len(edges)
        if m == 0:
            passed = True
            path = "empty"
        else:
            strong_pairs = strong_adj_pairs(n, edges)
            ok = is_strongly_k_colourable(m, strong_pairs, bound)
            passed = ok
            path = "sat" if ok else "FAIL_sat"
        if args.csv:
            print(f"{line},{n},{m},{bound},{path}")
        if not passed:
            candidates += 1
            print(f"!!! CANDIDATE COUNTEREXAMPLE: g6={line} n={n} m={m} "
                  f"(χ'_s > {bound} via SAT) !!!", file=sys.stderr)
        count += 1
        if count % args.every == 0:
            dt = time.monotonic() - t0
            print(f"# {count} graphs done, {candidates} candidates, "
                  f"elapsed={dt:.1f}s, rate={count/dt:.1f}g/s",
                  file=sys.stderr)
            sys.stderr.flush()

    dt = time.monotonic() - t0
    print(f"# done: {count} graphs in {dt:.1f}s "
          f"(rate {count/max(dt, 1e-9):.0f}g/s)", file=sys.stderr)
    if candidates > 0:
        print(f"# {candidates} CANDIDATE COUNTEREXAMPLES (chi_s > {bound})",
              file=sys.stderr)
    sys.exit(1 if candidates > 0 else 0)


if __name__ == "__main__":
    main()
