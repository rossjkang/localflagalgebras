#!/usr/bin/env python3
"""
Pentagon counter — reads graph6 strings from stdin (one per line, as
emitted by nauty's `geng`), counts induced 5-cycles, and reports the
maximum ratio P(G) / (|G| * Delta^4) plus the graph achieving it.

Used by phase2_geng_sweep.sh: `geng -t -d{D} -D{D} {n} | pentagon_counter.py`.

Output (to stdout): one summary line per stream, of the form
    n={n} Delta={D} count={N} max_P={P} max_ratio_num={p} max_ratio_den={q}
    max_g6={g6} max_girth={g}

with `max_g6` being the graph6 string of the graph achieving the max
ratio (ties broken by lexicographic order). A `--verbose` flag dumps a
per-graph table including girth for the top-K ratios.
"""

from __future__ import annotations

import argparse
import heapq
import itertools
import sys
from fractions import Fraction
from typing import Optional

import networkx as nx


def parse_graph6(line: str) -> Optional[nx.Graph]:
    line = line.strip()
    if not line or line.startswith(">"):
        return None
    try:
        return nx.from_graph6_bytes(line.encode("ascii"))
    except Exception:
        return None


def count_induced_5cycles(G: nx.Graph) -> int:
    """Canonical-orientation induced-C_5 count (same as Phase 1)."""
    nodes = list(G.nodes())
    idx = {v: i for i, v in enumerate(nodes)}
    adj = {v: set(G.neighbors(v)) for v in nodes}
    cnt = 0
    for v0 in nodes:
        i0 = idx[v0]
        Nv0 = [u for u in adj[v0] if idx[u] > i0]
        for v1, v4 in itertools.combinations(Nv0, 2):
            if v4 in adj[v1]:
                continue
            for v2 in adj[v1]:
                if idx[v2] <= i0 or v2 == v4:
                    continue
                if v2 in adj[v0] or v2 in adj[v4]:
                    continue
                for v3 in adj[v2] & adj[v4]:
                    if idx[v3] <= i0 or v3 == v1 or v3 == v2:
                        continue
                    if v3 in adj[v0] or v3 in adj[v1]:
                        continue
                    cnt += 1
    return cnt


def girth(G: nx.Graph) -> int:
    n = G.number_of_nodes()
    if n == 0 or G.number_of_edges() == 0:
        return sys.maxsize
    best = sys.maxsize
    for src in G.nodes():
        dist = {src: 0}
        parent = {src: None}
        queue = [src]
        head = 0
        while head < len(queue):
            u = queue[head]; head += 1
            for v in G.neighbors(u):
                if v not in dist:
                    dist[v] = dist[u] + 1
                    parent[v] = u
                    queue.append(v)
                elif parent[u] != v:
                    cycle_len = dist[u] + dist[v] + 1
                    if cycle_len < best:
                        best = cycle_len
        if best == 3:
            return 3
    return best


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--verbose", "-v", action="store_true",
                    help="dump per-graph table for the top-K ratios")
    ap.add_argument("--top-k", type=int, default=5)
    ap.add_argument("--report-all", action="store_true",
                    help="emit g6 + ratio for every input graph (debug)")
    ap.add_argument("--label", default="",
                    help="optional label echoed in the summary line")
    args = ap.parse_args()

    count = 0
    max_P = 0
    max_ratio = Fraction(0)
    max_g6 = ""
    max_n = 0
    max_D = 0
    max_girth_val = 0
    # Streaming top-K: min-heap of (ratio, idx, P, n, D, g6, g6_girth_flag) tuples.
    # We use idx as tie-breaker to avoid Fraction comparison ambiguity on heap.
    top_heap = []  # heapq min-heap of size <= args.top_k
    top_k = args.top_k if (args.verbose or args.report_all) else 0

    for line in sys.stdin:
        G = parse_graph6(line)
        if G is None:
            continue
        n = G.number_of_nodes()
        if n == 0:
            continue
        degs = [d for _, d in G.degree()]
        D = max(degs) if degs else 0
        if D == 0:
            count += 1
            continue
        P = count_induced_5cycles(G)
        ratio = Fraction(P, n * D ** 4)
        g6 = line.strip()
        count += 1
        if top_k > 0:
            # Maintain top-K (largest ratios) via min-heap of size top_k.
            entry = (ratio, count, P, n, D, g6)
            if len(top_heap) < top_k:
                heapq.heappush(top_heap, entry)
            elif ratio > top_heap[0][0]:
                heapq.heapreplace(top_heap, entry)
        if ratio > max_ratio:
            max_ratio = ratio
            max_P = P
            max_g6 = g6
            max_n = n
            max_D = D
            max_girth_val = girth(G) if P > 0 else 0
        if args.report_all:
            print(f"  {g6}\tn={n}\tD={D}\tP={P}\tratio={float(ratio):.6f}",
                  file=sys.stderr)

    if max_ratio == 0:
        print(f"LABEL={args.label} count={count} max_P=0 max_ratio_num=0 "
              f"max_ratio_den=1 max_g6=- max_n=0 max_D=0 max_girth=0")
        return

    print(f"LABEL={args.label} count={count} max_P={max_P} "
          f"max_ratio_num={max_ratio.numerator} "
          f"max_ratio_den={max_ratio.denominator} "
          f"max_g6={max_g6} max_n={max_n} max_D={max_D} "
          f"max_girth={max_girth_val}")
    if args.verbose and top_heap:
        # Print top-K table to stderr (sorted descending by ratio).
        # Heap stores up to top_k entries; sort once at the end.
        rows = sorted(top_heap, key=lambda r: (-r[0], r[5]))
        print(f"# Top {args.top_k} graphs by ratio (label={args.label}):",
              file=sys.stderr)
        for ratio, _idx, P, n, D, g6 in rows:
            # Re-compute girth only for the top-K (cheap; K <= 20).
            G = parse_graph6(g6)
            g = girth(G) if (G is not None and P > 0) else 0
            print(f"  {g6}\tn={n}\tD={D}\tP={P}\t"
                  f"ratio={ratio} ({float(ratio):.6f})\tgirth={g}",
                  file=sys.stderr)


if __name__ == "__main__":
    main()
