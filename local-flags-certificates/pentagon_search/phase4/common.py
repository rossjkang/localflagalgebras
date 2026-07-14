#!/usr/bin/env python3
"""
Phase 4 — common utilities.

Pentagon counting, girth, TSV-row emission, triangle-free check.

The "ratio" used throughout Phase 4 is

    delta(G) = P(G) / (|G| * Delta(G)^4)

with the Clebsch benchmark at 12/625 = 0.01920.
"""

from __future__ import annotations

import itertools
import sys
from fractions import Fraction
from typing import Iterable, Optional

import networkx as nx


CLEBSCH_RATIO = Fraction(12, 625)  # 0.01920


def is_triangle_free(G: nx.Graph) -> bool:
    for u, v in G.edges():
        nu = set(G.neighbors(u))
        nv = set(G.neighbors(v))
        if nu & nv:
            return False
    return True


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


def count_induced_5cycles(G: nx.Graph) -> int:
    """Canonical-orientation induced-C_5 count. ~10x faster than C(n,5)."""
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


def graph_stats(G: nx.Graph) -> tuple[int, int, int, bool, int]:
    """Return (n, Delta, m, TF, girth_val)."""
    n = G.number_of_nodes()
    m = G.number_of_edges()
    if n == 0:
        return 0, 0, 0, True, sys.maxsize
    degs = [d for _, d in G.degree()]
    Delta = max(degs) if degs else 0
    tf = is_triangle_free(G)
    g = girth(G) if m > 0 else sys.maxsize
    return n, Delta, m, tf, g


def ratio_str(P: int, n: int, Delta: int) -> tuple[Fraction, float]:
    if n == 0 or Delta == 0:
        return Fraction(0), 0.0
    r = Fraction(P, n * Delta ** 4)
    return r, float(r)


def vs_clebsch(r: Fraction) -> str:
    """Return '>', '=', '<' against CLEBSCH_RATIO."""
    if r > CLEBSCH_RATIO:
        return ">"
    if r == CLEBSCH_RATIO:
        return "="
    return "<"


# ============================================================ TSV logging


TSV_HEADER = "source\tname\tn\tDelta\tm\tgirth\tTF\tP\tratio_num\tratio_den\tratio_float\tvs_clebsch\n"


def open_tsv(path: str, append: bool = False):
    """Open the master TSV with header written iff new file."""
    import os
    new = not os.path.exists(path) or os.path.getsize(path) == 0
    f = open(path, "a" if append else "w", buffering=1)
    if new or not append:
        f.write(TSV_HEADER)
    return f


def tsv_row(f, source: str, name: str, G: nx.Graph) -> tuple[bool, Fraction, int]:
    """
    Compute stats + ratio + write a row.

    Returns (is_TF, ratio, P). Skips pentagon counting if girth >= 6.
    """
    n, Delta, m, tf, g = graph_stats(G)
    if not tf or g >= 6 or Delta == 0:
        # Pentagon count is 0 in these cases.
        P = 0
    else:
        P = count_induced_5cycles(G)
    r, rf = ratio_str(P, n, Delta)
    girth_out = -1 if g == sys.maxsize else g
    vs = vs_clebsch(r)
    f.write(
        f"{source}\t{name}\t{n}\t{Delta}\t{m}\t{girth_out}\t{int(tf)}\t"
        f"{P}\t{r.numerator}\t{r.denominator}\t{rf:.8f}\t{vs}\n"
    )
    return tf, r, P
