#!/usr/bin/env python3
"""
Phase 4 — sub-category 4a: finite-geometry constructions.

Levi graphs of:
  * Projective planes PG(2, q) for q in {2,3,4,5,7,8,9,11}
  * Generalised quadrangles GQ(2,2) [Tutte-Coxeter graph]
  * Generalised hexagons (small)
Plus Kneser K(n,k) and Johnson J(n,k) graphs.

Output: appends rows to phase4_logs/all_graphs.tsv (source='4a_*').
Prints per-graph one-line summary to stdout.
"""

from __future__ import annotations

import itertools
import os
import sys
from fractions import Fraction

import networkx as nx

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import (
    CLEBSCH_RATIO,
    is_triangle_free,
    girth,
    count_induced_5cycles,
    graph_stats,
    ratio_str,
    vs_clebsch,
    open_tsv,
    tsv_row,
)


# ============================================================ Projective planes


def desarguesian_plane_points_lines(q: int):
    """
    Return (points, lines) for the Desarguesian projective plane PG(2, q),
    q a prime power. Points = 1-dim subspaces of F_q^3; lines = 2-dim subspaces.

    For prime q we use F_q = Z/qZ. For prime-power q in {4, 8, 9} we use sympy's
    GF.
    """
    # Build F_q as a list of elements; need primitive polynomial for non-prime.
    if all(q % p != 0 for p in [2, 3, 5, 7, 11, 13]) or _is_prime(q):
        field = list(range(q))
        add = lambda a, b: (a + b) % q
        mul = lambda a, b: (a * b) % q
        zero, one = 0, 1
    else:
        # Use sympy's GF for q = p^k.
        import sympy
        from sympy.polys.domains import GF as SymGF
        F = SymGF(q)
        # We sample all elements: GF(q) has q elements; we iterate via int(i) up to q-1.
        # sympy.GF makes a "GroundType"; we instead build the field explicitly.
        # The easier route: build F_{p^k} via galois package if present, else fallback.
        try:
            import galois
            GFq = galois.GF(q)
            # Use ints 0..q-1 as canonical reps; bridge to/from GFq for ops.
            field = list(range(q))
            zero, one = 0, 1
            def _wrap(a): return GFq(a)
            def _unwrap(x): return int(x)
            add = lambda a, b: _unwrap(_wrap(a) + _wrap(b))
            mul = lambda a, b: _unwrap(_wrap(a) * _wrap(b))
        except ImportError:
            raise RuntimeError(
                f"PG(2,{q}) requires `galois` package for non-prime q. "
                f"pip install galois"
            )

    # 1-dim subspaces of F_q^3: vectors (a,b,c) != 0, mod scalar.
    # Canonical rep: first non-zero coord = 1. We can canonicalise by:
    #   if a != 0: scale by a^{-1} -> (1, b/a, c/a)
    #   elif b != 0: scale by b^{-1} -> (0, 1, c/b)
    #   else: (0, 0, 1)
    def inv(x):
        # For prime q (int field): use pow(x, -1, q).
        # For prime-power q via galois bridge: x is an int in [1, q-1]; compute
        # inverse in GF(q) and unwrap to int.
        if _is_prime(q):
            return pow(x, -1, q)
        # prime-power case: use galois
        import galois
        GFq = galois.GF(q)
        return int(GFq(x) ** -1)

    def canon(v):
        a, b, c = v
        if a != zero:
            ia = inv(a)
            return (one, mul(b, ia), mul(c, ia))
        if b != zero:
            ib = inv(b)
            return (zero, one, mul(c, ib))
        return (zero, zero, one)

    # Enumerate non-zero vectors and canonicalise.
    points = set()
    for a in field:
        for b in field:
            for c in field:
                if a == zero and b == zero and c == zero:
                    continue
                points.add(canon((a, b, c)))
    points = sorted(points, key=lambda p: tuple(_to_int(x, q) for x in p))

    # Lines (2-dim subspaces): same as points via plane-line duality (use dual triples
    # for the line ax + by + cz = 0; canonicalise the same way.)
    lines = points[:]  # same canonical-tuple set; a line is identified with its
                       # (a,b,c) coeff triple.

    # Incidence: point (x,y,z) lies on line (a,b,c) iff ax + by + cz = 0.
    def inc(pt, ln):
        s = add(add(mul(ln[0], pt[0]), mul(ln[1], pt[1])), mul(ln[2], pt[2]))
        return s == zero

    return points, lines, inc


def _is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    for d in range(3, int(n ** 0.5) + 1, 2):
        if n % d == 0:
            return False
    return True


def _to_int(x, q):
    if isinstance(x, int):
        return x
    # Try galois GF element.
    try:
        return int(x)
    except Exception:
        return hash(x)


def levi_graph_pg2(q: int) -> nx.Graph:
    """Levi graph of PG(2, q): bipartite, (q+1)-regular, 2(q^2+q+1) vertices."""
    points, lines, inc = desarguesian_plane_points_lines(q)
    G = nx.Graph()
    p_nodes = [("P", p) for p in points]
    l_nodes = [("L", l) for l in lines]
    G.add_nodes_from(p_nodes)
    G.add_nodes_from(l_nodes)
    for p in points:
        for l in lines:
            if inc(p, l):
                G.add_edge(("P", p), ("L", l))
    return G


# ============================================================ Kneser & Johnson


def kneser_graph(n: int, k: int) -> nx.Graph:
    """K(n,k): vertices = k-subsets of [n]; edges = disjoint pairs."""
    verts = list(itertools.combinations(range(n), k))
    vset = [frozenset(v) for v in verts]
    G = nx.Graph()
    G.add_nodes_from(range(len(vset)))
    for i, j in itertools.combinations(range(len(vset)), 2):
        if vset[i].isdisjoint(vset[j]):
            G.add_edge(i, j)
    return G


def johnson_graph(n: int, k: int) -> nx.Graph:
    """J(n,k): vertices = k-subsets of [n]; edges = subsets meeting in k-1 elts."""
    verts = list(itertools.combinations(range(n), k))
    vset = [frozenset(v) for v in verts]
    G = nx.Graph()
    G.add_nodes_from(range(len(vset)))
    for i, j in itertools.combinations(range(len(vset)), 2):
        if len(vset[i] & vset[j]) == k - 1:
            G.add_edge(i, j)
    return G


# ============================================================ Generalised quadrangles & hexagons


def tutte_coxeter_graph() -> nx.Graph:
    """
    Tutte-Coxeter graph = Levi graph of GQ(2,2) = generalised quadrangle of order (2,2).
    30 vertices, 3-regular, girth 8, bipartite.
    Built as the Levi graph of the unique GQ(2,2), with vertex set
    {synthemes} ∪ {duads} on a 6-element set, edge = incidence.

    A duad = 2-subset of {1..6}; a syntheme = partition of {1..6} into three duads.
    There are 15 duads and 15 synthemes. Each duad lies in 3 synthemes; each
    syntheme contains 3 duads. The Levi graph is the desired graph.
    """
    duads = list(itertools.combinations(range(1, 7), 2))
    duad_set = [frozenset(d) for d in duads]
    duad_id = {d: i for i, d in enumerate(duad_set)}

    # A syntheme is a partition of {1..6} into 3 duads. Enumerate.
    synthemes = []
    pts = list(range(1, 7))
    for d1 in itertools.combinations(pts, 2):
        rest1 = [p for p in pts if p not in d1]
        for d2 in itertools.combinations(rest1, 2):
            d3 = tuple(sorted(p for p in rest1 if p not in d2))
            if d2 < d3:  # canonicalise (avoid permutations of the 3 duads)
                synthemes.append((frozenset(d1), frozenset(d2), frozenset(d3)))
    # Dedupe (canonical order of the 3 duads).
    canon = set()
    for s in synthemes:
        canon.add(tuple(sorted(s, key=lambda d: sorted(d))))
    synthemes = sorted(canon, key=lambda s: tuple(sorted(d) for d in s))

    G = nx.Graph()
    d_nodes = [("D", i) for i in range(len(duad_set))]
    s_nodes = [("S", i) for i in range(len(synthemes))]
    G.add_nodes_from(d_nodes)
    G.add_nodes_from(s_nodes)
    for si, s in enumerate(synthemes):
        for d in s:
            di = duad_id[d]
            G.add_edge(("D", di), ("S", si))
    return G


# ============================================================ Polarity graph


def orthogonal_polarity_graph(q: int) -> nx.Graph:
    """
    Brown / Erdős-Rényi polarity graph ER_q.

    Built on points of PG(2,q) with the polarity p = (a,b,c) <-> line L_p:
    ax + by + cz = 0. Vertex p connects to p' iff p lies on L_{p'}, i.e.,
    a*a' + b*b' + c*c' = 0 (and p != p').

    n = q^2+q+1, regular(q+1) except for absolute points (where p lies on L_p),
    which have degree q.

    NOT generally triangle-free for q >= 3, but C_4-free always. We compute and
    let the TSV log report TF=0/1.
    """
    points, _, _ = desarguesian_plane_points_lines(q)
    G = nx.Graph()
    G.add_nodes_from(range(len(points)))

    def dot(p, p_):
        # The "inc" function in desarguesian_plane_points_lines tests the same.
        # But our points are tuples of either ints or galois GF elements.
        if isinstance(p[0], int):
            return (p[0] * p_[0] + p[1] * p_[1] + p[2] * p_[2]) % q
        # galois GF
        zero = p[0] * 0  # works for galois GF
        return p[0] * p_[0] + p[1] * p_[1] + p[2] * p_[2]

    if isinstance(points[0][0], int):
        zero_test = lambda v: v == 0
    else:
        zero_test = lambda v: int(v) == 0

    for i in range(len(points)):
        for j in range(i + 1, len(points)):
            if zero_test(dot(points[i], points[j])):
                G.add_edge(i, j)
    return G


# ============================================================ Driver


def run(tsv_path: str):
    f = open_tsv(tsv_path, append=True)
    results = []

    def test(source: str, name: str, G: nx.Graph):
        tf, r, P = tsv_row(f, source, name, G)
        n, Delta, m, tf2, g = graph_stats(G)
        gout = g if g != sys.maxsize else -1
        rf = float(r)
        vs = vs_clebsch(r)
        msg = (f"[{source}] {name}: n={n} Δ={Delta} m={m} girth={gout} "
               f"TF={int(tf)} P={P} ratio={rf:.6f} ({vs} Clebsch)")
        print(msg)
        results.append((source, name, n, Delta, P, r, rf, tf, gout))
        return r, P

    # ---------- 4a-PG: Projective planes -----------
    for q in [2, 3, 4, 5, 7, 8, 9]:
        try:
            G = levi_graph_pg2(q)
            test("4a_PG", f"Levi-PG(2,{q})", G)
        except Exception as e:
            print(f"[4a_PG] q={q} FAILED: {e}")

    # q=11 is bigger: 266 vertices, 11+1=12-regular Levi. Pentagons might be many.
    # We attempt it; counter is O(n*Delta^4) ~ 266*20736 ≈ 5.5M ops per vertex
    # for the path probe — should be fast.
    try:
        G = levi_graph_pg2(11)
        test("4a_PG", "Levi-PG(2,11)", G)
    except Exception as e:
        print(f"[4a_PG] q=11 FAILED: {e}")

    # ---------- 4a-GQ: GQ(2,2) Tutte-Coxeter -----------
    G = tutte_coxeter_graph()
    test("4a_GQ", "TutteCoxeter-GQ(2,2)", G)

    # ---------- 4a-Kneser ----------
    # K(n,k) TF iff n < 3k.
    for (n, k) in [(5, 2), (6, 2), (7, 3), (8, 3), (9, 4), (10, 4), (11, 4),
                   (11, 5), (12, 5), (13, 5), (13, 6)]:
        try:
            G = kneser_graph(n, k)
            test("4a_Kneser", f"K({n},{k})", G)
        except Exception as e:
            print(f"[4a_Kneser] K({n},{k}) FAILED: {e}")

    # ---------- 4a-Johnson ----------
    # J(n,k): edges between k-subsets meeting in k-1 elts. Usually has triangles.
    for (n, k) in [(5, 2), (6, 2), (7, 3), (8, 3), (9, 4), (10, 4)]:
        try:
            G = johnson_graph(n, k)
            test("4a_Johnson", f"J({n},{k})", G)
        except Exception as e:
            print(f"[4a_Johnson] J({n},{k}) FAILED: {e}")

    # ---------- 4a-Polarity: Brown-Erdős-Sós polarity graphs of PG(2,q) ----------
    # ER_q (polarity graph) — vertices = points of PG(2,q), edge (p, p') iff
    # p lies on the line dual to p' (and p != p'). These are TF only for special
    # polarities; the orthogonal polarity gives the Erdős-Rényi polarity graph
    # which has K_{1,q+1} but is C_4-free, n = q^2+q+1, regular degree q+1 or q.
    # NOT triangle-free in general — but contains long paths. We test for TF
    # after construction.
    for q in [2, 3, 5, 7, 11]:
        try:
            G = orthogonal_polarity_graph(q)
            test("4a_Polarity", f"ER_polarity({q})", G)
        except Exception as e:
            print(f"[4a_Polarity] q={q} FAILED: {e}")

    # ---------- 4a-PG (prime-power q via galois) ----------
    for q in [4, 8, 9]:
        try:
            G = levi_graph_pg2(q)
            test("4a_PG", f"Levi-PG(2,{q})", G)
        except Exception as e:
            print(f"[4a_PG] q={q} FAILED: {e}")

    f.close()

    # Local summary
    best = max(results, key=lambda t: t[5])
    print()
    print(f"4a SUMMARY: best ratio = {float(best[5]):.6f} at "
          f"{best[0]}/{best[1]} (Clebsch ratio: {float(CLEBSCH_RATIO):.6f})")
    return results


if __name__ == "__main__":
    tsv = sys.argv[1] if len(sys.argv) > 1 else (
        os.path.join(os.path.dirname(__file__), "..", "phase4_logs", "all_graphs.tsv")
    )
    run(tsv)
