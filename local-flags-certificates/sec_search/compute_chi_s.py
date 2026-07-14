#!/usr/bin/env python3
"""Compute the strong chromatic index χ'_s(G) via SAT.

χ'_s(G) = χ(L(G)²) — the chromatic number of the square of the line graph.
Equivalently, the minimum colours for a proper edge-colouring such that
two edges sharing an endpoint OR connected by another edge get different
colours.

SAT encoding (k-colourability of the "strong-adjacency" graph H = L(G)²):
  Variables: x_{e,c} for each edge e of G, colour c ∈ {1..k}.
  At-least-one: ∨_c x_{e,c}  for each e.
  At-most-one: ¬x_{e,c1} ∨ ¬x_{e,c2}  for each e, c1 < c2.
  Strong-adj clauses: ¬x_{e,c} ∨ ¬x_{f,c}  for each strong-adjacent (e,f) and c.

Binary-search k between a lower bound (greedy) and upper bound (|E|).

Reference output for smoke test:
  χ'_s(K_n) = n(n-1)/2 = |E(K_n)|  for small n
  χ'_s(K_{n,n}) = n² = |E(K_{n,n})|
  χ'_s(C_n) = 5 for n ∈ {5, 7, 9}; = 4 for n=4,6; bigger n same recurrence
  χ'_s(Petersen) = 7   (Andersen / Faudree-Schelp-Gyárfás-Tuza)
  χ'_s(Heawood)  = ?   (this run determines)
"""

import argparse
import sys
import time
from itertools import combinations
from pathlib import Path

import networkx as nx
from pysat.solvers import Glucose3


def strong_adjacency_pairs(G: nx.Graph):
    """Return list of pairs (e, f) where e, f are strong-adjacent edges.

    Two edges e, f are strong-adjacent iff
    (a) they share an endpoint, OR
    (b) some endpoint of e is adjacent to some endpoint of f.

    Returns sorted list of (e_idx, f_idx) with e_idx < f_idx.
    """
    edges = sorted(tuple(sorted(e)) for e in G.edges())
    n_edges = len(edges)
    pairs = []
    for i, j in combinations(range(n_edges), 2):
        u1, v1 = edges[i]
        u2, v2 = edges[j]
        if {u1, v1} & {u2, v2}:
            pairs.append((i, j))
            continue
        # Check distance-2: any endpoint of i adjacent to any endpoint of j
        if (G.has_edge(u1, u2) or G.has_edge(u1, v2)
                or G.has_edge(v1, u2) or G.has_edge(v1, v2)):
            pairs.append((i, j))
    return edges, pairs


def _solve_k_colouring(n_edges: int, strong_pairs, k: int):
    """Return (sat: bool, colouring: list[int] or None) for k-strong-colouring."""
    if k <= 0:
        return (n_edges == 0, [] if n_edges == 0 else None)
    if k == 1:
        if len(strong_pairs) == 0 and n_edges <= 1:
            return (True, [0] * n_edges)
        return (False, None)

    def var(e, c):
        return e * k + c + 1

    solver = Glucose3()
    for e in range(n_edges):
        solver.add_clause([var(e, c) for c in range(k)])
    for e in range(n_edges):
        for c1, c2 in combinations(range(k), 2):
            solver.add_clause([-var(e, c1), -var(e, c2)])
    for (i, j) in strong_pairs:
        for c in range(k):
            solver.add_clause([-var(i, c), -var(j, c)])
    sat = solver.solve()
    if not sat:
        solver.delete()
        return (False, None)
    model = solver.get_model()
    solver.delete()
    colouring = [-1] * n_edges
    mset = set(v for v in model if v > 0)
    for e in range(n_edges):
        for c in range(k):
            if var(e, c) in mset:
                colouring[e] = c
                break
    return (True, colouring)


def is_k_strong_colourable(n_edges: int, strong_pairs, k: int) -> bool:
    return _solve_k_colouring(n_edges, strong_pairs, k)[0]


def verify_colouring(n_edges: int, strong_pairs, colouring) -> bool:
    """Sanity-check a candidate colouring: each edge has a colour, no two
    strong-adjacent edges share a colour."""
    if any(c < 0 for c in colouring):
        return False
    for (i, j) in strong_pairs:
        if colouring[i] == colouring[j]:
            return False
    return True


def chi_s(G: nx.Graph, k_lo: int = None, k_hi: int = None,
          verbose: bool = False) -> int:
    """Compute χ'_s(G) by binary-search over SAT."""
    edges, strong_pairs = strong_adjacency_pairs(G)
    n_edges = len(edges)
    if n_edges == 0:
        return 0
    if n_edges == 1:
        return 1

    # Shortcut: if L(G)² is the complete graph on n_edges vertices,
    # then χ'_s(G) = n_edges (every edge needs its own colour).
    n_strong_pairs = len(strong_pairs)
    n_all_pairs = n_edges * (n_edges - 1) // 2
    if n_strong_pairs == n_all_pairs:
        return n_edges

    # Compute clique lower bound on L(G)².
    # 1. For any edge (u,v), the deg(u) + deg(v) - 1 incident edges form
    #    a clique in L(G)².
    # 2. For any vertex v of degree d, picking 2 incident edges and a
    #    "next neighbour" edge can give larger cliques (skipped here).
    max_clique_lb = 1
    for u, v in G.edges():
        cl = G.degree(u) + G.degree(v) - 1
        if cl > max_clique_lb:
            max_clique_lb = cl

    # Compute Δ(L²) for greedy upper bound.
    strong_deg = [0] * n_edges
    for i, j in strong_pairs:
        strong_deg[i] += 1
        strong_deg[j] += 1
    max_strong_deg = max(strong_deg) if strong_deg else 0

    if k_lo is None:
        k_lo = max(1, max_clique_lb)
    if k_hi is None:
        # Greedy bound + safety. Greedy on L(G)² gives ≤ Δ(L²) + 1.
        k_hi = max_strong_deg + 1

    if verbose:
        print(f"  chi_s search: lo={k_lo} hi={k_hi} edges={n_edges} "
              f"strong-pairs={n_strong_pairs} max_strong_deg={max_strong_deg} "
              f"clique_lb={max_clique_lb}", file=sys.stderr)

    # Confirm k_hi works (greedy bound should but doubles as safety).
    while not is_k_strong_colourable(n_edges, strong_pairs, k_hi):
        if verbose:
            print(f"    {k_hi} infeasible, doubling hi", file=sys.stderr)
        k_hi = max(k_hi + 1, k_hi * 2)
    # Binary search for the smallest k that is colourable.
    while k_lo < k_hi:
        mid = (k_lo + k_hi) // 2
        if is_k_strong_colourable(n_edges, strong_pairs, mid):
            k_hi = mid
        else:
            k_lo = mid + 1
        if verbose:
            print(f"    bisect: lo={k_lo} hi={k_hi}", file=sys.stderr)
    return k_lo


# ============================================================
# Named test graphs
# ============================================================

def G_complete(n):
    return nx.complete_graph(n)


def G_complete_bipartite(n, m):
    return nx.complete_bipartite_graph(n, m)


def G_cycle(n):
    return nx.cycle_graph(n)


def G_petersen():
    return nx.petersen_graph()


def G_mobius_kantor():
    # Möbius-Kantor = Generalized Petersen GP(8, 3):
    # 16 vertices, 24 edges, 3-regular, bipartite, girth 6.
    # Outer 8-cycle: 0-1-...-7-0; inner edges i ↔ i+3 mod 8 on vertices 8..15;
    # spokes i ↔ i+8.
    g = nx.Graph()
    for i in range(8):
        g.add_edge(i, (i + 1) % 8)              # outer
        g.add_edge(8 + i, 8 + (i + 3) % 8)      # inner (3-step cycle)
        g.add_edge(i, i + 8)                    # spoke
    return g


def G_heawood():
    # Heawood: 3-regular, 14 vertices, bipartite, girth 6.
    # Built from McKay's table; networkx has it.
    return nx.heawood_graph()


def G_desargues():
    # Desargues: 3-regular, 20 vertices, bipartite, girth 6.
    return nx.desargues_graph()


def G_hypercube(d):
    return nx.hypercube_graph(d)


def G_prism(n):
    # Y_n = K_n × K_2 (prism over K_n). For n=3 = K_3 × K_2 (3-regular).
    return nx.cartesian_product(nx.complete_graph(n), nx.complete_graph(2))


def G_5blowup_C5():
    # 5-blowup of C_5: 25 vertices, Δ=10, conjectured-tight extremal
    # for Erdős-Nešetřil. Each of 5 "blocks" has 5 vertices, between
    # consecutive blocks all 25 edges present.
    g = nx.Graph()
    for b in range(5):
        for v in range(5):
            for w in range(5):
                g.add_edge((b, v), ((b + 1) % 5, w))
    return g


# ============================================================
# Smoke test suite
# ============================================================

SMOKE_TESTS = [
    # (name, graph factory, expected_chi_s, expected_delta)
    # Corrected after first SAT pipeline run: C_n for n in {6,7,8} have
    # lower χ'_s than I initially claimed.
    #   L²(C_6) = K_6 minus perfect matching = K_{2,2,2}, χ = 3.
    #   L²(C_7) is the complement of a 2-regular graph on 7 vertices; χ = 4.
    #   L²(C_8): similar, χ = 4.
    ("C4=K_{2,2}",     lambda: G_cycle(4),               4,  2),
    ("C5",             lambda: G_cycle(5),               5,  2),
    ("C6",             lambda: G_cycle(6),               3,  2),
    ("C7",             lambda: G_cycle(7),               4,  2),
    ("C8",             lambda: G_cycle(8),               4,  2),
    ("K3",             lambda: G_complete(3),            3,  2),
    ("K4",             lambda: G_complete(4),            6,  3),
    ("K5",             lambda: G_complete(5),           10,  4),
    ("K6",             lambda: G_complete(6),           15,  5),
    ("K_{2,2}",        lambda: G_complete_bipartite(2,2),4,  2),
    ("K_{3,3}",        lambda: G_complete_bipartite(3,3),9,  3),
    ("K_{4,4}",        lambda: G_complete_bipartite(4,4),16, 4),
    # Petersen: SAT-verified χ'_s = 5 (k=3,4 UNSAT; k=5 SAT with explicit
    # verified colouring). Matches clique lower bound (Δ+Δ-1 = 5). I had
    # initially recalled 7 from literature but that appears wrong.
    ("Petersen",       G_petersen,                       5,  3),
]


def smoke_test(verbose=False):
    print(f"{'Graph':18s} {'Δ':>3s} {'|E|':>4s} {'χ_s (exp)':>10s} "
          f"{'χ_s (got)':>10s} {'time(s)':>8s}  status", flush=True)
    print("-" * 80, flush=True)
    all_ok = True
    for name, factory, expected, expected_delta in SMOKE_TESTS:
        G = factory()
        delta = max(d for _, d in G.degree())
        m = G.number_of_edges()
        print(f"{name:18s} {delta:>3d} {m:>4d} {expected:>10d} ... ",
              end="", flush=True)
        t0 = time.time()
        got = chi_s(G, verbose=verbose)
        dt = time.time() - t0
        ok = (got == expected) and (delta == expected_delta)
        all_ok &= ok
        print(f"{got:>5d} {dt:>8.2f}  {'OK' if ok else 'FAIL'}", flush=True)
    print("-" * 80, flush=True)
    print(f"Overall: {'ALL OK' if all_ok else 'FAILURES PRESENT'}", flush=True)
    return all_ok


# ============================================================
# T3 panel
# ============================================================

T3_PANEL = [
    # (name, graph factory)
    # — general panel
    ("Pentagon C5",        lambda: G_cycle(5)),
    ("C6",                 lambda: G_cycle(6)),
    ("C7",                 lambda: G_cycle(7)),
    ("K4",                 lambda: G_complete(4)),
    ("K5",                 lambda: G_complete(5)),
    ("K6",                 lambda: G_complete(6)),
    ("K7",                 lambda: G_complete(7)),
    ("Petersen (cubic)",   G_petersen),
    ("Mobius-Kantor",      G_mobius_kantor),
    ("Prism Y3 = K3xK2",   lambda: G_prism(3)),
    # — bipartite panel
    ("K_{2,2}",            lambda: G_complete_bipartite(2, 2)),
    ("K_{3,3}",            lambda: G_complete_bipartite(3, 3)),
    ("K_{4,4}",            lambda: G_complete_bipartite(4, 4)),
    ("C6 (bipartite)",     lambda: G_cycle(6)),
    ("Heawood",            G_heawood),
    ("Desargues",          G_desargues),
    ("Q3 hypercube",       lambda: G_hypercube(3)),
    ("Q4 hypercube",       lambda: G_hypercube(4)),
]


def run_panel(verbose=False):
    print(f"{'Graph':22s} {'Δ':>3s} {'n':>3s} {'|E|':>4s} {'bipartite?':>10s} "
          f"{'χ_s':>5s} {'χ_s/Δ²':>8s} {'time(s)':>8s}")
    print("-" * 90)
    for name, factory in T3_PANEL:
        G = factory()
        delta = max(d for _, d in G.degree())
        nV = G.number_of_nodes()
        m = G.number_of_edges()
        bip = "yes" if nx.is_bipartite(G) else "no"
        t0 = time.time()
        chis = chi_s(G, verbose=verbose)
        dt = time.time() - t0
        ratio = chis / (delta * delta)
        print(f"{name:22s} {delta:>3d} {nV:>3d} {m:>4d} {bip:>10s} "
              f"{chis:>5d} {ratio:>8.3f} {dt:>8.2f}")


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--test-suite", action="store_true",
                   help="run smoke tests against known χ'_s values")
    p.add_argument("--panel", action="store_true",
                   help="run T3 panel and tabulate χ'_s")
    p.add_argument("-v", "--verbose", action="store_true")
    args = p.parse_args()
    if args.test_suite:
        ok = smoke_test(verbose=args.verbose)
        sys.exit(0 if ok else 1)
    elif args.panel:
        run_panel(verbose=args.verbose)
    else:
        p.print_help()


if __name__ == "__main__":
    main()
