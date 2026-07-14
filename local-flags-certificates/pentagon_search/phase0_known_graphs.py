#!/usr/bin/env python3
"""
Phase 0 — Theoretical groundwork for the bounded-degree pentagon
conjecture counterexample search.

For each named/constructed graph G, this script computes:
  - n = |V(G)|, Delta = max degree
  - whether G is triangle-free
  - P(G) = number of INDUCED 5-cycles (pentagons)
  - the conjecture ratio    delta(G) = P(G) / (n * Delta^4)
  - comparison against the conjectured 1/80 = 0.0125 and the
    proved 0.02073 (Paper 1, Theorem 3.1).

Pentagon counting (induced 5-cycles): enumerate ordered 5-tuples
(v0,v1,v2,v3,v4) with v0 = min(...), with consecutive adjacencies
v_i ~ v_{i+1 mod 5} present and ALL non-consecutive (the 5 chords)
absent. Divide by 10 to account for the 10 cyclic+reflective
symmetries of C_5.

Equivalent (and what we use, for clarity): iterate over unordered
5-subsets {u0,...,u4} of V(G), and check whether the induced
subgraph is exactly C_5 (5 edges, all degrees 2, connected). On the
small graphs in this table (|G| <= 50) the binomial(50,5)~2.1M cost
is trivial.

Reference: Paper 1 of the project,
  papers/paper1_local_flags_pentagon/main.tex, Section 1 + Section 6.
"""

from __future__ import annotations

import itertools
from fractions import Fraction
from typing import Iterable

import networkx as nx


# ---------------------------------------------------------------- helpers


def is_triangle_free(G: nx.Graph) -> bool:
    for u, v in G.edges():
        nu = set(G.neighbors(u))
        nv = set(G.neighbors(v))
        if (nu & nv):
            return False
    return True


def count_induced_5cycles(G: nx.Graph) -> int:
    """Count induced C_5 subgraphs (pentagons)."""
    verts = list(G.nodes())
    cnt = 0
    adj = {v: set(G.neighbors(v)) for v in verts}
    for sub in itertools.combinations(verts, 5):
        # Check exactly 5 edges among them and all degrees 2 inside.
        edges_inside = 0
        deg_inside = {v: 0 for v in sub}
        for a, b in itertools.combinations(sub, 2):
            if b in adj[a]:
                edges_inside += 1
                deg_inside[a] += 1
                deg_inside[b] += 1
        if edges_inside != 5:
            continue
        if any(d != 2 for d in deg_inside.values()):
            continue
        cnt += 1
    return cnt


# ------------------------------------------------------------ constructors


def blowup_C5(k: int) -> nx.Graph:
    """The balanced (k/2)-blowup of C_5 (k even):

    5 independent supernodes of size k/2 each, arranged in a C_5
    pattern, with all cross-supernode edges between adjacent
    supernodes.

    Result: n = 5k/2, Delta = k, triangle-free, regular.
    """
    assert k % 2 == 0 and k >= 2, "k must be even and >= 2"
    h = k // 2  # supernode size
    G = nx.Graph()
    # supernode i has vertices (i, 0), (i, 1), ..., (i, h-1)
    for i in range(5):
        for j in range(h):
            G.add_node((i, j))
    for i in range(5):
        i2 = (i + 1) % 5
        for j in range(h):
            for jp in range(h):
                G.add_edge((i, j), (i2, jp))
    return G


def generalized_petersen(n: int, k: int) -> nx.Graph:
    """GP(n,k): inner cycle u_0..u_{n-1} with u_i ~ u_{i+k},
    outer cycle v_0..v_{n-1} with v_i ~ v_{i+1}, plus spokes
    u_i ~ v_i. Requires k != n/2.
    """
    G = nx.Graph()
    for i in range(n):
        G.add_node(('u', i))
        G.add_node(('v', i))
    for i in range(n):
        G.add_edge(('v', i), ('v', (i + 1) % n))             # outer cycle
        G.add_edge(('u', i), ('u', (i + k) % n))             # inner edges
        G.add_edge(('u', i), ('v', i))                        # spokes
    return G


def blowup(G: nx.Graph, k: int) -> nx.Graph:
    """k-blowup of G: each vertex v becomes a supernode {(v, 0)...(v, k-1)}
    of size k; each edge (u, v) becomes the complete bipartite graph
    K_{k, k} between the two supernodes (and the supernodes themselves
    are independent sets). n(blowup) = k * n(G); Delta(blowup) = k * Delta(G);
    triangle-free iff G is triangle-free.
    """
    H = nx.Graph()
    for v in G.nodes():
        for j in range(k):
            H.add_node((v, j))
    for u, v in G.edges():
        for j in range(k):
            for jp in range(k):
                H.add_edge((u, j), (v, jp))
    return H


# ------------------------------------------------------------- conjecture


def delta(G: nx.Graph) -> Fraction:
    """delta(G) = P(G) / (|G| * Delta^4) as an exact rational."""
    n = G.number_of_nodes()
    if n == 0:
        return Fraction(0)
    Delta = max(d for _, d in G.degree())
    if Delta == 0:
        return Fraction(0)
    P = count_induced_5cycles(G)
    return Fraction(P, n * Delta ** 4)


def fmt_frac(f: Fraction, digits: int = 5) -> str:
    return f"{float(f):.{digits}f}"


# ----------------------------------------------------------------- table


CONJ_BOUND   = Fraction(1, 80)            # = 0.0125 (Conjecture, Paper 1)
PROVED_BOUND = Fraction(2073, 100_000)    # = 0.02073 (Thm 3.1 tight)


def vs(f: Fraction, target: Fraction) -> str:
    if f == target:
        return "="
    if f < target:
        return "<"
    return "> (!!)"


def row(label: str, G: nx.Graph) -> tuple[str, str]:
    n = G.number_of_nodes()
    if n == 0:
        return label, "empty"
    degs = [d for _, d in G.degree()]
    Delta = max(degs)
    is_reg = all(d == Delta for d in degs)
    tf = is_triangle_free(G)
    if not tf:
        return label, (
            f"| {label} | {n} | {Delta} | N | --- | --- | --- | --- |"
        )
    P = count_induced_5cycles(G)
    d = Fraction(P, n * Delta ** 4) if Delta > 0 else Fraction(0)
    reg_marker = "" if is_reg else " (irreg)"
    return label, (
        f"| {label}{reg_marker} | {n} | {Delta} | Y | {P} | "
        f"{fmt_frac(d, 5)} | {vs(d, CONJ_BOUND)} | {vs(d, PROVED_BOUND)} |"
    )


def main() -> None:
    rows: list[tuple[str, str]] = []

    # 1. (k/2)-blowups of C_5 for k in {4,6,8,10,12}
    for k in (4, 6, 8, 10, 12):
        G = blowup_C5(k)
        rows.append(row(f"(k={k}) (k/2)-blowup C_5", G))

    # 2. Petersen graph
    rows.append(row("Petersen (GP(5,2))", nx.petersen_graph()))

    # 3. Moebius-Kantor (= GP(8,3))
    rows.append(row("Moebius-Kantor (GP(8,3))", nx.moebius_kantor_graph()))

    # 4. Several generalised Petersen graphs (small).
    #    Skip those with triangles.
    gp_cases = [
        (5, 2),   # Petersen
        (6, 2),
        (7, 2),
        (7, 3),
        (8, 3),   # Moebius-Kantor
        (9, 2),
        (9, 3),   # has triangles? check
        (9, 4),
        (10, 2),
        (10, 3),
        (10, 4),  # Desargues
        (11, 2),
        (11, 3),
        (11, 4),
        (12, 5),  # Nauru
        (13, 5),
    ]
    for (n, k) in gp_cases:
        if 2 * k == n:
            continue
        G = generalized_petersen(n, k)
        rows.append(row(f"GP({n},{k})", G))

    # 5. Heawood graph (Fano-plane incidence; n=14, girth 6).
    rows.append(row("Heawood", nx.heawood_graph()))

    # 6. Pappus graph (n=18, girth 6).
    rows.append(row("Pappus", nx.pappus_graph()))

    # 7. Desargues graph (n=20, girth 6).
    rows.append(row("Desargues", nx.desargues_graph()))

    # 8. Dodecahedral graph (n=20, girth 5).
    rows.append(row("Dodecahedron", nx.dodecahedral_graph()))

    # 9. Coxeter graph (n=28, girth 7): omitted — networkx has no built-in
    #    constructor and the natural LCF code [-10,7,-10,7]^7 fails because
    #    the Coxeter graph is non-Hamiltonian. Since Coxeter has girth 7,
    #    P(Coxeter) = 0 anyway, so it is non-informative for the conjecture
    #    table; we skip it.

    # 10. Hoffman-Singleton (n=50, Delta=7, girth 5).
    rows.append(row("Hoffman-Singleton", nx.hoffman_singleton_graph()))

    # 11. A C_5 itself (sanity check) — this is C_5 = (k=2)/2-blowup = identity.
    C5 = nx.cycle_graph(5)
    rows.append(row("C_5", C5))

    # 12. Petersen 2-blowup, 3-blowup — should preserve the Petersen ratio
    #     2/135 = 0.014815 > 1/80, demonstrating that Petersen's
    #     potential counterexample propagates to large Delta.
    rows.append(row("Petersen 2-blowup", blowup(nx.petersen_graph(), 2)))
    #  (k=3 is 30 nodes, choose-5 = 142k — still fast)
    rows.append(row("Petersen 3-blowup", blowup(nx.petersen_graph(), 3)))

    # ------------------------------------------------------------- print
    print("# Phase 0 — known-graph table")
    print()
    print("Conjecture bound (Paper 1): P(G) / (n * Delta^4) <= 1/80 = "
          f"{float(CONJ_BOUND):.5f}.")
    print(f"Proved bound  (Paper 1, Thm 3.1): <= {float(PROVED_BOUND):.5f}.")
    print()
    print("| Graph | n | Delta | TF? | P(G) | P/(n*Delta^4) | vs 1/80 | vs 0.02073 |")
    print("|---|---|---|---|---|---|---|---|")
    for label, line in rows:
        print(line)


if __name__ == "__main__":
    main()
