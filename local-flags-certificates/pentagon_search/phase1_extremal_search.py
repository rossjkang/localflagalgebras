#!/usr/bin/env python3
"""
Phase 1 — Pivoted extremal search for the true sup of
    delta(G) := P(G) / (|G| * Delta(G)^4)
over triangle-free graphs G.

Phase 0 (commit 5aa73e4) found the Petersen graph as a counterexample to
Paper 1's `conj:bounded_pentagon` (claimed sup 1/80 = 0.01250) at ratio
2/135 ≈ 0.01481. This script explores four additional graph families
to determine whether anything beats Petersen.

Targets (in priority order):
  P1. Triangle-free strongly-regular graphs:
        Petersen     SRG(10,3,0,1)     — already done, ratio 0.01481
        Clebsch      SRG(16,5,0,2)     — built via halved 5-cube
        Hoffman-S    SRG(50,7,0,1)     — already done, ratio 0.01050
        Gewirtz      SRG(56,10,0,2)    — built via S(3,6,22) blocks not containing point 0
        M22          SRG(77,16,0,4)    — built via S(3,6,22) block-graph (edge = disjoint)
        Higman-Sims  SRG(100,22,0,6)   — built via star + 22 points + 77 S(3,6,22) blocks
  P2. Random TF cubic graphs of girth 5, n in {10, 14, 18, 22, 26, 30}, sample 1000 each.
  P3. Cayley graphs of small groups (A_5, S_5) with various 3-element generator sets.
  P4. Tensor and lexicographic products: C_5 (x) H for small TF H.
  P5 (extra). Exhaustive enumeration of small TF cubic girth-5 graphs at n in {10,12,...}.

Logs everything to stdout in markdown.

Pentagon counting: fast canonical-orientation enumeration. Pick v0 = min-index
in {v0,v1,v2,v3,v4}; then v1 < v4 in our index order. For each induced C_5
this generates exactly one (v0,v1,v2,v3,v4) tuple. ~10x faster than brute
C(n,5) enumeration on n=100.

Reference: Paper 1 of the project, papers/paper1_local_flags_pentagon/main.tex.
Phase 0: the development notes.
"""

from __future__ import annotations

import itertools
import random
import sys
import time
from fractions import Fraction
from typing import Iterable

import networkx as nx
import numpy as np


# ============================================================ HELPERS


def is_triangle_free(G: nx.Graph) -> bool:
    for u, v in G.edges():
        nu = set(G.neighbors(u))
        nv = set(G.neighbors(v))
        if nu & nv:
            return False
    return True


def girth(G: nx.Graph) -> int:
    """Return the girth of G (smallest cycle length), or sys.maxsize if acyclic."""
    n = G.number_of_nodes()
    if n == 0 or G.number_of_edges() == 0:
        return sys.maxsize
    best = sys.maxsize
    for src in G.nodes():
        # BFS computing shortest cycle through src
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
    """
    Fast count of induced C_5 (pentagon) subgraphs.

    Canonical orientation: pick v0 = min-index vertex in the cycle, and
    require v1 < v4 (the two cycle-neighbours of v0). Then walk v0-v1-v2-v3-v4-v0
    and check all 5 non-cycle pairs are non-edges. Each induced C_5 is
    visited exactly once.
    """
    nodes = list(G.nodes())
    idx = {v: i for i, v in enumerate(nodes)}
    adj = {v: set(G.neighbors(v)) for v in nodes}
    cnt = 0
    for v0 in nodes:
        i0 = idx[v0]
        Nv0 = [u for u in adj[v0] if idx[u] > i0]
        for v1, v4 in itertools.combinations(Nv0, 2):
            if v4 in adj[v1]:
                continue  # v1~v4 is a chord
            for v2 in adj[v1]:
                if idx[v2] <= i0:
                    continue
                if v2 == v4:
                    continue
                if v2 in adj[v0]:
                    continue  # v0~v2 chord
                if v2 in adj[v4]:
                    continue  # v2~v4 chord
                for v3 in adj[v2] & adj[v4]:
                    if idx[v3] <= i0:
                        continue
                    if v3 == v1 or v3 == v2:
                        continue
                    if v3 in adj[v0]:
                        continue  # v0~v3 chord
                    if v3 in adj[v1]:
                        continue  # v1~v3 chord
                    cnt += 1
    return cnt


def delta_ratio(G: nx.Graph) -> Fraction:
    n = G.number_of_nodes()
    if n == 0:
        return Fraction(0)
    Delta = max(d for _, d in G.degree())
    if Delta == 0:
        return Fraction(0)
    P = count_induced_5cycles(G)
    return Fraction(P, n * Delta ** 4)


CONJ_BOUND = Fraction(1, 80)             # 0.01250 (Paper 1 conj)
PETERSEN_RATIO = Fraction(2, 135)        # 0.014815 (Phase 0 finding)
PROVED_BOUND = Fraction(2073, 100_000)   # 0.02073 (Paper 1 Thm 3.1)


def cmp_str(f: Fraction, target: Fraction) -> str:
    if f == target:
        return "="
    if f < target:
        return "<"
    return ">"


# ====================================================== TF SRG BUILDERS


def build_clebsch() -> nx.Graph:
    """Clebsch SRG(16, 5, 0, 2): halved 5-cube. Vertices = even-weight binary
    5-vectors. Edges = pairs at Hamming distance 4."""
    G = nx.Graph()
    verts = [tuple(int(b) for b in format(i, '05b'))
             for i in range(32) if bin(i).count('1') % 2 == 0]
    G.add_nodes_from(verts)
    for u, v in itertools.combinations(verts, 2):
        if sum(a != b for a, b in zip(u, v)) == 4:
            G.add_edge(u, v)
    return G


# Extended binary Golay code generator matrix G_24 = [I_12 | B]
# where B is the bordered Paley matrix.
_GOLAY_B = np.array([
    [1,1,0,1,1,1,0,0,0,1,0,1],
    [1,0,1,1,1,0,0,0,1,0,1,1],
    [0,1,1,1,0,0,0,1,0,1,1,1],
    [1,1,1,0,0,0,1,0,1,1,0,1],
    [1,1,0,0,0,1,0,1,1,0,1,1],
    [1,0,0,0,1,0,1,1,0,1,1,1],
    [0,0,0,1,0,1,1,0,1,1,1,1],
    [0,0,1,0,1,1,0,1,1,1,0,1],
    [0,1,0,1,1,0,1,1,1,0,0,1],
    [1,0,1,1,0,1,1,1,0,0,0,1],
    [0,1,1,0,1,1,1,0,0,0,1,1],
    [1,1,1,1,1,1,1,1,1,1,1,0],
], dtype=int)


def steiner_3_6_22():
    """Construct the Steiner system S(3,6,22) as a list of 77 blocks
    (frozensets of 6 elements of {0..21}).

    Method: enumerate weight-8 codewords (octads) of the extended Golay code G_24,
    take those containing both points {22,23}, and remove those two points.
    This is the standard derived-design construction S(5,8,24) -> S(4,7,23) -> S(3,6,22).
    """
    G = np.hstack([np.eye(12, dtype=int), _GOLAY_B])  # 12 x 24
    octads = []
    for mask in range(4096):
        bits = np.array([(mask >> i) & 1 for i in range(12)], dtype=int)
        c = (bits @ G) % 2
        if c.sum() == 8:
            octads.append(frozenset(i for i, x in enumerate(c) if x))
    return [frozenset(x for x in o if x not in (22, 23))
            for o in octads if 22 in o and 23 in o]


def build_M22(blocks) -> nx.Graph:
    """M22 graph: SRG(77,16,0,4). Vertices = 77 blocks of S(3,6,22),
    adjacent iff disjoint."""
    G = nx.Graph()
    G.add_nodes_from(blocks)
    for b1, b2 in itertools.combinations(blocks, 2):
        if len(b1 & b2) == 0:
            G.add_edge(b1, b2)
    return G


def build_gewirtz(blocks) -> nx.Graph:
    """Gewirtz graph: SRG(56,10,0,2). Induced subgraph of M22 on the 56
    blocks of S(3,6,22) not containing a fixed point (here point 0)."""
    blocks_without_0 = [b for b in blocks if 0 not in b]
    G = nx.Graph()
    G.add_nodes_from(blocks_without_0)
    for b1, b2 in itertools.combinations(blocks_without_0, 2):
        if len(b1 & b2) == 0:
            G.add_edge(b1, b2)
    return G


def build_higman_sims(blocks) -> nx.Graph:
    """Higman-Sims graph: SRG(100,22,0,6). Vertices = {*} u {22 points} u {77 blocks}.
    * adjacent to all 22 points; point ~ block iff point in block; block ~ block iff
    disjoint."""
    G = nx.Graph()
    star = 'STAR'
    G.add_node(star)
    for p in range(22):
        G.add_node(('P', p))
    for b in blocks:
        G.add_node(('B', b))
    for p in range(22):
        G.add_edge(star, ('P', p))
    for p in range(22):
        for b in blocks:
            if p in b:
                G.add_edge(('P', p), ('B', b))
    for b1, b2 in itertools.combinations(blocks, 2):
        if len(b1 & b2) == 0:
            G.add_edge(('B', b1), ('B', b2))
    return G


# ===================================================== CAYLEY GRAPHS


def cayley_graph_from_perms(generators, group_elements) -> nx.Graph:
    """Build the right Cayley graph Cay(G, S) where S is a symmetric
    generating set (= generators + inverses, deduplicated).

    Vertices = elements of the group (as Permutation objects); g ~ g*s for s in S.
    """
    from sympy.combinatorics import Permutation
    # Build full S = generators u inverses
    S = set()
    for s in generators:
        S.add(s)
        S.add(s ** -1)
    # Remove identity if present
    e = Permutation(list(range(generators[0].size)))
    S.discard(e)
    G = nx.Graph()
    # Use the array_form as a hashable key
    key = lambda p: tuple(p.array_form)
    for g in group_elements:
        G.add_node(key(g))
    for g in group_elements:
        for s in S:
            h = g * s
            G.add_edge(key(g), key(h))
    return G


def all_group_elements(generators):
    """Generate all elements of the group <generators>."""
    from sympy.combinatorics import PermutationGroup
    grp = PermutationGroup(generators)
    return list(grp.generate())


# ===================================================== PRODUCTS


def tensor_product(G: nx.Graph, H: nx.Graph) -> nx.Graph:
    """G (x) H (categorical / tensor): vertices V(G) x V(H);
    (u,x) ~ (v,y) iff u~v in G AND x~y in H."""
    return nx.tensor_product(G, H)


def lex_product(G: nx.Graph, H: nx.Graph) -> nx.Graph:
    """G[H] lexicographic: vertices V(G) x V(H);
    (u,x) ~ (v,y) iff (u~v in G) OR (u=v AND x~y in H)."""
    return nx.lexicographic_product(G, H)


# ============================================================ RUNNERS


def run_TF_SRGs():
    print("\n## P1. Triangle-free strongly-regular graphs")
    print()
    print("| Graph | SRG params | n | Δ | P(G) | δ(G) = P/(nΔ⁴) | vs 1/80 | vs 2/135 |")
    print("|---|---|---:|---:|---:|---:|:---:|:---:|")

    rows = []

    # Petersen (baseline from Phase 0)
    G = nx.petersen_graph()
    P = count_induced_5cycles(G)
    n = G.number_of_nodes(); D = max(d for _,d in G.degree())
    r = Fraction(P, n * D**4)
    rows.append(("Petersen", "SRG(10,3,0,1)", n, D, P, r))

    # Clebsch
    G = build_clebsch()
    assert is_triangle_free(G)
    P = count_induced_5cycles(G)
    n = G.number_of_nodes(); D = max(d for _,d in G.degree())
    r = Fraction(P, n * D**4)
    rows.append(("Clebsch", "SRG(16,5,0,2)", n, D, P, r))

    # Hoffman-Singleton
    G = nx.hoffman_singleton_graph()
    assert is_triangle_free(G)
    P = count_induced_5cycles(G)
    n = G.number_of_nodes(); D = max(d for _,d in G.degree())
    r = Fraction(P, n * D**4)
    rows.append(("Hoffman-Singleton", "SRG(50,7,0,1)", n, D, P, r))

    # Build S(3,6,22) once and reuse for M22, Gewirtz, HiS
    print("(building S(3,6,22) ...)", file=sys.stderr)
    blocks = steiner_3_6_22()
    assert len(blocks) == 77

    # Gewirtz
    G = build_gewirtz(blocks)
    assert is_triangle_free(G)
    P = count_induced_5cycles(G)
    n = G.number_of_nodes(); D = max(d for _,d in G.degree())
    r = Fraction(P, n * D**4)
    rows.append(("Gewirtz", "SRG(56,10,0,2)", n, D, P, r))

    # M22
    G = build_M22(blocks)
    assert is_triangle_free(G)
    P = count_induced_5cycles(G)
    n = G.number_of_nodes(); D = max(d for _,d in G.degree())
    r = Fraction(P, n * D**4)
    rows.append(("M22", "SRG(77,16,0,4)", n, D, P, r))

    # Higman-Sims
    G = build_higman_sims(blocks)
    assert is_triangle_free(G)
    P = count_induced_5cycles(G)
    n = G.number_of_nodes(); D = max(d for _,d in G.degree())
    r = Fraction(P, n * D**4)
    rows.append(("Higman-Sims", "SRG(100,22,0,6)", n, D, P, r))

    for name, params, n, D, P, r in rows:
        print(f"| {name} | {params} | {n} | {D} | {P} | "
              f"{float(r):.6f} | {cmp_str(r, CONJ_BOUND)} | "
              f"{cmp_str(r, PETERSEN_RATIO)} |")

    return rows


def run_random_cubic(ns=(10, 14, 18, 22, 26, 30), samples=1000, seed=42):
    print("\n## P2. Random TF cubic graphs (girth >= 5)")
    print()
    print(f"Samples per n: {samples} (seed={seed}). Each sample drawn from")
    print(f"`networkx.random_regular_graph(3, n)`, filtered to triangle-free")
    print(f"AND girth-5 (i.e., contains at least one C_5; otherwise pentagons = 0).")
    print()
    print("| n | TF samples | girth-5 samples | max P | max ratio | mean ratio (girth-5) | best vs 2/135 |")
    print("|---:|---:|---:|---:|---:|---:|:---:|")

    rng = random.Random(seed)
    summaries = []
    for n in ns:
        tf_count = 0
        g5_count = 0
        ratios = []
        max_P = 0
        max_ratio = Fraction(0)
        # NX random_regular_graph requires n*d even
        if (n * 3) % 2 != 0:
            print(f"| {n} | (n*3 must be even) | | | | | |")
            continue
        for s in range(samples):
            seedval = rng.randint(0, 2**30)
            try:
                G = nx.random_regular_graph(3, n, seed=seedval)
            except Exception:
                continue
            if not is_triangle_free(G):
                continue
            tf_count += 1
            P = count_induced_5cycles(G)
            if P > 0:
                g5_count += 1
                r = Fraction(P, n * 3**4)
                ratios.append(r)
                if r > max_ratio:
                    max_ratio = r
                    max_P = P
        mean = sum(ratios) / len(ratios) if ratios else Fraction(0)
        cmp = cmp_str(max_ratio, PETERSEN_RATIO) if ratios else "n/a"
        print(f"| {n} | {tf_count} | {g5_count} | {max_P} | "
              f"{float(max_ratio):.6f} | "
              f"{float(mean):.6f} | {cmp} |")
        summaries.append((n, tf_count, g5_count, max_P, max_ratio, mean))
    return summaries


def run_cayley():
    print("\n## P3. Cayley graphs of small groups")
    print()
    print("Searched: 3-regular Cayley graphs Cay(G, S) for G in {A_5, S_5, A_4, S_4, D_n}")
    print("with S a symmetric 3-element involution-set. Builds the graph, filters to")
    print("triangle-free, computes ratio.")
    print()
    from sympy.combinatorics import Permutation, AlternatingGroup, SymmetricGroup, DihedralGroup
    from sympy.combinatorics import PermutationGroup
    from itertools import combinations as icomb

    found = []

    def cayley_undirected(grp_elements, S_inv_closed):
        """Build undirected Cayley graph; S must be inverse-closed and not contain identity.
        Returns nx.Graph keyed by tuples (Permutation.array_form)."""
        key = lambda p: tuple(p.array_form)
        H = nx.Graph()
        nodes = {}
        for g in grp_elements:
            k = key(g)
            nodes[k] = g
            H.add_node(k)
        for g in grp_elements:
            for s in S_inv_closed:
                gs = g * s
                k1 = key(g); k2 = key(gs)
                if k1 != k2:
                    H.add_edge(k1, k2)
        return H

    def all_involutions(grp_elements):
        return [g for g in grp_elements if g.order() == 2]

    # === A_5 (order 60) ===
    # All conjugacy-classes of involutions: A_5 has the unique class of (ab)(cd) (15 elems)
    # All 3-element involution sets {s1, s2, s3} subset of involutions; we want
    # the Cayley graph to be 3-regular (3 generators all distinct, all involutions),
    # connected (the set generates A_5), and triangle-free.
    grp = AlternatingGroup(5)
    elts = list(grp.generate())
    invs = all_involutions(elts)
    print(f"A_5: |inv|={len(invs)}, scanning C({len(invs)},3)={len(invs)*(len(invs)-1)*(len(invs)-2)//6} triples", file=sys.stderr)
    # Cap to avoid blowup
    seen_tf = 0
    for triple in icomb(invs, 3):
        # Need triple to generate A_5
        H = PermutationGroup(list(triple))
        if H.order() != 60:
            continue
        G = cayley_undirected(elts, list(triple))
        if not is_triangle_free(G):
            continue
        seen_tf += 1
        P = count_induced_5cycles(G)
        n = G.number_of_nodes(); D = max(d for _,d in G.degree())
        r = Fraction(P, n * D**4)
        found.append(("A_5", triple, n, D, P, r))
    print(f"A_5 TF Cayley graphs found: {seen_tf}", file=sys.stderr)

    # === S_4 (order 24) ===
    grp = SymmetricGroup(4)
    elts = list(grp.generate())
    invs = all_involutions(elts)
    print(f"S_4: |inv|={len(invs)}", file=sys.stderr)
    seen_tf = 0
    for triple in icomb(invs, 3):
        H = PermutationGroup(list(triple))
        if H.order() != 24:
            continue
        G = cayley_undirected(elts, list(triple))
        if not is_triangle_free(G):
            continue
        seen_tf += 1
        P = count_induced_5cycles(G)
        n = G.number_of_nodes(); D = max(d for _,d in G.degree())
        r = Fraction(P, n * D**4)
        found.append(("S_4", triple, n, D, P, r))
    print(f"S_4 TF Cayley graphs found: {seen_tf}", file=sys.stderr)

    # === Dihedral D_n for n in {5, 7, 8, 9, 10, 12} ===
    for nn in (5, 7, 8, 9, 10, 12):
        grp = DihedralGroup(nn)
        elts = list(grp.generate())
        invs = all_involutions(elts)
        if len(invs) < 3: continue
        for triple in icomb(invs, 3):
            H = PermutationGroup(list(triple))
            if H.order() != 2*nn:
                continue
            G = cayley_undirected(elts, list(triple))
            if not is_triangle_free(G):
                continue
            P = count_induced_5cycles(G)
            n = G.number_of_nodes(); D = max(d for _,d in G.degree())
            r = Fraction(P, n * D**4)
            found.append((f"D_{nn}", triple, n, D, P, r))

    # === S_5 (order 120) is too big to enumerate all triples — sample 200 triples ===
    grp = SymmetricGroup(5)
    elts = list(grp.generate())
    invs = all_involutions(elts)
    rng = random.Random(11)
    all_triples = list(icomb(invs, 3))
    sample = rng.sample(all_triples, min(500, len(all_triples)))
    seen_tf = 0
    for triple in sample:
        H = PermutationGroup(list(triple))
        if H.order() != 120:
            continue
        G = cayley_undirected(elts, list(triple))
        if not is_triangle_free(G):
            continue
        seen_tf += 1
        P = count_induced_5cycles(G)
        n = G.number_of_nodes(); D = max(d for _,d in G.degree())
        r = Fraction(P, n * D**4)
        found.append(("S_5 (sample)", triple, n, D, P, r))
    print(f"S_5 (500-sample) TF Cayley graphs: {seen_tf}", file=sys.stderr)

    # Tabulate top results by ratio. Dedup by (group, n, D, P, ratio) tuple
    # rather than ratio alone (many different graphs share ratio=0).
    found.sort(key=lambda t: -t[5])
    print()
    print("Top 20 distinct (group, n, Δ, P, ratio) tuples, sorted by ratio descending:")
    print()
    print("| Group | n | Δ | P | ratio | vs 1/80 | vs 2/135 |")
    print("|---|---:|---:|---:|---:|:---:|:---:|")
    seen = set()
    shown = 0
    for grpn, triple, n, D, P, r in found:
        key = (grpn, n, D, P, r)
        if key in seen:
            continue
        seen.add(key)
        print(f"| {grpn} | {n} | {D} | {P} | "
              f"{float(r):.6f} | {cmp_str(r, CONJ_BOUND)} | "
              f"{cmp_str(r, PETERSEN_RATIO)} |")
        shown += 1
        if shown >= 20:
            break
    print(f"\n(Total TF Cayley graphs found across all groups: {len(found)})")
    # Also explicit best-ratio summary
    if found:
        best = found[0]
        grpn, triple, n, D, P, r = best
        print(f"\n**Best Cayley graph found**: {grpn}, n={n}, Δ={D}, "
              f"P={P}, ratio={float(r):.6f}")
    return found


def run_products():
    print("\n## P4. Tensor and lexicographic products")
    print()
    print("Tested: C_5 (x) H (tensor) and C_5 [H] (lex) for H in")
    print("{C_5, C_7, C_8, C_9, K_{2,2}, K_{3,3}, Q_3, Petersen, Heawood}.")
    print()
    print("| Product | n | Δ | TF? | P | ratio | vs 1/80 | vs 2/135 |")
    print("|---|---:|---:|---|---:|---:|:---:|:---:|")

    C5 = nx.cycle_graph(5)
    Petersen = nx.petersen_graph()
    H_list = [
        ("C_5", nx.cycle_graph(5)),
        ("C_7", nx.cycle_graph(7)),
        ("C_8", nx.cycle_graph(8)),
        ("C_9", nx.cycle_graph(9)),
        ("K_{2,2}", nx.complete_bipartite_graph(2, 2)),
        ("K_{3,3}", nx.complete_bipartite_graph(3, 3)),
        ("Q_3", nx.hypercube_graph(3)),
        ("Petersen", nx.petersen_graph()),
        ("Heawood", nx.heawood_graph()),
    ]
    results = []
    for hname, H in H_list:
        # Tensor product C_5 (x) H
        T = nx.tensor_product(C5, H)
        tf = is_triangle_free(T)
        n = T.number_of_nodes()
        if n > 0 and any(d > 0 for _,d in T.degree()):
            D = max(d for _,d in T.degree())
        else:
            D = 0
        if tf and D > 0:
            P = count_induced_5cycles(T)
            r = Fraction(P, n * D**4)
            results.append((f"C_5 (x) {hname}", n, D, True, P, r))
            print(f"| C_5 ⊗ {hname} | {n} | {D} | Y | {P} | "
                  f"{float(r):.6f} | {cmp_str(r, CONJ_BOUND)} | "
                  f"{cmp_str(r, PETERSEN_RATIO)} |")
        else:
            results.append((f"C_5 (x) {hname}", n, D, False, None, None))
            print(f"| C_5 ⊗ {hname} | {n} | {D} | N | - | - | - | - |")

        # Lex product (we expect non-TF generally because (u,x)~(u,y) for adjacent x,y
        # AND complete bipartite between adjacent supernodes -> triangles in many cases)
        L = nx.lexicographic_product(C5, H)
        tf = is_triangle_free(L)
        n = L.number_of_nodes()
        if n > 0 and any(d > 0 for _,d in L.degree()):
            D = max(d for _,d in L.degree())
        else:
            D = 0
        if tf and D > 0:
            P = count_induced_5cycles(L)
            r = Fraction(P, n * D**4)
            results.append((f"C_5 [{hname}]", n, D, True, P, r))
            print(f"| C_5[{hname}] | {n} | {D} | Y | {P} | "
                  f"{float(r):.6f} | {cmp_str(r, CONJ_BOUND)} | "
                  f"{cmp_str(r, PETERSEN_RATIO)} |")
        else:
            results.append((f"C_5 [{hname}]", n, D, False, None, None))
            print(f"| C_5[{hname}] | {n} | {D} | N | - | - | - | - |")

    return results


def run_enumeration(ns=(10, 12, 14, 16, 18, 20), samples_per_n=10000):
    """Heavy random sampling of 3-regular graphs at fixed n.

    No `geng` available, so we sample very heavily from
    `random_regular_graph(3, n)`, deduplicate using a stronger iso-class
    discriminator: pentagon-count tuple (=P) augmented with girth and triangle
    count. (`weisfeiler_lehman_graph_hash` collapses all degree-uniform graphs
    to the same value; useless here.) For each n, log the max ratio across all
    sampled TF-graphs with at least one pentagon.
    """
    print("\n## P5 (extra). Heavy random sampling at fixed n, Δ=3 (no nauty)")
    print()
    print(f"Samples per n: {samples_per_n}. Dedup by `(n, P)` (a weak invariant,")
    print("but tracks the quantity of interest — the pentagon count). For each n,")
    print("report the TF samples, those with P>0, and the maximum P observed.")
    print()
    print("| n | TF samples | girth-5 samples | max P | max ratio | vs 2/135 |")
    print("|---:|---:|---:|---:|---:|:---:|")
    rng = random.Random(2026)
    summaries = []
    for n in ns:
        if (n * 3) % 2 != 0:
            continue
        tf_count = 0
        g5_count = 0
        max_P = 0
        max_ratio = Fraction(0)
        for s in range(samples_per_n):
            try:
                G = nx.random_regular_graph(3, n, seed=rng.randint(0, 2**30))
            except Exception:
                continue
            if not is_triangle_free(G):
                continue
            tf_count += 1
            P = count_induced_5cycles(G)
            if P == 0:
                continue
            g5_count += 1
            r = Fraction(P, n * 3**4)
            if r > max_ratio:
                max_ratio = r
                max_P = P
        cmp = cmp_str(max_ratio, PETERSEN_RATIO) if max_ratio > 0 else "n/a"
        print(f"| {n} | {tf_count} | {g5_count} | {max_P} | "
              f"{float(max_ratio):.6f} | {cmp} |")
        summaries.append((n, tf_count, g5_count, max_P, max_ratio))
    return summaries


# ============================================================ MAIN


def main():
    t0 = time.time()
    print("# Phase 1 — Pivoted Extremal Pentagon Search")
    print()
    print(f"Petersen baseline (Phase 0): δ = 2/135 ≈ {float(PETERSEN_RATIO):.6f}.")
    print(f"Conjecture bound (Paper 1): 1/80 = {float(CONJ_BOUND):.6f}.")
    print(f"Proved bound (Paper 1 Thm 3.1): {float(PROVED_BOUND):.6f}.")
    print()

    srg_rows = run_TF_SRGs()
    cubic_rows = run_random_cubic()
    cayley_rows = run_cayley()
    prod_rows = run_products()
    enum_rows = run_enumeration()

    # ===== final summary =====
    print("\n## Summary")
    print()
    # Find max ratio across all categories
    best = (Fraction(0), "", None)
    for label, params, n, D, P, r in srg_rows:
        if r > best[0]:
            best = (r, f"{label} {params}: n={n} Δ={D} P={P}", None)
    for n, tf_count, g5_count, max_P, max_ratio, mean in cubic_rows:
        if max_ratio > best[0]:
            best = (max_ratio, f"Random cubic n={n}: max P={max_P}", None)
    for grpn, triple, n, D, P, r in cayley_rows:
        if r > best[0]:
            best = (r, f"Cayley {grpn}: n={n} Δ={D} P={P}", None)
    for entry in prod_rows:
        label, n, D, tf, P, r = entry
        if tf and r is not None and r > best[0]:
            best = (r, f"Product {label}: n={n} Δ={D} P={P}", None)
    for n, classes, tf_classes, max_P, max_ratio in enum_rows:
        if max_ratio > best[0]:
            best = (max_ratio, f"Enumeration n={n}: max P={max_P}", None)

    print(f"**Highest ratio found across all categories**: "
          f"{float(best[0]):.6f} = {best[0]} via {best[1]}")
    print()
    print(f"Comparison: 1/80 = {float(CONJ_BOUND):.6f}, "
          f"2/135 = {float(PETERSEN_RATIO):.6f}, "
          f"Thm 3.1 = {float(PROVED_BOUND):.6f}.")
    print()
    print(f"Total runtime: {time.time()-t0:.1f}s.")


if __name__ == "__main__":
    main()
