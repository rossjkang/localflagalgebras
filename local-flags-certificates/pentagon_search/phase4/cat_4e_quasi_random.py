#!/usr/bin/env python3
"""
Phase 4 — sub-category 4e: quasi-random TF constructions.

  - Halved hypercubes ½Q_n for n in {5, 6, 7, 8}: ½Q_5 = Clebsch (n=16);
    ½Q_6 (n=32, Δ=15); ½Q_7 (n=64, Δ=21); ½Q_8 (n=128, Δ=28).
  - Cayley graphs of Z_2^n with C_4-free connection sets.
  - Bilinear forms graphs H(d, q).
  - Hamming graphs H(d, q) for q >= 3.
  - Twisted-Clebsch / blowup-of-Clebsch comparisons.

The halved hypercubes are an important new family — ½Q_6 may extend or
break the Clebsch baseline.
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


# ============================================================ Halved hypercube


def halved_hypercube(d: int) -> nx.Graph:
    """½Q_d: vertices = even-weight binary d-vectors; edges = pairs at Hamming
    distance 2. (Equivalently, the folded d-cube — well, the halved-cube is
    one variant.)

    Parameters:
      d=5: 16 vertices, 10-regular(?) — actually let me reconsider.

    Two standard "halved cube" definitions:
      (a) vertices = even-weight binary d-vectors (only 2^{d-1} of them),
          edges = Hamming-distance-2.
      (b) vertices = all binary d-vectors, edges = Hamming-distance-2.

    Definition (a) at d=5 gives 16 vertices, each with C(5,2) = 10 neighbours
    BUT only those at Hamming distance 2 from a fixed even-weight vector
    that are also even-weight. From even-weight v, neighbours at Hamming dist
    2 are obtained by flipping any 2 bits — also even weight (since flipping
    2 bits preserves parity). So degree = C(5,2) = 10? No — for d=5, the
    Clebsch is 5-regular not 10-regular.

    The Clebsch graph is the "folded 5-cube": vertices = binary 5-vectors
    modulo the all-ones vector, so 2^4 = 16 vertices; edges = at Hamming
    distance 1 or 5 (since all-ones is identified). Vertex has 5 neighbours.

    Use this definition:
      Folded d-cube: 2^{d-1} vertices, d-regular, TF iff d >= 5.
      Clebsch = folded 5-cube.
    """
    n_verts = 1 << (d - 1)
    verts = list(range(n_verts))
    # Each vertex v (0..2^{d-1}-1) represents the pair {v, v XOR (2^d - 1)}.
    # Two vertices u, v are adjacent iff their representatives differ in
    # Hamming distance 1 or d-1 (which after folding becomes 1).
    G = nx.Graph()
    G.add_nodes_from(verts)
    mask = (1 << d) - 1
    for u in verts:
        for bit in range(d):
            v_raw = u ^ (1 << bit)
            # Fold: pick smaller representative.
            v_alt = v_raw ^ mask
            v = min(v_raw, v_alt) & ((1 << (d - 1)) - 1) if v_raw >= n_verts else v_raw
            # Simpler: representative = v_raw if v_raw < n_verts else v_raw XOR mask
            if v_raw < n_verts:
                vrep = v_raw
            else:
                vrep = v_raw ^ mask
            if vrep != u:
                G.add_edge(u, vrep)
    return G


def halved_5cube_alt() -> nx.Graph:
    """Alternative Clebsch via halved 5-cube: even-weight binary 5-vectors,
    edge iff Hamming distance 4 (= 4 = 5-1). Should be equivalent."""
    verts = []
    for v in range(1 << 5):
        if bin(v).count("1") % 2 == 0:
            verts.append(v)
    G = nx.Graph()
    G.add_nodes_from(verts)
    for u, v in itertools.combinations(verts, 2):
        if bin(u ^ v).count("1") == 4:
            G.add_edge(u, v)
    return G


def folded_n_cube(d: int) -> nx.Graph:
    """Standard folded d-cube: 2^{d-1} vertices, d-regular.
    TF iff d >= 5; for d=5 it is Clebsch."""
    if d < 2:
        raise ValueError("d must be >= 2")
    n_verts = 1 << (d - 1)
    mask = (1 << d) - 1
    G = nx.Graph()
    G.add_nodes_from(range(n_verts))
    for u in range(n_verts):
        for bit in range(d):
            v_raw = u ^ (1 << bit)
            v = v_raw if v_raw < n_verts else v_raw ^ mask
            if v != u:
                G.add_edge(u, v)
    return G


# ============================================================ Hamming / bilinear


def hamming_graph(d: int, q: int) -> nx.Graph:
    """H(d, q): vertices = words in {0..q-1}^d, edges = words at Hamming dist 1."""
    verts = list(itertools.product(range(q), repeat=d))
    idx = {v: i for i, v in enumerate(verts)}
    G = nx.Graph()
    G.add_nodes_from(range(len(verts)))
    for i, v in enumerate(verts):
        for pos in range(d):
            for c in range(q):
                if c == v[pos]:
                    continue
                w = list(v)
                w[pos] = c
                w = tuple(w)
                G.add_edge(i, idx[w])
    return G


def shrikhande_graph() -> nx.Graph:
    """Shrikhande graph (n=16, 6-regular, SRG(16,6,2,2)). NOT TF (λ=2).
    Included for log; will report TF=0."""
    # Cayley graph of Z_4 x Z_4 with connection set {(±1,0), (0,±1), (±1,±1)}.
    n = 16
    G = nx.Graph()
    G.add_nodes_from(range(n))
    def idx(a, b):
        return (a % 4) * 4 + (b % 4)
    for a in range(4):
        for b in range(4):
            u = idx(a, b)
            for da, db in [(1, 0), (-1, 0), (0, 1), (0, -1),
                            (1, 1), (-1, -1)]:
                v = idx(a + da, b + db)
                if v != u:
                    G.add_edge(u, v)
    return G


def blowup_graph(H: nx.Graph, k: int) -> nx.Graph:
    """k-blowup of H: replace each vertex with an independent set of size k.
    Two clones of u and v are adjacent iff uv is an edge of H.

    For TF H, the blowup is still TF: any potential triangle would need
    three vertices x, y, z forming a triangle; their part-classes lie
    in u, v, w (possibly with repeats). Since clones in the same part
    are independent, the triangle must lie across 3 distinct parts,
    requiring u, v, w to form a triangle in H — contradiction.
    """
    G = nx.Graph()
    n = H.number_of_nodes()
    for v in H.nodes():
        for i in range(k):
            G.add_node((v, i))
    for u, v in H.edges():
        for i in range(k):
            for j in range(k):
                G.add_edge((u, i), (v, j))
    return G


# ============================================================ Driver


def run(tsv_path: str):
    f = open_tsv(tsv_path, append=True)
    results = []

    # ---- folded n-cubes ----
    for d in [5, 6, 7, 8]:
        try:
            G = folded_n_cube(d)
            tf, r, P = tsv_row(f, "4e_FoldedCube", f"Q_{d}_folded", G)
            n, D, m, _, gv = graph_stats(G)
            gout = gv if gv != sys.maxsize else -1
            print(f"[4e] FoldedCube Q_{d}: n={n} Δ={D} m={m} girth={gout} "
                  f"TF={int(tf)} P={P} ratio={float(r):.6f} ({vs_clebsch(r)})")
            results.append((f"FoldedCube Q_{d}", n, D, P, r))
        except Exception as e:
            print(f"[4e] FoldedCube Q_{d}: FAILED {e}")

    # ---- Hamming graphs (these have triangles for q >= 3) ----
    for (d, q) in [(2, 3), (3, 3), (2, 4)]:
        try:
            G = hamming_graph(d, q)
            tf, r, P = tsv_row(f, "4e_Hamming", f"H({d},{q})", G)
            n, D, m, _, gv = graph_stats(G)
            gout = gv if gv != sys.maxsize else -1
            print(f"[4e] H({d},{q}): n={n} Δ={D} girth={gout} TF={int(tf)} "
                  f"P={P} ratio={float(r):.6f} ({vs_clebsch(r)})")
            results.append((f"H({d},{q})", n, D, P, r))
        except Exception as e:
            print(f"[4e] H({d},{q}): FAILED {e}")

    # ---- Shrikhande (not TF, but check) ----
    G = shrikhande_graph()
    tf, r, P = tsv_row(f, "4e_Shrikhande", "Shrikhande", G)
    n, D, m, _, gv = graph_stats(G)
    print(f"[4e] Shrikhande: n={n} Δ={D} TF={int(tf)} P={P} ratio={float(r):.6f}")

    # ---- Clebsch blowups (verify ratio preservation) ----
    clebsch = folded_n_cube(5)
    for k in [2, 3, 4]:
        G = blowup_graph(clebsch, k)
        tf, r, P = tsv_row(f, "4e_ClebschBlowup", f"Clebsch_blowup_k{k}", G)
        n, D, m, _, gv = graph_stats(G)
        gout = gv if gv != sys.maxsize else -1
        print(f"[4e] Clebsch_blowup_k{k}: n={n} Δ={D} m={m} girth={gout} "
              f"TF={int(tf)} P={P} ratio={float(r):.6f} ({vs_clebsch(r)})")
        results.append((f"ClebschBlowup_k{k}", n, D, P, r))

    # ---- C_5 blowups (sanity) ----
    c5 = nx.cycle_graph(5)
    for k in [2, 3, 4, 6]:
        G = blowup_graph(c5, k)
        tf, r, P = tsv_row(f, "4e_C5Blowup", f"C5_blowup_k{k}", G)
        n, D, m, _, gv = graph_stats(G)
        gout = gv if gv != sys.maxsize else -1
        print(f"[4e] C5_blowup_k{k}: n={n} Δ={D} m={m} girth={gout} "
              f"TF={int(tf)} P={P} ratio={float(r):.6f} ({vs_clebsch(r)})")
        results.append((f"C5Blowup_k{k}", n, D, P, r))

    # ---- Petersen blowups (Phase 0 showed Petersen at 2/135; blowups preserve) ----
    pete = nx.petersen_graph()
    for k in [2, 3]:
        G = blowup_graph(pete, k)
        tf, r, P = tsv_row(f, "4e_PetersenBlowup", f"Petersen_blowup_k{k}", G)
        n, D, m, _, gv = graph_stats(G)
        gout = gv if gv != sys.maxsize else -1
        print(f"[4e] Petersen_blowup_k{k}: n={n} Δ={D} m={m} girth={gout} "
              f"TF={int(tf)} P={P} ratio={float(r):.6f} ({vs_clebsch(r)})")
        results.append((f"PetersenBlowup_k{k}", n, D, P, r))

    f.close()
    if results:
        best = max(results, key=lambda t: t[4])
        print(f"\n4e SUMMARY: best ratio = {float(best[4]):.6f} at {best[0]}")
    return results


if __name__ == "__main__":
    tsv = sys.argv[1] if len(sys.argv) > 1 else (
        os.path.join(os.path.dirname(__file__), "..", "phase4_logs", "all_graphs.tsv")
    )
    run(tsv)
