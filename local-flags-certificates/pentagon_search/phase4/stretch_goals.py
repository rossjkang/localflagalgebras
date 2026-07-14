#!/usr/bin/env python3
"""
Phase 4 — stretch goals.

Includes:
  - Bilinear forms graphs at slightly larger parameters
  - Doubly-resolvable Steiner triple systems (block graphs) — skip if too
    complex to construct; instead test other algebraic graphs.
  - Brown-Erdős-Sós polarity graphs (already in 4a, but redo at larger q)
  - Orthogonal-group Cayley graphs (skip; group construction too involved
    for the time budget)

Pragmatic stretch list:
  * Halved Q_d for d up to 10 (n = 2^9 = 512 vertices for d=10)
  * Hamming graphs at q=2, d up to 8 (these are bipartite TF)
  * Hypercube Q_d (just to confirm TF + girth 4 + P=0 for d >= 4)
  * Petersen blowups at k = 4, 5
  * SRG-like graphs: Paley graphs? They are usually not TF.

This script appends rows to phase4_logs/all_graphs.tsv with source='4s_*'.
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
from cat_4e_quasi_random import folded_n_cube, blowup_graph


# ============================================================ Hypercube


def hypercube_graph(d: int) -> nx.Graph:
    """Q_d: vertices = binary d-vectors, edges = Hamming dist 1."""
    return nx.hypercube_graph(d)


# ============================================================ Paley graph (not TF for small q)


def paley_graph(q: int) -> nx.Graph:
    """Paley graph for q ≡ 1 (mod 4), q prime. Self-complementary SRG.
    Usually NOT TF — included for completeness."""
    assert q % 4 == 1, "Paley needs q ≡ 1 (mod 4)"
    # Squares in F_q (q prime)
    sqs = set()
    for x in range(1, q):
        sqs.add((x * x) % q)
    G = nx.Graph()
    G.add_nodes_from(range(q))
    for u in range(q):
        for s in sqs:
            v = (u + s) % q
            if v != u:
                G.add_edge(u, v)
    return G


# ============================================================ Driver


def run(tsv_path: str):
    f = open_tsv(tsv_path, append=True)
    results = []

    # ---- hypercubes ----
    for d in [3, 4, 5, 6, 7, 8, 9]:
        G = hypercube_graph(d)
        tf, r, P = tsv_row(f, "4s_Hypercube", f"Q_{d}", G)
        n, D, m, _, gv = graph_stats(G)
        gout = gv if gv != sys.maxsize else -1
        print(f"[4s] Q_{d}: n={n} Δ={D} m={m} girth={gout} TF={int(tf)} "
              f"P={P} ratio={float(r):.6f} ({vs_clebsch(r)})")
        results.append((f"Q_{d}", n, D, P, r))

    # ---- folded cubes (extend 4e) ----
    for d in [9, 10]:
        try:
            G = folded_n_cube(d)
            tf, r, P = tsv_row(f, "4s_FoldedCube", f"Q_{d}_folded", G)
            n, D, m, _, gv = graph_stats(G)
            gout = gv if gv != sys.maxsize else -1
            print(f"[4s] FoldedCube Q_{d}: n={n} Δ={D} m={m} girth={gout} "
                  f"TF={int(tf)} P={P} ratio={float(r):.6f} ({vs_clebsch(r)})")
            results.append((f"Q_{d}_folded", n, D, P, r))
        except Exception as e:
            print(f"[4s] FoldedCube Q_{d}: FAILED {e}")

    # ---- Paley graphs ----
    for q in [5, 9, 13, 17]:
        if q % 4 != 1:
            continue
        try:
            if q == 9:
                # Paley over GF(9) — skip (needs prime-power)
                continue
            G = paley_graph(q)
            tf, r, P = tsv_row(f, "4s_Paley", f"Paley({q})", G)
            n, D, m, _, gv = graph_stats(G)
            gout = gv if gv != sys.maxsize else -1
            print(f"[4s] Paley({q}): n={n} Δ={D} m={m} girth={gout} "
                  f"TF={int(tf)} P={P} ratio={float(r):.6f} ({vs_clebsch(r)})")
            results.append((f"Paley({q})", n, D, P, r))
        except Exception as e:
            print(f"[4s] Paley({q}): FAILED {e}")

    # ---- Petersen blowups extended ----
    pete = nx.petersen_graph()
    for k in [4, 5, 6]:
        G = blowup_graph(pete, k)
        tf, r, P = tsv_row(f, "4s_PetersenBlowup", f"Petersen_blowup_k{k}", G)
        n, D, m, _, gv = graph_stats(G)
        gout = gv if gv != sys.maxsize else -1
        print(f"[4s] Petersen_blowup_k{k}: n={n} Δ={D} m={m} girth={gout} "
              f"TF={int(tf)} P={P} ratio={float(r):.6f} ({vs_clebsch(r)})")
        results.append((f"Petersen_blowup_k{k}", n, D, P, r))

    # ---- Clebsch blowup extended ----
    cl = folded_n_cube(5)
    for k in [5, 6]:
        G = blowup_graph(cl, k)
        tf, r, P = tsv_row(f, "4s_ClebschBlowup", f"Clebsch_blowup_k{k}", G)
        n, D, m, _, gv = graph_stats(G)
        gout = gv if gv != sys.maxsize else -1
        print(f"[4s] Clebsch_blowup_k{k}: n={n} Δ={D} m={m} girth={gout} "
              f"TF={int(tf)} P={P} ratio={float(r):.6f} ({vs_clebsch(r)})")
        results.append((f"Clebsch_blowup_k{k}", n, D, P, r))

    # ---- Higman-Sims blowup (largest known TF SRG) ----
    # Building Higman-Sims is involved; skip the blowup and rely on Phase 1's
    # known ratio.

    f.close()
    if results:
        best = max(results, key=lambda t: t[4])
        print(f"\n4s SUMMARY: best stretch ratio = {float(best[4]):.6f} at {best[0]}")
    return results


if __name__ == "__main__":
    tsv = sys.argv[1] if len(sys.argv) > 1 else (
        os.path.join(os.path.dirname(__file__), "..", "phase4_logs", "all_graphs.tsv")
    )
    run(tsv)
