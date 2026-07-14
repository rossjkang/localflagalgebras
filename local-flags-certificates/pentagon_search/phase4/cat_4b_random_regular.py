#!/usr/bin/env python3
"""
Phase 4 — sub-category 4b: random Δ-regular sampling at higher Δ.

Phase 1 sampled at Δ=3 only. Now we sample at Δ ∈ {8, 10, 12, 15, 20} for
n ∈ {Δ+4, Δ+8, Δ+12, Δ+16, Δ+20}, ~few thousand graphs per (Δ, n) slice.
Filter to TF + girth >= 5, compute ratio, track maximum.

If any sample exceeds 12/625 = Clebsch ratio, refine via local search.
"""

from __future__ import annotations

import os
import random
import sys
import time
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


def sample_random_regular(D: int, n: int, attempts: int = 5) -> nx.Graph | None:
    """Attempt to sample a random D-regular graph on n vertices."""
    for _ in range(attempts):
        try:
            return nx.random_regular_graph(D, n, seed=random.randrange(2**30))
        except nx.NetworkXError:
            continue
    return None


def random_tf_bipartite_regular(D: int, m: int) -> nx.Graph | None:
    """
    Random D-regular bipartite graph on 2m vertices (m on each side).
    Bipartite => triangle-free automatically.

    Implementation: bipartite circulant Cay_{Z_m}({r_1..r_D}). Connect
    L[i] to R[(i + r_k) mod m] for k = 1..D, where {r_1..r_D} ⊂ Z_m are
    distinct. Always D-regular if the residues are distinct.

    For larger m and D, this gives a structured but reasonably random
    bipartite graph. After the swap-walk it loses bipartiteness mostly.
    """
    if m < D:
        return None
    # Pick D distinct residues mod m.
    residues = random.sample(range(m), D)
    L = list(range(m))
    R = list(range(m, 2 * m))
    G = nx.Graph()
    G.add_nodes_from(L + R)
    for i in range(m):
        for r in residues:
            G.add_edge(L[i], R[(i + r) % m])
    degs = [d for _, d in G.degree()]
    if min(degs) == D and max(degs) == D:
        return G
    return None


def random_tf_swap_walk(seed: nx.Graph, n_swaps: int = 1000) -> nx.Graph:
    """
    Random walk in TF-Δ-regular space via 2-edge-swap mixing.
    Each step: pick two disjoint edges {a,b} {c,d}; try swap to {a,c} {b,d}
    iff result is TF + still regular.
    """
    G = seed.copy()
    edges = list(G.edges())
    for _ in range(n_swaps):
        if len(edges) < 2:
            break
        e1, e2 = random.sample(edges, 2)
        a, b = e1
        c, d = e2
        if len({a, b, c, d}) != 4:
            continue
        # Try both pairings.
        random.shuffle([0, 0])  # cheap shuffle of below order
        candidates = [((a, c), (b, d)), ((a, d), (b, c))]
        random.shuffle(candidates)
        for new_pair in candidates:
            (x1, y1), (x2, y2) = new_pair
            if G.has_edge(x1, y1) or G.has_edge(x2, y2):
                continue
            # Check TF preservation.
            G.remove_edges_from([e1, e2])
            G.add_edges_from(new_pair)
            if is_triangle_free(G):
                # accept
                edges = list(G.edges())
                break
            else:
                # revert
                G.remove_edges_from(new_pair)
                G.add_edges_from([e1, e2])
    return G


def local_swap_search(G: nx.Graph, iters: int = 200) -> tuple[nx.Graph, Fraction, int]:
    """
    Local 2-edge-swap search: pick two disjoint edges {a,b} {c,d}, replace with
    {a,c} {b,d} (or {a,d} {b,c}) if it preserves TF + degree sequence and
    increases the pentagon count.
    """
    best_G = G.copy()
    best_P = count_induced_5cycles(best_G)
    n = best_G.number_of_nodes()
    if n == 0:
        return best_G, Fraction(0), 0
    Delta = max(d for _, d in best_G.degree())
    best_r = Fraction(best_P, n * Delta ** 4) if Delta > 0 else Fraction(0)

    for _ in range(iters):
        edges = list(best_G.edges())
        if len(edges) < 2:
            break
        e1, e2 = random.sample(edges, 2)
        a, b = e1
        c, d = e2
        if len({a, b, c, d}) != 4:
            continue
        for new_pair in [((a, c), (b, d)), ((a, d), (b, c))]:
            (x1, y1), (x2, y2) = new_pair
            if best_G.has_edge(x1, y1) or best_G.has_edge(x2, y2):
                continue
            H = best_G.copy()
            H.remove_edges_from([e1, e2])
            H.add_edges_from(new_pair)
            if not is_triangle_free(H):
                continue
            P = count_induced_5cycles(H)
            if P > best_P:
                best_G = H
                best_P = P
                Delta_new = max(d for _, d in H.degree())
                best_r = Fraction(P, n * Delta_new ** 4) if Delta_new > 0 else Fraction(0)
                break
    return best_G, best_r, best_P


def run(tsv_path: str, samples_per_slice: int = 200):
    f = open_tsv(tsv_path, append=True)
    overall_best = (Fraction(0), None, "")
    refined_results = []

    # Strategy: seed with random D-regular bipartite (automatically TF), then
    # MCMC-walk via 2-edge swaps that preserve both regularity AND TF. This
    # gives mixing on the TF-D-regular graph space at scales where direct
    # rejection sampling fails.
    slices = []
    # n = 2m needs m >= D and total edges m*D such that swap walks reach
    # non-bipartite components.
    for D in [3, 4, 5, 6, 8, 10, 12, 15]:
        # 2*m vertices each, where m chosen so n is "moderately above"
        # the Clebsch n=16 scale.
        ns = []
        if D <= 5:
            ns = [12, 16, 20, 30]
        elif D <= 8:
            ns = [16, 24, 32, 48]
        elif D <= 12:
            ns = [24, 40, 60]
        else:  # D=15
            ns = [32, 60, 100]
        for n in ns:
            if n % 2 == 0 and n >= 2 * D:
                slices.append((D, n))

    random.seed(20260521)

    for (D, n) in slices:
        m = n // 2
        if m < D:
            continue
        t0 = time.time()
        slice_best_r = Fraction(0)
        slice_best_g6 = ""
        tf_count = 0
        ok_seeds = 0
        for s in range(samples_per_slice):
            # Seed: random TF bipartite D-regular (always TF).
            seed = random_tf_bipartite_regular(D, m)
            if seed is None:
                continue
            ok_seeds += 1
            # MCMC walk: scale with n*D for mixing.
            G = random_tf_swap_walk(seed, n_swaps=max(100, 20 * n * D))
            if not is_triangle_free(G):
                continue
            tf_count += 1
            gv = girth(G)
            if gv >= 6:
                P = 0
            else:
                P = count_induced_5cycles(G)
            degs = [d for _, d in G.degree()]
            Delta_eff = max(degs) if degs else 0
            if Delta_eff == 0:
                continue
            r = Fraction(P, n * Delta_eff ** 4)
            if r > slice_best_r:
                slice_best_r = r
                slice_best_g6 = nx.to_graph6_bytes(G, header=False).decode().strip()
                if r > overall_best[0]:
                    overall_best = (r, G.copy(), f"D{D}_n{n}_sample{s}")
            # Only log every-10th sample to TSV to avoid explosion.
            if s % 10 == 0:
                tsv_row(f, "4b_RandReg",
                        f"D{D}_n{n}_sample{s}", G)
        dt = time.time() - t0
        print(f"[4b] D={D} n={n}: seeds={ok_seeds}, TF post-walk={tf_count}/{samples_per_slice}, "
              f"best ratio={float(slice_best_r):.6f} "
              f"(vs Clebsch {float(CLEBSCH_RATIO):.6f}), "
              f"time {dt:.1f}s")

    # Refine if we found anything close to Clebsch
    if overall_best[1] is not None and overall_best[0] >= Fraction(15, 1000):
        print(f"\n[4b-refine] Best random sample at ratio {float(overall_best[0]):.6f} — "
              f"applying local-swap search...")
        G = overall_best[1]
        Gr, rr, Pr = local_swap_search(G, iters=500)
        print(f"[4b-refine] After local search: ratio {float(rr):.6f}, P={Pr}")
        tsv_row(f, "4b_RandReg_Refined",
                f"{overall_best[2]}_refined", Gr)
        refined_results.append((rr, Gr, overall_best[2]))

    f.close()
    print(f"\n4b SUMMARY: overall best ratio = {float(overall_best[0]):.6f} "
          f"({overall_best[2]}), Clebsch = {float(CLEBSCH_RATIO):.6f}")
    return overall_best, refined_results


if __name__ == "__main__":
    tsv = sys.argv[1] if len(sys.argv) > 1 else (
        os.path.join(os.path.dirname(__file__), "..", "phase4_logs", "all_graphs.tsv")
    )
    sps = int(sys.argv[2]) if len(sys.argv) > 2 else 100
    run(tsv, samples_per_slice=sps)
