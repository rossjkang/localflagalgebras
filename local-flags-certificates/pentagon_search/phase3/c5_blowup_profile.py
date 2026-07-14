#!/usr/bin/env python3
"""Compare Clebsch's cert profile to the C_5 (k/2)-blowup's profile.

The C_5 blowup is the tight construction for the size-5 cert (P = |G|·Δ⁴/40
exactly). So evaluating the cert at the C_5 blowup should give target = 0
(or close, mod rounding).
"""
import itertools
import re
from collections import defaultdict
from pathlib import Path

def build_c5_blowup(k):
    """C_5 blowup: 5 parts of size k. Vertices (i, j) for i ∈ Z/5, j ∈ [k].
    Edges: (i, j) ~ (i+1 mod 5, j') for all j, j'."""
    n = 5 * k
    adj = [[False] * n for _ in range(n)]
    def vid(i, j):
        return i * k + j
    for i in range(5):
        for j in range(k):
            for jp in range(k):
                u = vid(i, j)
                v = vid((i + 1) % 5, jp)
                adj[u][v] = True
                adj[v][u] = True
    return adj, n


def parse_flag_enum():
    flags = {}
    path = Path("flags_enumeration.txt")
    text = path.read_text()
    for line in text.splitlines():
        m = re.match(r"^F(\d+): edges=(\[.*\]) colours=(\[.*\])", line)
        if not m:
            continue
        fid = int(m.group(1))
        edges = eval(m.group(2))
        colours = eval(m.group(3))
        flags[fid] = (edges, colours)
    return flags


def count_flag_smart(adj, n, fedges, fcolours, cl, by_colour):
    edge_set = set()
    for (i, j) in fedges:
        edge_set.add((i, j))
        edge_set.add((j, i))
    fsz = 5
    pools = [by_colour[fcolours[k]] for k in range(fsz)]
    count = 0
    for tup in itertools.product(*pools):
        if len(set(tup)) != fsz:
            continue
        ok = True
        for i in range(fsz):
            for j in range(i + 1, fsz):
                want = ((i, j) in edge_set)
                got = adj[tup[i]][tup[j]]
                if want != got:
                    ok = False
                    break
            if not ok:
                break
        if ok:
            count += 1
    return count


# All scaled ×2 as in the Lean file (copied from phase3 script).
b1x2 = [10,0,0,0,0,-2,0,0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0]
sig1x2 = [0,0,0,-8,-12,0,0,0,0,0, 0,4,0,0,0,0,0,0,0,0, 0,0,0,4,0,0,0,0,0,0, 0,8,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0]
sig2x2 = [0,0,0,0,0,48,0,0,0,0, 0,0,-8,0,-8,0,0,-4,0,0, 0,0,0,0,-4,0,0,0,0,0, 0,0,-24,-12,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0]
sig3x2 = [0,0,0,0,0,0,0,0,0,0, 4,2,0,0,-4,0,0,0,0,0, 0,2,0,4,-4,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0]
sig4x2 = [0,0,0,0,0,0,0,2,0,0, 0,2,0,0,-4,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0, 8,8,0,-12,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0]
sig5x2 = [0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,-4,-2,0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,2,0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,0,0,0,4,0,0,0]
linSum2 = [60,0,0,-8,-12,0,0,2,0,0, 4,8,-2,0,-10,-8,-4,-1,0,0, 0,2,0,8,-5,0,0,0,0,0, 8,16,-6,-15,0,0,4,0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,0,0,0,8,0,0,0]
cs0x2 = [0,0,0,8,0,0,0,-2,0,0, -4,0,2,0,0,0,0,1,0,0, 0,-2,0,0,0,0,0,0,0,0, -8,0,6,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0]
cs1x2 = [0,0,0,0,12,0,0,0,-4,0, 0,-8,0,0,10,8,4,0,0,0, 0,0,0,-8,5,0,0,0,0,0, 0,-16,0,15,0,0,-6,0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,0,0,0,-12,0,0,0]
target2 = [60,0,0,0,0,0,0,0,-4,0, 0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,-2,0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,0,0,0,-4,0,0,0]


def main():
    flags = parse_flag_enum()
    # Try multiple k values (need Δ ≥ 5 for local-flag normalisation)
    for k in [4, 6, 8]:
        print(f"\n{'='*78}")
        print(f"C_5 blowup at k={k}: n={5*k}, Δ={2*k}")
        print('='*78)
        adj, n = build_c5_blowup(k)
        # Sanity: degree
        for u in range(n):
            deg = sum(adj[u])
            assert deg == 2 * k, f"vertex {u} deg {deg}"
        # Pick v_star = vertex 0
        v_star = 0
        cl = [(0 if (u == v_star or adj[v_star][u]) else 1) for u in range(n)]
        by_colour = defaultdict(list)
        for u in range(n):
            by_colour[cl[u]].append(u)
        print(f"colour 0 (v_star + N(v_star)): {len(by_colour[0])} vertices")
        print(f"colour 1: {len(by_colour[1])} vertices")
        # Local-flag normalisation: φ(F) = count(F) / (C(Δ, 5) * 5!)
        from math import comb
        Delta = 2 * k
        denom = comb(Delta, 5) * 120
        counts = {}
        for fid, (fedges, fcolours) in flags.items():
            counts[fid] = count_flag_smart(adj, n, fedges, fcolours, cl, by_colour)
        densities = [counts[fid] / denom for fid in range(1, 59)]
        print(f"non-zero flags: {sum(1 for c in counts.values() if c > 0)}")
        print(f"count(F1) = {counts[1]}, φ(F1) = {counts[1]/denom:.6f}")
        components = [
            ("B1", b1x2, 2.0),
            ("σ1", sig1x2, 2.0),
            ("σ2/4", sig2x2, 8.0),
            ("σ3", sig3x2, 2.0),
            ("σ4", sig4x2, 2.0),
            ("σ5", sig5x2, 2.0),
            ("linSum", linSum2, 2.0),
            ("cs0 (σ6 PSD)", cs0x2, 2.0),
            ("cs1 (σ7 PSD)", cs1x2, 2.0),
            ("target", target2, 2.0),
        ]
        for label, vec, scale_div in components:
            val = sum(vec[i] * densities[i] for i in range(58)) / scale_div
            print(f"  {label:20s} = {val:+.10f}")
        # Check pentagon count P
        # We're using the size-5 cert that bounds P/(|G|·Δ⁴) ≤ 1/40 = 0.025
        # So density ratio target should be 0 in the limit.
        # Compute P directly
        P = 0
        for v0 in range(n):
            for v1 in range(v0+1, n):
                if not adj[v0][v1]:
                    continue
                for v2 in range(v0+1, n):
                    if v2 == v1 or not adj[v1][v2] or adj[v0][v2]:
                        continue
                    for v3 in range(v0+1, n):
                        if v3 == v1 or v3 == v2 or not adj[v2][v3]:
                            continue
                        if adj[v0][v3] or adj[v1][v3]:
                            continue
                        for v4 in range(v1+1, n):
                            if v4 == v2 or v4 == v3:
                                continue
                            if not adj[v3][v4] or not adj[v4][v0]:
                                continue
                            if adj[v1][v4] or adj[v2][v4]:
                                continue
                            P += 1
        Delta = 2*k
        print(f"  P = {P}, |G|·Δ⁴/40 = {n*Delta**4/40}, ratio = {P/(n*Delta**4):.6f}")


if __name__ == "__main__":
    main()
