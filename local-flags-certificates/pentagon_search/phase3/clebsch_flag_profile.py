#!/usr/bin/env python3
"""Phase 3 — Step 3a + 3b + 3c (size-5 cert).

Compute the Clebsch graph's local-flag profile against the 58 size-5
bounded-pentagon flags (from `flags_enumeration.txt`), then
evaluate the BRRB SDP cert's per-block contributions at this profile.

The BRRB size-5 cert proves `P(G) ≤ |G|·Δ⁴/40` (Theorem 3.2). At
Clebsch (n=16, Δ=5) this gives bound = 16·625/40 = 250 pentagons,
but Clebsch has only 192 — so the size-5 cert is loose by 250/192 ≈ 1.30×.

Output: a per-flag and per-CS-block profile + a `.tsv` ranked by
block contribution.
"""
import itertools
import json
import re
import sys
from collections import defaultdict
from pathlib import Path

# ---------------------------------------------------------------------------
# Clebsch graph SRG(16,5,0,2): halved 5-cube.
# Vertices = even-weight binary 5-tuples; edges = pairs at Hamming distance 4.
# ---------------------------------------------------------------------------

def build_clebsch():
    verts = []
    for i in range(32):
        bits = [(i >> b) & 1 for b in range(5)]
        if sum(bits) % 2 == 0:
            verts.append(tuple(bits))
    assert len(verts) == 16
    vid = {v: idx for idx, v in enumerate(verts)}
    adj = [[False] * 16 for _ in range(16)]
    for i, u in enumerate(verts):
        for j, v in enumerate(verts):
            if i != j and sum(a != b for a, b in zip(u, v)) == 4:
                adj[i][j] = True
    # Sanity check
    for v in range(16):
        deg = sum(adj[v])
        assert deg == 5, f"vertex {v} has deg {deg}"
    return adj, verts, vid

# ---------------------------------------------------------------------------
# Parse the size-5 flag enumeration.
# ---------------------------------------------------------------------------

def parse_flag_enum():
    flags = {}
    path = Path("flags_enumeration.txt")
    text = path.read_text()
    for line in text.splitlines():
        m = re.match(r"^F(\d+): edges=(\[.*\]) colours=(\[.*\])", line)
        if not m:
            continue
        fid = int(m.group(1))
        edges = eval(m.group(2))  # safe; controlled file
        colours = eval(m.group(3))
        flags[fid] = (edges, colours)
    return flags

# ---------------------------------------------------------------------------
# Bounded-pentagon flag semantics:
#   F1..F58 are size-5 2-coloured graphs (colour 0 / 1) with the constraints:
#     (a) no triangle, (b) no black-black edge, (c) the colour-0 component
#         is connected.
# We need: in Clebsch (n=16, Δ=5), for each F, count the number of size-5
# vertex tuples (v_0, ..., v_4) such that:
#     - the induced colored sub-flag on (v_0..v_4) is isomorphic to F,
#     - with the colouring derived from a "marked" vertex v_⋆ — i.e., colour
#       of v_i = 0 iff v_i is v_⋆ or v_i ∈ N(v_⋆).
# But actually the cert is OBJECTIVE-FREE: it proves a bound on the OBJECTIVE
# (= path counting) under the local-flag density profile. The profile is:
#
#   d(F) := # of labelled size-5 induced subgraphs of (G, v_⋆) isomorphic to F
#          / (some normalisation)
#
# where (G, v_⋆) is a "marked TF graph". For PROFILE EVALUATION at Clebsch:
# Clebsch is vertex-transitive, so we can fix v_⋆ = vertex 0 of Clebsch and
# do not need to average over choice of v_⋆.
#
# Convention (matches BRRB/Lean): we use UNLABELLED (Razborov "p-density")
# counts: density d(F) = #{induced labelled embeddings F → G_marked} / aut(F) ÷ C(n-1, 4) etc.
# But for this analysis we'll use RAW LABELLED-induced counts; ratios of
# blocks are invariant under uniform scaling.
# ---------------------------------------------------------------------------

def count_flag_in_marked_clebsch(adj, n, flag_edges, flag_colours, v_star):
    """Count labelled induced size-5 subgraphs of (Clebsch, v_star) isomorphic
    to (flag_edges, flag_colours). The coloring of each Clebsch vertex u is:
        0 if u == v_star or adj[v_star][u]
        1 otherwise
    The flag edge set is canonically on vertices {0,1,2,3,4} (size = 5).

    Returns # of ordered 5-tuples (u_0,...,u_4) of DISTINCT vertices of
    Clebsch such that:
      - colouring matches (clebsch_color(u_i) = flag_colours[i]),
      - induced adjacency matches (u_i ~_G u_j iff (i,j) in flag_edges).
    """
    # Mark colours of all vertices given v_star.
    cl = [None] * n
    for u in range(n):
        cl[u] = 0 if (u == v_star or adj[v_star][u]) else 1
    edge_set = set()
    for (i, j) in flag_edges:
        edge_set.add((i, j))
        edge_set.add((j, i))
    fsz = 5
    count = 0
    for tup in itertools.permutations(range(n), fsz):
        ok = True
        # colour check
        for i in range(fsz):
            if cl[tup[i]] != flag_colours[i]:
                ok = False
                break
        if not ok:
            continue
        # adjacency check
        for i in range(fsz):
            for j in range(i + 1, fsz):
                want = ((i, j) in edge_set)
                got = adj[tup[i]][tup[j]]
                if want != got:
                    ok = False
                    break
            if not ok:
                break
        if not ok:
            continue
        count += 1
    return count

# ---------------------------------------------------------------------------
# Cert vectors from BrrbCertificate.lean (these are scaled by integer
# factors as documented in that file).
# ---------------------------------------------------------------------------

# All scaled ×2 as in the Lean file.
b1x2 = [10,0,0,0,0,-2,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,
        0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,
        0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0]

sig1x2 = [0,0,0,-8,-12,0,0,0,0,0, 0,4,0,0,0,0,0,0,0,0,
          0,0,0,4,0,0,0,0,0,0, 0,8,0,0,0,0,0,0,0,0,
          0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0]

sig2x2 = [0,0,0,0,0,48,0,0,0,0, 0,0,-8,0,-8,0,0,-4,0,0,
          0,0,0,0,-4,0,0,0,0,0, 0,0,-24,-12,0,0,0,0,0,0,
          0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0]

sig3x2 = [0,0,0,0,0,0,0,0,0,0, 4,2,0,0,-4,0,0,0,0,0,
          0,2,0,4,-4,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,
          0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0]

sig4x2 = [0,0,0,0,0,0,0,2,0,0, 0,2,0,0,-4,0,0,0,0,0,
          0,0,0,0,0,0,0,0,0,0, 8,8,0,-12,0,0,0,0,0,0,
          0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0]

sig5x2 = [0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,-4,-2,0,0,0,
          0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,2,0,0,0,
          0,0,0,0,0,0,0,0,0,0, 0,0,0,0,4,0,0,0]

linSum2 = [60,0,0,-8,-12,0,0,2,0,0, 4,8,-2,0,-10,-8,-4,-1,0,0,
           0,2,0,8,-5,0,0,0,0,0, 8,16,-6,-15,0,0,4,0,0,0,
           0,0,0,0,0,0,0,0,0,0, 0,0,0,0,8,0,0,0]

cs0x2 = [0,0,0,8,0,0,0,-2,0,0, -4,0,2,0,0,0,0,1,0,0,
         0,-2,0,0,0,0,0,0,0,0, -8,0,6,0,0,0,0,0,0,0,
         0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0]

cs1x2 = [0,0,0,0,12,0,0,0,-4,0, 0,-8,0,0,10,8,4,0,0,0,
         0,0,0,-8,5,0,0,0,0,0, 0,-16,0,15,0,0,-6,0,0,0,
         0,0,0,0,0,0,0,0,0,0, 0,0,0,0,-12,0,0,0]

target2 = [60,0,0,0,0,0,0,0,-4,0, 0,0,0,0,0,0,0,0,0,0,
           0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,-2,0,0,0,
           0,0,0,0,0,0,0,0,0,0, 0,0,0,0,-4,0,0,0]

# Sanity check: linSum2 + cs0x2 + cs1x2 == target2
test_sum = [linSum2[i] + cs0x2[i] + cs1x2[i] for i in range(58)]
assert test_sum == target2, "decomposition mismatch"

# Sanity check: 6*b1x2 + sig1x2 + sig2x2/4 + sig3x2 + sig4x2 + 2*sig5x2 == linSum2
linsum_check = [
    6 * b1x2[i] + sig1x2[i] + (sig2x2[i] // 4) + sig3x2[i] + sig4x2[i] + 2 * sig5x2[i]
    for i in range(58)
]
assert linsum_check == linSum2, "linSum decomposition mismatch"

# ---------------------------------------------------------------------------
# Evaluate the certificate at a flag profile (d_1, ..., d_58).
# Each cert vector v of length 58 satisfies the cone identity:
#     sum_i v[i] * d(F_i) >= 0
# where the sum is the cert's per-component contribution to the bound.
# ---------------------------------------------------------------------------

def evaluate_at_profile(profile, label, vec):
    """Compute the cert component's linear functional at the profile.

    profile[i] = d(F_{i+1}) (1-indexed flag).
    vec[i] = cert coefficient on F_{i+1}, scaled by 2.

    Returns sum / 2.
    """
    total = 0
    contribs = []
    for i in range(58):
        if vec[i] != 0:
            contribs.append((i + 1, vec[i], profile[i], vec[i] * profile[i]))
        total += vec[i] * profile[i]
    return total / 2.0, contribs


def main():
    print("[*] Building Clebsch graph SRG(16,5,0,2)...")
    adj, verts, vid = build_clebsch()
    n = 16

    # Verify Clebsch's pentagon count
    print("[*] Verifying Clebsch pentagon count = 192...")
    pent = 0
    # induced C5: canonical orientation: v0 = min, v1 < v4
    for v0 in range(n):
        for v1 in range(v0 + 1, n):
            if not adj[v0][v1]:
                continue
            for v2 in range(v0 + 1, n):
                if v2 == v1 or not adj[v1][v2] or adj[v0][v2]:
                    continue
                for v3 in range(v0 + 1, n):
                    if v3 == v1 or v3 == v2 or not adj[v2][v3]:
                        continue
                    if adj[v0][v3] or adj[v1][v3]:
                        continue
                    for v4 in range(v1 + 1, n):  # v4 > v1, ensures canonical orientation
                        if v4 == v2 or v4 == v3:
                            continue
                        if not adj[v3][v4] or not adj[v4][v0]:
                            continue
                        if adj[v1][v4] or adj[v2][v4]:
                            continue
                        pent += 1
    print(f"[*] Pentagon count = {pent} (expected 192)")
    assert pent == 192

    print("[*] Parsing flag enumeration...")
    flags = parse_flag_enum()
    assert len(flags) == 58
    print(f"[*] Loaded {len(flags)} flags F1..F58")

    # Clebsch is vertex-transitive, so fix v_star = 0.
    v_star = 0
    print(f"[*] Counting labelled flag embeddings at v_star={v_star}...")
    counts = {}
    # Note: each ordered 5-tuple takes O(n^5) = 16^5 = ~1M iterations per flag.
    # 58 flags → 58 * 1M = ~60M; let's optimise by precomputing colour vector.
    cl = [(0 if (u == v_star or adj[v_star][u]) else 1) for u in range(n)]
    by_colour = defaultdict(list)
    for u in range(n):
        by_colour[cl[u]].append(u)
    print(f"    colour distribution: 0={len(by_colour[0])}, 1={len(by_colour[1])}")
    # In Clebsch: v_star + N(v_star) = 1 + 5 = 6 colour-0 vertices.
    # The remaining 10 are colour 1.
    assert len(by_colour[0]) == 6, f"got {len(by_colour[0])}, expected 6"
    assert len(by_colour[1]) == 10

    for fid, (fedges, fcolours) in flags.items():
        # Smarter enumeration: iterate over vertex slots, restricted by colour.
        c = count_flag_smart(adj, n, fedges, fcolours, cl, by_colour)
        counts[fid] = c

    # Save raw counts
    print("[*] Flag counts at Clebsch (v_star=0):")
    nonzero = [(f, c) for f, c in counts.items() if c > 0]
    nonzero.sort(key=lambda x: -x[1])
    for f, c in nonzero[:20]:
        print(f"    F{f}: {c}")
    if len(nonzero) > 20:
        print(f"    ... ({len(nonzero)} non-zero flags total)")
    print(f"    {sum(1 for v in counts.values() if v == 0)} flags have zero count")

    # ---------------------------------------------------------------------------
    # Density normalisation: per-flag-class, count / aut(F).
    # Note: the cert is invariant under different normalisations as long as it's
    # consistent (i.e., each F is treated the same way). The raw labelled counts
    # are fine for ranking block contributions.
    #
    # For interpretability, we'll also report the "labelled-induced density"
    # d_lab(F) := counts[F] / (n * (n-1)*(n-2)*(n-3)*(n-4))   [denominator =
    # number of size-5 ordered subsets of V].
    # ---------------------------------------------------------------------------
    # Local-flag-algebra normalisation: φ(F) = count(F) / (C(Δ, 5) * 120)
    # where Δ = max degree. This is the normalisation used in Lean
    # (`density_certF1_eq_one`): φ(F_1) = (Δ)_5 / (C(Δ,5) · 120) = 1.
    # For Clebsch (Δ=5): denom = C(5,5)*120 = 1*120 = 120.
    Delta = 5
    from math import comb, factorial
    denom = comb(Delta, 5) * 120  # = 120 for Δ=5
    profile_lab = [counts[fid] for fid in range(1, 59)]
    densities = [c / denom for c in profile_lab]

    # ---------------------------------------------------------------------------
    # Evaluate each cert component at this profile.
    # ---------------------------------------------------------------------------
    print()
    print("=" * 78)
    print("Per-component cert evaluation at Clebsch (v_star=0)")
    print("=" * 78)
    print(f"Normalisation: raw labelled count / {denom}")
    print()

    components = [
        ("B1 (5∅ - F6)", b1x2, "regularity B1: phi(F1)=1 ⟹ phi(F6)=5"),
        ("σ1", sig1x2, "extension diff at σ_1 type"),
        ("σ2 (/4)", sig2x2, "extension diff at σ_2 type"),
        ("σ3", sig3x2, "extension diff at σ_3 type"),
        ("σ4", sig4x2, "extension diff at σ_4 type"),
        ("σ5", sig5x2, "extension diff at σ_5 type"),
        ("linSum (6·B1+σ1+σ2/4+σ3+σ4+2σ5)", linSum2, "ALL linear constraints"),
        ("cs0 (CS at σ6 = K_{1,2} BBR)", cs0x2, "PSD block 0 (σ_6)"),
        ("cs1 (CS at σ7 = K_{1,2} RBR)", cs1x2, "PSD block 1 (σ_7)"),
        ("target (30∅ - 2F9 - F37 - 2F55)", target2, "objective"),
    ]
    block_eval = {}
    for label, vec, descr in components:
        # ALL vectors scaled ×2 (linSum, cs0, cs1, target), σ_2 is scaled ×8 effectively
        # so we report the linear functional `sum v[i] * d[i] / 2` (the cert's true contribution).
        scale_div = 2.0
        if label == "σ2 (/4)":
            scale_div = 8.0  # both ×2 in file AND division by 4 outside
        elif label == "σ5":
            # The cert uses 2·σ5x2 = σ5 contribution at scale ×4 in target, but since
            # we just want the SLACK of σ5x2 itself, report at /2.
            scale_div = 2.0
        val = sum(vec[i] * densities[i] for i in range(58)) / scale_div
        block_eval[label] = val
        print(f"  {label:60s} = {val:+.10f}    [{descr}]")

    # Sanity: linSum + cs0 + cs1 should equal target at this density.
    chk = (block_eval["linSum (6·B1+σ1+σ2/4+σ3+σ4+2σ5)"]
           + block_eval["cs0 (CS at σ6 = K_{1,2} BBR)"]
           + block_eval["cs1 (CS at σ7 = K_{1,2} RBR)"])
    print()
    print(f"linSum + cs0 + cs1 = {chk:+.10f}")
    print(f"target              = {block_eval['target (30∅ - 2F9 - F37 - 2F55)']:+.10f}")
    print(f"diff                = {chk - block_eval['target (30∅ - 2F9 - F37 - 2F55)']:+.2e}")

    # Save details to TSV
    out_path = Path("local-flags-certificates/pentagon_search/phase3/clebsch_profile.tsv")
    with out_path.open("w") as f:
        f.write("flag\tcount\tdensity\n")
        for fid in range(1, 59):
            f.write(f"F{fid}\t{counts[fid]}\t{densities[fid-1]:.10e}\n")
    print(f"\n[*] Per-flag densities saved to {out_path}")

    # Per-block ranking (per cert component)
    rank_path = Path("local-flags-certificates/pentagon_search/phase3/clebsch_block_contribs.tsv")
    with rank_path.open("w") as f:
        f.write("component\tcontribution\tdescription\n")
        for label, vec, descr in components:
            f.write(f"{label}\t{block_eval[label]:.10f}\t{descr}\n")
    print(f"[*] Block contributions saved to {rank_path}")

    return counts, densities, block_eval


def count_flag_smart(adj, n, fedges, fcolours, cl, by_colour):
    """Smarter enumeration using colour-restricted iteration."""
    edge_set = set()
    for (i, j) in fedges:
        edge_set.add((i, j))
        edge_set.add((j, i))
    fsz = 5
    pools = [by_colour[fcolours[k]] for k in range(fsz)]
    count = 0
    # iterate over a single product, respecting distinctness
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


if __name__ == "__main__":
    main()
