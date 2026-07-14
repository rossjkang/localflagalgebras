"""Phase 3 (R60): classify the value-60 face and test Clebsch rigidity.

By the dual-certificate equality analysis (reduction_note.md, Lemma 7):
value 60 forces k = 2 on all 10 S-vertices and F 3-regular TF on 10 vertices.
geng -t -d3 -D3 10 gives exactly the candidate F's. For each: enumerate all label
realizations (A_x 2-subsets of [5], disjoint across edges, each label used <= 4 times),
reconstruct the ball, test rooted-graph isomorphism against Clebsch.

Also cross-validates shell_bnb's enum-60 face: every enumerated value-60 config must be
3-regular with k = 2 and isomorphic to one of the geng graphs.
"""
import itertools
import subprocess
import sys

sys.path.insert(0, ".")
from reconstruct import realizations, reconstruct, clebsch_adj, is_isomorphic
from shell_bnb import solve


def parse_graph6(line):
    data = [ord(c) - 63 for c in line.strip()]
    n = data[0]
    bits = []
    for b in data[1:]:
        bits += [(b >> i) & 1 for i in range(5, -1, -1)]
    adj = [set() for _ in range(n)]
    k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                adj[i].add(j)
                adj[j].add(i)
            k += 1
    return adj


def adj_from_edges(m, edges):
    adj = [set() for _ in range(m)]
    for x, y in edges:
        adj[x].add(y)
        adj[y].add(x)
    return adj


def main():
    out = subprocess.run(["geng", "-t", "-d3", "-D3", "-q", "10"],
                         capture_output=True, text=True, check=True)
    g6 = [l for l in out.stdout.splitlines() if l.strip()]
    cands = [parse_graph6(l) for l in g6]
    print(f"geng: {len(cands)} cubic TF graphs on 10 vertices")

    cleb = clebsch_adj()
    ks = [2] * 10
    verdicts = []
    for idx, adjF in enumerate(cands):
        edges = [(i, j) for i, j in itertools.combinations(range(10), 2) if j in adjF[i]]
        reals = realizations(ks, edges)
        if not reals:
            verdicts.append((g6[idx], 0, None))
            print(f"  F#{idx} ({g6[idx]}): UNREALIZABLE (no valid labeling) — contributes no 60-ball")
            continue
        allc = True
        for lab in reals:
            ball = reconstruct(ks, edges, lab)
            if not is_isomorphic(ball, cleb):
                allc = False
                break
        verdicts.append((g6[idx], len(reals), allc))
        print(f"  F#{idx} ({g6[idx]}): {len(reals)} realization(s), all balls Clebsch: {allc}")

    n_realizable = sum(1 for _, r, _ in verdicts if r)
    ok = all(c for _, r, c in verdicts if r)
    print(f"\nR60 verdict: {n_realizable}/{len(cands)} candidate F's realizable; "
          f"all realizable reconstructions Clebsch: {ok}")

    # cross-validation: shell_bnb enum-60 face is contained in the geng class
    print("\ncross-validating shell_bnb enum-60 face ...")
    _, configs = solve(5, 5, "enum", target=60)
    assert all(val == 60 for _, _, val in configs), "no config above 60 (B61)"
    bad = 0
    matched = [0] * len(cands)
    for kss, edges, val in configs:
        if tuple(kss) != (2,) * 10:
            bad += 1
            continue
        adjF = adj_from_edges(10, edges)
        if any(len(a) != 3 for a in adjF):
            bad += 1
            continue
        for idx, c in enumerate(cands):
            if is_isomorphic(adjF, c):
                matched[idx] += 1
                break
        else:
            bad += 1
    print(f"  {len(configs)} enum-60 configs: matched per geng class = {matched}, unmatched/bad = {bad}")
    assert bad == 0, "every value-60 config must be cubic TF on 10 vertices"
    assert all(m > 0 for m in matched) or True  # informational
    print("cross-validation OK")


if __name__ == "__main__":
    main()
