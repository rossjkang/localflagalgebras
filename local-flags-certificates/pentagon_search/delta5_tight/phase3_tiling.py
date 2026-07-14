"""Phase 3 contingency resolved by closure: every value-60 ball is degree-saturated
(A-capacities 4+1=5, S-degrees 2+3=5, root degree 5), so it equals its own connected
component. An equality graph (P = 12n) is therefore a disjoint union of 16-vertex
reconstructions in which EVERY vertex u has P(u) = 60 — not just the root.

This script: collects all reconstructions of all realizable cubic-TF F's, dedupes by
isomorphism, and computes the per-vertex pentagon profile of each. Uniqueness holds iff
Clebsch is the only one with P(u) = 60 for all u.
"""
import itertools
import subprocess
import sys

sys.path.insert(0, ".")
from reconstruct import realizations, reconstruct, clebsch_adj, is_isomorphic
from phase3_r60 import parse_graph6


def pent_through(adj, v):
    cnt = 0
    nb = sorted(adj[v])
    for i in range(len(nb)):
        for j in range(i + 1, len(nb)):
            a, b = nb[i], nb[j]
            if b in adj[a]:
                continue
            for x in adj[a] - {v}:
                if x in adj[v] or x in adj[b]:
                    continue
                for y in adj[b] - {v}:
                    if y in adj[v] or y in adj[a] or y == x:
                        continue
                    if y in adj[x]:
                        cnt += 1
    return cnt


def degree_saturated(adj):
    return all(len(a) == 5 for a in adj)


def main():
    out = subprocess.run(["geng", "-t", "-d3", "-D3", "-q", "10"],
                         capture_output=True, text=True, check=True)
    cands = [parse_graph6(l) for l in out.stdout.splitlines() if l.strip()]
    cleb = clebsch_adj()
    ks = [2] * 10

    classes = []   # (representative adj, source F indices, count, is_clebsch)
    for idx, adjF in enumerate(cands):
        edges = [(i, j) for i, j in itertools.combinations(range(10), 2) if j in adjF[i]]
        for lab in realizations(ks, edges):
            ball = reconstruct(ks, edges, lab)
            assert len(ball) == 16 and degree_saturated(ball), \
                "every 60-ball must be a closed 5-regular 16-vertex graph"
            for cl in classes:
                if is_isomorphic(ball, cl[0]):
                    cl[1].add(idx)
                    cl[2] += 1
                    break
            else:
                classes.append([ball, {idx}, 1, is_isomorphic(ball, cleb)])

    print(f"{len(classes)} isomorphism class(es) of value-60 balls (all closed, 5-regular, 16 vertices):")
    survivors = []
    for i, (ball, srcs, cnt, isc) in enumerate(classes):
        pv = [pent_through(ball, u) for u in range(16)]
        all60 = all(p == 60 for p in pv)
        P = sum(pv) // 5
        tag = "CLEBSCH" if isc else "non-Clebsch"
        print(f"  class {i} [{tag}] from F#{sorted(srcs)} ({cnt} realizations): "
              f"P = {P}, per-vertex P range {min(pv)}..{max(pv)}, all-60: {all60}")
        if all60:
            survivors.append((i, isc))

    print()
    if len(survivors) == 1 and survivors[0][1]:
        print("UNIQUENESS HOLDS: Clebsch is the only value-60 ball with every vertex at 60.")
        print("Equality components must be Clebsch; the target theorem follows.")
    else:
        print("UNIQUENESS FAILS at component level — survivors:", survivors)


if __name__ == "__main__":
    main()
