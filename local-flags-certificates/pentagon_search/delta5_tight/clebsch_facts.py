"""Phase 0 item 3: verify the Clebsch facts used by the local-to-global reduction.

Clebsch graph = folded 5-cube on F_2^4: u ~ v iff u XOR v in D = {1,2,4,8,15}
(matches `clebschFlag` in DaveyThesis2024/PentagonConjecture.lean).

Facts needed by the reduction (the development notes):
  (C1) 16 vertices, 5-regular
  (C2) triangle-free
  (C3) diameter 2
  (C4) vertex-transitive (translations x -> x XOR a are automorphisms acting transitively)
  (C5) P(v) = 60 pentagons through every vertex (=> pentagonCount = 192)
  (C6) shell structure at any root v: second shell S has 10 vertices, each with
       exactly 2 neighbours in N(v) (mu = 2), and G[S] is 3-regular on 10 vertices
       with 15 edges (the Petersen graph), so
       P(v) = sum over S-S edges of |Ax|*|Ay| = 15 * 2 * 2 = 60.
"""
import itertools

D = {1, 2, 4, 8, 15}
N = 16
adj = [set(u ^ d for d in D) for u in range(N)]

# C1
assert all(len(adj[u]) == 5 for u in range(N)), "5-regular"

# C2
assert all(v not in adj[u] or not (adj[u] & adj[v]) for u in range(N) for v in range(N) if v in adj[u]), "triangle-free"

# C3: diameter 2
for u in range(N):
    ball = {u} | adj[u] | set().union(*(adj[w] for w in adj[u]))
    assert len(ball) == N, "diameter 2"

# C4: translations are automorphisms (u~v iff (u^a)~(v^a)) and act transitively
for a in range(N):
    assert all((v in adj[u]) == ((v ^ a) in adj[u ^ a]) for u in range(N) for v in range(N)), "translation automorphism"
# transitivity: translation by a maps 0 to a, for every a.

# C5: pentagons through each vertex
def pent_through(v):
    cnt = 0
    nb = sorted(adj[v])
    for i in range(5):
        for j in range(i + 1, 5):
            a, b = nb[i], nb[j]
            for x in adj[a] - {v}:
                if x in adj[v] or x in adj[b]:
                    continue
                for y in adj[b] - {v}:
                    if y in adj[v] or y in adj[a] or y == x:
                        continue
                    if y in adj[x]:
                        cnt += 1
    return cnt

pv = [pent_through(v) for v in range(N)]
assert pv == [60] * N, pv
print("C1-C5 verified: 5-regular, TF, diameter 2, vertex-transitive, P(v)=60 for all v")
print("pentagonCount =", sum(pv) // 5)

# C6: shell structure at root 0
root = 0
A = adj[root]
S = [u for u in range(N) if u != root and u not in A]
assert len(S) == 10
ks = [len(adj[s] & A) for s in S]
assert ks == [2] * 10, ks
sedges = [(x, y) for x, y in itertools.combinations(S, 2) if y in adj[x]]
assert len(sedges) == 15
assert all(len(adj[s] & set(S)) == 3 for s in S)
# G[S] is the Petersen graph: 3-regular, 10 vertices, girth 5 (no C3, no C4)
for x, y in itertools.combinations(S, 2):
    common = adj[x] & adj[y] & set(S)
    if y in adj[x]:
        assert not common, "girth: no triangle in S"
    else:
        assert len(common) <= 1, "girth: no C4 in S"
assert sum(len(adj[x] & set(adj[y])) >= 0 for x, y in sedges) == 15
recount = sum(len(adj[x] & A) * len(adj[y] & A) for x, y in sedges)
assert recount == 60
print("C6 verified: shell decomposition |S|=10, k_x=2 each, G[S] = Petersen (3-reg, 15 edges, girth 5);")
print("P(root) = sum k_x*k_y over S-edges =", recount)
