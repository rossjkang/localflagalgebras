"""Phase 3 (R60) tooling: from a shell configuration (k-profile + F-edges) produced by
shell_bnb.py, (1) enumerate label realizations A_x (attachment sets), (2) reconstruct the
ball H per Lemma 5 of the reduction note, (3) test rooted isomorphism against Clebsch.

A configuration is a pair (ks, edges): ks[i] = k-weight of S-vertex i, edges = F-edges.
Realization: A_x subset of [5], |A_x| = ks[x], A_x cap A_y = empty for xy in F,
each a in [5] used <= 4 times.
"""
import itertools


def realizations(ks, edges, limit=None):
    """Backtracking enumeration of label assignments. Returns list of tuples of frozensets."""
    m = len(ks)
    nbr = [[] for _ in range(m)]
    for x, y in edges:
        nbr[x].append(y)
        nbr[y].append(x)
    cap = [4] * 5
    assign = [None] * m
    out = []

    def rec(i):
        if limit and len(out) >= limit:
            return
        if i == m:
            out.append(tuple(frozenset(s) for s in assign))
            return
        forbidden = set()
        for j in nbr[i]:
            if j < i:
                forbidden |= assign[j]
        avail = [a for a in range(5) if a not in forbidden and cap[a] > 0]
        for combo in itertools.combinations(avail, ks[i]):
            assign[i] = set(combo)
            for a in combo:
                cap[a] -= 1
            rec(i + 1)
            for a in combo:
                cap[a] += 1
            assign[i] = None

    rec(0)
    return out


def reconstruct(ks, edges, labels):
    """Ball H: vertex 0 = root, 1..5 = A, 6.. = S. Returns adjacency sets."""
    m = len(ks)
    n = 6 + m
    adj = [set() for _ in range(n)]

    def add(u, v):
        adj[u].add(v)
        adj[v].add(u)

    for a in range(1, 6):
        add(0, a)
    for x in range(m):
        for a in labels[x]:
            add(6 + x, 1 + a)
    for x, y in edges:
        add(6 + x, 6 + y)
    return adj


def clebsch_adj():
    D = {1, 2, 4, 8, 15}
    return [set(u ^ x for x in D) for u in range(16)]


def is_isomorphic(adj1, adj2):
    """Backtracking isomorphism test for small graphs (degree-partition refined)."""
    n = len(adj1)
    if len(adj2) != n:
        return False
    d1 = sorted(len(a) for a in adj1)
    d2 = sorted(len(a) for a in adj2)
    if d1 != d2:
        return False
    mapping = [None] * n
    used = [False] * n
    order = sorted(range(n), key=lambda v: -len(adj1[v]))

    def rec(idx):
        if idx == n:
            return True
        v = order[idx]
        for w in range(n):
            if used[w] or len(adj2[w]) != len(adj1[v]):
                continue
            ok = True
            for u in adj1[v]:
                mu = mapping[u]
                if mu is not None and mu not in adj2[w]:
                    ok = False
                    break
            if ok:
                for u in range(n):
                    if mapping[u] is not None and u not in adj1[v] and mapping[u] in adj2[w]:
                        ok = False
                        break
            if ok:
                mapping[v] = w
                used[w] = True
                if rec(idx + 1):
                    return True
                mapping[v] = None
                used[w] = False
        return False

    return rec(0)


def check_config_is_clebsch(ks, edges, verbose=True):
    """Full R60 pipeline for one configuration. Returns (n_realizations, all_clebsch)."""
    reals = realizations(ks, edges)
    if verbose:
        print(f"  config k={ks}: {len(reals)} label realization(s)")
    if not reals:
        return 0, True  # unrealizable: contributes no ball
    cleb = clebsch_adj()
    allc = True
    for lab in reals:
        adj = reconstruct(ks, edges, lab)
        if len(adj) != 16:
            allc = False
            if verbose:
                print(f"    realization {lab}: ball has {len(adj)} vertices != 16 — NOT Clebsch")
            continue
        iso = is_isomorphic(adj, cleb)
        if verbose and not iso:
            print(f"    realization {lab}: 16-vertex ball NOT isomorphic to Clebsch")
        allc &= iso
    return len(reals), allc


if __name__ == "__main__":
    # self-test: the Clebsch configuration (F = Petersen as it appears in the Clebsch shell)
    D = {1, 2, 4, 8, 15}
    adjC = [set(u ^ x for x in D) for u in range(16)]
    A = sorted(adjC[0])
    S = [u for u in range(16) if u != 0 and u not in adjC[0]]
    ks = [2] * 10
    edges = [(i, j) for i, j in itertools.combinations(range(10), 2) if S[j] in adjC[S[i]]]
    labels = [frozenset(A.index(a) for a in adjC[s] & set(A)) for s in S]
    adj = reconstruct(ks, edges, labels)
    assert is_isomorphic(adj, adjC), "self-test: reconstructed Clebsch shell must be Clebsch"
    print("self-test OK: Clebsch shell config reconstructs to Clebsch")
    nreal, allc = check_config_is_clebsch(ks, edges)
    print(f"Clebsch config: {nreal} realizations, all reconstruct to Clebsch: {allc}")
