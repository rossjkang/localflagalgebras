import random, sys

def pentagons_through_root(n, adj):
    # count induced C5 containing vertex 0, sparse walk: 0-a-x-y-b-0
    cnt = 0
    nb0 = [v for v in range(1, n) if adj[0] >> v & 1]
    for ia in range(len(nb0)):
        for ib in range(ia+1, len(nb0)):
            a, b = nb0[ia], nb0[ib]
            if adj[a] >> b & 1: continue  # TF anyway
            for x in range(1, n):
                if x == a or x == b: continue
                if not (adj[a] >> x & 1): continue
                if adj[0] >> x & 1 or adj[b] >> x & 1: continue
                for y in range(1, n):
                    if y == a or y == b or y == x: continue
                    if not (adj[b] >> y & 1 and adj[x] >> y & 1): continue
                    if adj[0] >> y & 1 or adj[a] >> y & 1: continue
                    cnt += 1
    return cnt // 1  # each pentagon counted once per unordered {a,b} and ordered (x,y)? a<b fixed, x,y determined by sides -> once

def degs(n, adj):
    return [bin(adj[v]).count('1') for v in range(n)]

def tf_ok_after(n, adj, u, v):
    # adding uv creates triangle iff common neighbor
    return (adj[u] & adj[v]) == 0

def search(Delta, n, iters, seed_adj=None, rng=None):
    rng = rng or random.Random()
    adj = list(seed_adj) if seed_adj else [0]*n
    cur = pentagons_through_root(n, adj)
    best = cur
    for it in range(iters):
        u = rng.randrange(n); v = rng.randrange(n)
        if u == v: continue
        had = adj[u] >> v & 1
        if had:
            adj[u] ^= 1 << v; adj[v] ^= 1 << u
        else:
            if bin(adj[u]).count('1') >= Delta or bin(adj[v]).count('1') >= Delta: continue
            if not tf_ok_after(n, adj, u, v): continue
            adj[u] |= 1 << v; adj[v] |= 1 << u
        new = pentagons_through_root(n, adj)
        # simulated annealing acceptance
        T = max(0.01, 2.0 * (1 - it/iters))
        if new >= cur or rng.random() < pow(2.718, (new-cur)/T):
            cur = new
            if cur > best: best = cur
        else:
            # revert
            if had:
                adj[u] |= 1 << v; adj[v] |= 1 << u
            else:
                adj[u] ^= 1 << v; adj[v] ^= 1 << u
    return best

# Clebsch check: P(v) per vertex
def clebsch():
    gens = {1,2,4,8,15}
    n = 16
    adj = [0]*n
    for u in range(n):
        for v in range(n):
            if u != v and (u ^ v) in gens:
                adj[u] |= 1 << v
    return n, adj

n, cadj = clebsch()
print("Clebsch P(v=0) =", pentagons_through_root(n, cadj))

random.seed(12345)
for Delta, nball, target in [(4, 17, 24), (5, 26, 60)]:
    best = 0
    for restart in range(8):
        b = search(Delta, nball, 4000, rng=random.Random(restart*7+1))
        best = max(best, b)
    print(f"Delta={Delta} ball<={nball}: best P(root) found = {best} (per-vertex route needs <= {target})")

# seed Delta=5 search from Clebsch embedded in 26 vertices
seed = cadj + [0]*10
best = 0
for restart in range(8):
    b = search(5, 26, 4000, seed_adj=seed, rng=random.Random(restart*13+5))
    best = max(best, b)
print("Delta=5 Clebsch-seeded: best P(root) =", best)
