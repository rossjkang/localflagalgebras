"""Implementation A of the Delta=4 pruned traversal.

A direct, INCREMENTAL port of DaveyThesis2024/Delta4/{Model,Search,Prune,MaskGen,ChunkP}.lean.
Adjacency is kept as a list of 12-bit row bitmasks; deg and e22 are maintained as
accumulators along the DFS; rem22/touched are suffix tables over pairList.

The independent cross-check is model_b.c, which recomputes every prune quantity from
scratch at each node out of the raw Nat adjacency word, exactly as the Lean does.
"""

import sys
sys.setrecursionlimit(200000)

# ---------------- MaskGen.genMask / msGen (Lean: MaskGen.lean:169) ----------------

def genMask(r, lo, c0, c1, c2, c3):
    if r == 0:
        return [0] if (c0 == 0 and c1 == 0 and c2 == 0 and c3 == 0) else []
    out = []
    for m in range(lo, 16):
        b0, b1, b2, b3 = m % 2, m // 2 % 2, m // 4 % 2, m // 8 % 2
        if b0 <= c0 and b1 <= c1 and b2 <= c2 and b3 <= c3:
            for w in genMask(r - 1, m, c0 - b0, c1 - b1, c2 - b2, c3 - b3):
                out.append(m + 16 * w)
    return out

def msGen(n):
    return genMask(n, 1, 3, 3, 3, 3)

# ---------------- Search.pairList (Lean: Search.lean:66) ----------------

def pairsFrom(i, m):
    return [(i, j) for j in range(m - 1, -1, -1)]

def pairList(n):
    out = []
    for i in range(n - 1, -1, -1):
        out.extend(pairsFrom(i, i))
    return out

# ---------------- Model digits ----------------

def msk(K, i):
    return (K // 16 ** i) % 16

POP = [bin(x).count('1') for x in range(16)]
CERT = {1: 1, 2: 3}

def cert(k):
    return CERT.get(k, 0)


class Ctx:
    """Everything determined by (n, K)."""
    __slots__ = ('n', 'K', 'mk', 'kw', 'n3', 'n4', 'ps', 'L', 'rem22', 'touch',
                 'rhs_const', 'hasL', 'rootW')

    def __init__(self, n, K):
        self.n = n
        self.K = K
        self.mk = [msk(K, i) for i in range(n)]
        self.kw = [POP[m] for m in self.mk]
        self.n3 = sum(1 for i in range(n) if self.kw[i] == 3)
        self.n4 = sum(1 for i in range(n) if self.kw[i] == 4)
        self.ps = pairList(n)
        L = len(self.ps)
        self.L = L
        # suffix rem22 (Prune.lean:100) and suffix touched-slot bitmask (Prune.lean:115)
        self.rem22 = [0] * (L + 1)
        self.touch = [0] * (L + 1)
        for t in range(L - 1, -1, -1):
            i, j = self.ps[t]
            add = 1 if (self.kw[i] == 2 and self.kw[j] == 2
                        and (self.mk[i] & self.mk[j]) == 0) else 0
            self.rem22[t] = self.rem22[t + 1] + add
            self.touch[t] = self.touch[t + 1] | (1 << i) | (1 << j)
        # pruneOK rhs constant: 38 + 4 n3 + 12 n4
        self.rhs_const = 38 + 4 * self.n3 + 12 * self.n4
        self.hasL = [[(self.mk[i] >> a) & 1 for a in range(4)] for i in range(n)]
        self.rootW = [[sum(self.hasL[i][a] * self.hasL[i][b] for i in range(n))
                       for b in range(4)] for a in range(4)]


def leafOK(ctx, rows, deg):
    """Model.leafOK (Model.lean:274): twoT < 38 or charge + 6*twoT <= credit + 212."""
    n, kw, hasL, rootW = ctx.n, ctx.kw, ctx.hasL, ctx.rootW
    twoT = 0
    for i in range(n):
        r = rows[i]
        if r:
            ki = kw[i]
            for j in range(n):
                if (r >> j) & 1:
                    twoT += ki * kw[j]
    if twoT < 38:
        return True
    # shellW(a, y) = (1 - hasL[y][a]) * |N(y) cap B_a|
    shellW = [[0] * n for _ in range(4)]
    for a in range(4):
        Ba = 0
        for i in range(n):
            if hasL[i][a]:
                Ba |= 1 << i
        for y in range(n):
            if hasL[y][a] == 0:
                shellW[a][y] = bin(rows[y] & Ba).count('1')
    slack = [max(0, 4 - kw[i] - deg[i]) for i in range(n)]
    credit = 0
    for a in range(4):
        credit += sum(3 * rootW[a][b] for b in range(4) if b != a)
        credit += sum(3 * shellW[a][y] for y in range(n))
    charge = 0
    for a in range(4):
        for b in range(4):
            if b == a:
                continue
            dhatRoot = sum(hasL[y][b] for y in range(n) if shellW[a][y] != 0)
            charge += dhatRoot * cert(rootW[a][b])
        for y in range(n):
            c = cert(shellW[a][y])
            if c == 0:
                continue
            d = sum(hasL[y][b] for b in range(4) if b != a and rootW[a][b] != 0)
            d += sum(1 for z in range(n)
                     if z != y and shellW[a][z] != 0 and (rows[y] >> z) & 1)
            d += slack[y]
            charge += d * c
    return charge + 6 * twoT <= credit + 212


def count_mask(ctx):
    """(nodes, violations) for searchPCnt n K -- ChunkP.goGCnt at pruneOK/leafOK."""
    n, kw, mk, ps, L = ctx.n, ctx.kw, ctx.mk, ctx.ps, ctx.L
    rem22, touch, rhs_const = ctx.rem22, ctx.touch, ctx.rhs_const
    rows = [0] * n
    deg = [0] * n
    st = [0, 0]  # nodes, violations

    def go(t, e22):
        st[0] += 1
        if t == L:
            if not leafOK(ctx, rows, deg):
                st[1] += 1
            return
        # pruneOK (Prune.lean:396)
        tch = touch[t]
        fixed = 0
        for x in range(n):
            if not ((tch >> x) & 1):
                s = 4 - kw[x] - deg[x]
                if s > 0:
                    fixed += (2 * kw[x] - 1) * s
        if 36 + 2 * (e22 + rem22[t]) < rhs_const + fixed:
            return
        i, j = ps[t]
        go(t + 1, e22)
        # takeGuard (Search.lean:175)
        if (kw[i] + deg[i] < 4 and kw[j] + deg[j] < 4
                and (mk[i] & mk[j]) == 0 and (rows[i] & rows[j]) == 0):
            rows[i] |= 1 << j
            rows[j] |= 1 << i
            deg[i] += 1
            deg[j] += 1
            go(t + 1, e22 + (1 if (kw[i] == 2 and kw[j] == 2) else 0))
            rows[i] &= ~(1 << j)
            rows[j] &= ~(1 << i)
            deg[i] -= 1
            deg[j] -= 1

    go(0, 0)
    return st[0], st[1]


def word_of_rows(rows):
    """The Nat adjacency word A: row i occupies base-4096 digit i."""
    A = 0
    for i, r in enumerate(rows):
        A |= r << (12 * i)
    return A


def expand(ctx, d):
    """ChunkP.expandP / expandPNodes plus each frontier state's subtree count.

    Returns (frontier : list[int], internal : int, subtree : list[(nodes,viol)])."""
    n, kw, mk, ps, L = ctx.n, ctx.kw, ctx.mk, ctx.ps, ctx.L
    rem22, touch, rhs_const = ctx.rem22, ctx.touch, ctx.rhs_const
    rows = [0] * n
    deg = [0] * n
    frontier = []
    internal = [0]

    def pruned(t, e22):
        tch = touch[t]
        fixed = 0
        for x in range(n):
            if not ((tch >> x) & 1):
                s = 4 - kw[x] - deg[x]
                if s > 0:
                    fixed += (2 * kw[x] - 1) * s
        return 36 + 2 * (e22 + rem22[t]) < rhs_const + fixed

    def go(dd, t, e22):
        if dd == 0 or t == L:
            frontier.append((word_of_rows(rows), e22, t))
            return
        if pruned(t, e22):
            internal[0] += 1
            return
        i, j = ps[t]
        go(dd - 1, t + 1, e22)
        internal[0] += 1
        if (kw[i] + deg[i] < 4 and kw[j] + deg[j] < 4
                and (mk[i] & mk[j]) == 0 and (rows[i] & rows[j]) == 0):
            rows[i] |= 1 << j
            rows[j] |= 1 << i
            deg[i] += 1
            deg[j] += 1
            go(dd - 1, t + 1, e22 + (1 if (kw[i] == 2 and kw[j] == 2) else 0))
            rows[i] &= ~(1 << j)
            rows[j] &= ~(1 << i)
            deg[i] -= 1
            deg[j] -= 1

    go(d, 0, 0)
    words = [w for (w, _, _) in frontier]
    subs = [subtree_count(ctx, w, e22, t) for (w, e22, t) in frontier]
    return words, internal[0], subs


def subtree_count(ctx, A, _e22_ignored, t0):
    """goGCnt from adjacency word A with undecided suffix ps[t0:].

    e22 is RECOMPUTED from A here, not inherited: the Lean prune reads it off the
    adjacency word, so recomputing is the faithful thing and also cross-checks the
    incremental accumulator used in count_mask."""
    n, kw, mk, ps, L = ctx.n, ctx.kw, ctx.mk, ctx.ps, ctx.L
    rem22, touch, rhs_const = ctx.rem22, ctx.touch, ctx.rhs_const
    rows = [(A >> (12 * i)) % 4096 for i in range(n)]
    deg = [bin(rows[i]).count('1') for i in range(n)]
    e22 = sum(1 for i in range(n) for j in range(i)
              if kw[i] == 2 and kw[j] == 2 and (rows[i] >> j) & 1)
    assert e22 == _e22_ignored, (e22, _e22_ignored)
    st = [0, 0]

    def go(t, e22):
        st[0] += 1
        if t == L:
            if not leafOK(ctx, rows, deg):
                st[1] += 1
            return
        tch = touch[t]
        fixed = 0
        for x in range(n):
            if not ((tch >> x) & 1):
                s = 4 - kw[x] - deg[x]
                if s > 0:
                    fixed += (2 * kw[x] - 1) * s
        if 36 + 2 * (e22 + rem22[t]) < rhs_const + fixed:
            return
        i, j = ps[t]
        go(t + 1, e22)
        if (kw[i] + deg[i] < 4 and kw[j] + deg[j] < 4
                and (mk[i] & mk[j]) == 0 and (rows[i] & rows[j]) == 0):
            rows[i] |= 1 << j
            rows[j] |= 1 << i
            deg[i] += 1
            deg[j] += 1
            go(t + 1, e22 + (1 if (kw[i] == 2 and kw[j] == 2) else 0))
            rows[i] &= ~(1 << j)
            rows[j] &= ~(1 << i)
            deg[i] -= 1
            deg[j] -= 1

    go(t0, e22)
    return st[0], st[1]
