"""Exact branch-and-bound for the shell-reformulated per-vertex pentagon maximum.

Problem (see the development notes, Lemma 5):
maximize  sum_{xy in E(F)} k_x * k_y  over TF graphs F with vertex weights k_x >= 1,
subject to (size relaxation M' of the full labeled problem M):
  (a) k_x + deg_F(x) <= Delta
  (e) edge xy  =>  k_x + k_y <= d          [attachment sets disjoint in A, |A| = d]
  (m) m_x = sum_{y~x} k_y <= (Delta-1)*(d - k_x)   [per-a capacity, sound consequence]
  (s) sum_x k_x <= d*(Delta-1)             [per-a capacity, summed]
  every vertex has deg_F >= 1 (isolated vertices are deleted WLOG).

M <= M'; Clebsch attains 60 in M (F = Petersen, k = 2), so M' <= 60 proves B61 (M = 60).

Modes:
  max      — compute M' and collect all optimal configurations
  decide T — prove no configuration reaches >= T (prune against T-1), or exhibit one

Calibration targets (must hold before any Delta=5 claim):
  Delta=3, d=3  ->  6   (ground truth: exhaustive geng sweep, delta3_calibration.log)
  Delta=5, d=2  -> 16   (hand proof: k=1 forced on edges, bipartite by label, K_{4,4})
  Delta=5, d<=5 restricted to Clebsch profile -> 60
"""
import sys
from itertools import combinations


def gen_profiles(delta, d):
    """Non-increasing weight profiles (k_1 >= ... >= k_m), parts in [1, min(d-1, delta-1)],
    sum <= d*(delta-1). Every vertex must have an edge, so k_x <= d-1 (its neighbour needs
    k >= 1) and k_x <= delta-1 (it needs a free degree slot)."""
    kmax = min(d - 1, delta - 1)
    smax = d * (delta - 1)
    out = []

    def rec(prefix, last, total):
        if prefix:
            out.append(tuple(prefix))
        for k in range(min(last, smax - total), 0, -1):
            prefix.append(k)
            rec(prefix, k, total + k)
            prefix.pop()

    rec([], kmax, 0)
    return out


def profile_ub(ks, delta, d):
    """Sound upper bounds on the objective for a whole profile."""
    K = sum(ks)
    # Mantel on the k-blowup (TF graph on K tokens)
    b_mantel = (K * K) // 4
    # slot bound: each vertex has <= delta - k_x edge slots, each edge weighted
    # <= k_x * (best compatible partner), halved since both endpoints pay a slot
    b_slot = 0
    for i, k in enumerate(ks):
        kappa = max((k2 for j, k2 in enumerate(ks) if j != i and k + k2 <= d), default=0)
        b_slot += k * (delta - k) * kappa
    b_slot //= 2
    # capacity bound on m_x, same halving
    b_cap = sum(k * min((delta - k) * max((k2 for j, k2 in enumerate(ks) if j != i and k + k2 <= d), default=0),
                        (delta - 1) * (d - k)) for i, k in enumerate(ks)) // 2
    # class-split bound: heavy vertices (k >= 2) pay k*(delta-k)*kappa per vertex (each
    # heavy edge counted at least once, heavy-k1 edges on the heavy side); edges among k=1
    # vertices have weight 1 and consume 2 slots from the k1 slot pool
    b_split = 0
    n1_slots = 0
    for i, k in enumerate(ks):
        if k >= 2:
            kappa = max((k2 for j, k2 in enumerate(ks) if j != i and k + k2 <= d), default=0)
            b_split += k * (delta - k) * kappa
        else:
            n1_slots += delta - 1
    b_split += n1_slots // 2
    bounds = [b_mantel, b_slot, b_cap, b_split]
    if delta == 5 and d == 5:
        # dual certificate y = (1/2, 2, 4, 7/2): k_x*k_y <= y(k_x)+y(k_y) on every
        # admissible edge (k_x+k_y <= 5), hence obj <= sum_x (5-k_x)*y(k_x).
        # Stored doubled to stay integral.
        Y2 = {1: 1, 2: 4, 3: 8, 4: 7}
        bounds.append(sum((5 - k) * Y2[k] for k in ks) // 2)
    return min(bounds)


def solve(delta, d, mode="max", target=None, verbose=False, symmetry=True):
    """max:    returns (best_value, optima)  [optima incomplete if pruning ties; see enum]
    decide: returns (found_geq_target, witness)
    enum:   returns (target, all_configs_with_value_geq_target)  [strict pruning < target]

    Symmetry breaking (sound): vertices sorted by k desc; within an equal-k block order
    vertices greedily by largest adjacency-bitmask-to-earlier. Any configuration admits such
    a labeling, so requiring (row_i & bits(0..i-2)) <= row_{i-1} when k_i = k_{i-1} loses no
    isomorphism class."""
    capA = delta - 1
    if mode == "decide":
        best = target - 1
    elif mode == "enum":
        best = target - 1
    else:
        best = 0
    optima = []
    witness = [None]

    profiles = gen_profiles(delta, d)
    profiles.sort(key=lambda ks: -profile_ub(ks, delta, d))

    for ks in profiles:
        if profile_ub(ks, delta, d) <= (target - 1 if mode == "enum" else best):
            continue
        m = len(ks)
        adj = [0] * m          # bitmask adjacency
        deg = [0] * m
        mw = [0] * m           # m_x = weighted neighbourhood sum
        edges = []
        rows = [0] * m         # row bitmask of each vertex (edges to earlier)

        degcap = [delta - k for k in ks]
        mcap = [capA * (d - k) for k in ks]
        # cache: for each position j, sorted compatible earlier-k list and kappa
        compat_ks = []
        kappa_f = []
        for j in range(m):
            cl = sorted((ks[t] for t in range(j) if ks[t] + ks[j] <= d), reverse=True)
            compat_ks.append(cl)
            kappa_f.append(max((ks[t] for t in range(m) if t != j and ks[t] + ks[j] <= d),
                               default=0))

        def future_ub(i, cur):
            # AGG1: per-future-vertex row caps
            agg1 = 0
            for j in range(i, m):
                kj = ks[j]
                agg1 += kj * min(mcap[j], sum(compat_ks[j][: degcap[j]]))
            # AGG2: residual slot pool (placed residuals + future slots), each edge
            # consumes one slot at each end -> halve
            pool = 0
            for t in range(i):
                pool += (degcap[t] - deg[t]) * ks[t] * kappa_f[t]
            for j in range(i, m):
                pool += degcap[j] * ks[j] * kappa_f[j]
            # AGG3 class-split: heavy residual slots pay k*kappa each; k1-k1 edges
            # (weight 1) consume 2 slots from the k1 residual pool. Heavy-k1 edges are
            # counted on the heavy side only (k1 residuals not reduced — overestimate, sound)
            heavy = 0
            n1pool = 0
            for t in range(m):
                r = degcap[t] - deg[t] if t < i else degcap[t]
                if ks[t] >= 2:
                    heavy += r * ks[t] * kappa_f[t]
                else:
                    n1pool += r
            agg3 = heavy + n1pool // 2
            aggs = [agg1, pool // 2, agg3]
            if delta == 5 and d == 5:
                # dual certificate on residual degrees (see profile_ub)
                Y2 = {1: 1, 2: 4, 3: 8, 4: 7}
                agg4 = 0
                for t in range(m):
                    r = degcap[t] - deg[t] if t < i else degcap[t]
                    agg4 += r * Y2[ks[t]]
                aggs.append(agg4 // 2)
            return cur + min(aggs)

        def dfs(i, cur):
            nonlocal best
            if mode == "decide" and witness[0] is not None:
                return
            if i == m:
                if min(deg) == 0:
                    return
                if mode == "max":
                    if cur > best:
                        best = cur
                        optima.clear()
                    if cur == best:
                        optima.append((ks, tuple(edges)))
                elif mode == "enum":
                    if cur >= target:
                        optima.append((ks, tuple(edges), cur))
                else:
                    if cur >= target:
                        witness[0] = (ks, tuple(edges), cur)
                return
            if future_ub(i, cur) <= (target - 1 if mode == "enum" else best):
                return
            ki = ks[i]
            cands = [j for j in range(i) if ks[j] + ki <= d and deg[j] < degcap[j]
                     and mw[j] + ki <= mcap[j]]
            maxrow = min(degcap[i], len(cands))
            tie = symmetry and i > 0 and ks[i - 1] == ki
            tie_limit = rows[i - 1] if tie else None
            lowmask = (1 << max(i - 1, 0)) - 1
            for rsize in range(maxrow, -1, -1):
                for row in combinations(cands, rsize):
                    rmask = 0
                    ok = True
                    for j in row:
                        if adj[j] & rmask:
                            ok = False
                            break
                        rmask |= 1 << j
                    if not ok:
                        continue
                    if tie and (rmask & lowmask) > tie_limit:
                        continue
                    w = sum(ks[j] for j in row)
                    if w > mcap[i]:
                        continue
                    for j in row:
                        adj[j] |= 1 << i
                        deg[j] += 1
                        mw[j] += ki
                    adj[i] = rmask
                    rows[i] = rmask
                    deg[i] = rsize
                    mw[i] = w
                    edges.extend((j, i) for j in row)
                    dfs(i + 1, cur + ki * w)
                    del edges[len(edges) - rsize:]
                    for j in row:
                        adj[j] &= ~(1 << i)
                        deg[j] -= 1
                        mw[j] -= ki
                    adj[i] = 0
                    rows[i] = 0
                    deg[i] = 0
                    mw[i] = 0
                    if mode == "decide" and witness[0] is not None:
                        return

        dfs(0, 0)
        if verbose:
            print(f"  profile {ks}: done (best so far {best})", file=sys.stderr)

    if mode == "max":
        return best, optima
    if mode == "enum":
        return target, optima
    return (witness[0] is not None), witness[0]


if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--delta", type=int, default=5)
    ap.add_argument("--d", type=int, required=True)
    ap.add_argument("--mode", choices=["max", "decide", "enum"], default="max")
    ap.add_argument("--target", type=int, default=None)
    ap.add_argument("--verbose", action="store_true")
    ap.add_argument("--no-symmetry", action="store_true",
                    help="disable tie-block symmetry breaking (validation runs)")
    args = ap.parse_args()
    sym = not args.no_symmetry
    if args.mode == "max":
        best, optima = solve(args.delta, args.d, "max", verbose=args.verbose, symmetry=sym)
        print(f"Delta={args.delta} d={args.d}: M' = {best}, {len(optima)} optimal configuration(s) [tie-pruned, not exhaustive]")
        for ks, es in optima[:20]:
            print(f"  k={ks} edges={es}")
        if len(optima) > 20:
            print(f"  ... and {len(optima)-20} more")
    elif args.mode == "decide":
        found, wit = solve(args.delta, args.d, "decide", target=args.target, verbose=args.verbose, symmetry=sym)
        if found:
            print(f"Delta={args.delta} d={args.d}: configuration with value >= {args.target} EXISTS: {wit}")
        else:
            print(f"Delta={args.delta} d={args.d}: NO configuration reaches {args.target} (M' <= {args.target-1})")
    else:
        _, configs = solve(args.delta, args.d, "enum", target=args.target, verbose=args.verbose, symmetry=sym)
        print(f"Delta={args.delta} d={args.d}: {len(configs)} configuration(s) with value >= {args.target}")
        for ks, es, val in configs[:50]:
            print(f"  val={val} k={ks} edges={es}")
        if len(configs) > 50:
            print(f"  ... and {len(configs)-50} more")
