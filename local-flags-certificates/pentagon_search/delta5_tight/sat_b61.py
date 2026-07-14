"""Independent SAT cross-check for B61 (and the calibration analogues), encoding the FULL
labeled shell problem of reduction_note.md Lemma 5 — attachment sets explicit, so label
realizability is built in (no relaxation).

Variables (m potential S-vertices, labels [d], degree bound Delta):
  s[x][a]      : a in A_x
  e[x][y]      : F-edge xy (x < y)
  t[x][y][a][b]: pentagon witness (edge xy, a in A_x, b in A_y), a != b

Constraints:
  TF on F; e_xy -> A_x, A_y disjoint; deg(x) = |A_x| + deg_F(x) <= Delta;
  capacity: each a used <= Delta-1 times; e_xy -> A_x, A_y nonempty;
  t -> e, s, s (one direction suffices to DECIDE "max >= target");
  sum t >= target.

UNSAT at target=61 (Delta=d=5, m=20)  <=>  M <= 60  (B61, exact level).

Calibration: Delta=3, d=3, m=6: target 7 must be UNSAT, target 6 SAT (ground truth M=6).
"""
import argparse
import itertools
import sys

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Cadical153


def build(delta, d, m, target):
    pool = IDPool()
    s = {(x, a): pool.id(f"s{x}_{a}") for x in range(m) for a in range(d)}
    e = {(x, y): pool.id(f"e{x}_{y}") for x, y in itertools.combinations(range(m), 2)}
    cls = []

    # TF
    for x, y, z in itertools.combinations(range(m), 3):
        cls.append([-e[(x, y)], -e[(y, z)], -e[(x, z)]])
    # edge -> disjoint labels, nonempty labels
    for (x, y), exy in e.items():
        for a in range(d):
            cls.append([-exy, -s[(x, a)], -s[(y, a)]])
        cls.append([-exy] + [s[(x, a)] for a in range(d)])
        cls.append([-exy] + [s[(y, a)] for a in range(d)])
    # degree per vertex: sum_a s + sum_y e <= Delta
    for x in range(m):
        lits = [s[(x, a)] for a in range(d)] + \
               [e[(min(x, y), max(x, y))] for y in range(m) if y != x]
        cnf = CardEnc.atmost(lits=lits, bound=delta, vpool=pool, encoding=EncType.seqcounter)
        cls.extend(cnf.clauses)
    # capacity per label: <= Delta - 1
    for a in range(d):
        lits = [s[(x, a)] for x in range(m)]
        cnf = CardEnc.atmost(lits=lits, bound=delta - 1, vpool=pool, encoding=EncType.seqcounter)
        cls.extend(cnf.clauses)
    # pentagon witnesses
    tlits = []
    for (x, y), exy in e.items():
        for a in range(d):
            for b in range(d):
                if a == b:
                    continue
                tv = pool.id(f"t{x}_{y}_{a}_{b}")
                cls.append([-tv, exy])
                cls.append([-tv, s[(x, a)]])
                cls.append([-tv, s[(y, b)]])
                tlits.append(tv)
    # objective
    cnf = CardEnc.atleast(lits=tlits, bound=target, vpool=pool, encoding=EncType.totalizer)
    cls.extend(cnf.clauses)
    return cls, s, e, pool


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--delta", type=int, default=5)
    ap.add_argument("--d", type=int, default=5)
    ap.add_argument("--m", type=int, default=None, help="number of S-vertex slots (default d*(delta-1))")
    ap.add_argument("--target", type=int, required=True)
    args = ap.parse_args()
    m = args.m if args.m is not None else args.d * (args.delta - 1)
    cls, s, e, pool = build(args.delta, args.d, m, args.target)
    print(f"Delta={args.delta} d={args.d} m={m} target={args.target}: "
          f"{pool.top} vars, {len(cls)} clauses", flush=True)
    with Cadical153(bootstrap_with=cls) as solver:
        sat = solver.solve()
        if sat:
            model = set(l for l in solver.get_model() if l > 0)
            edges = [(x, y) for (x, y), v in e.items() if v in model]
            labels = {x: [a for a in range(args.d) if s[(x, a)] in model] for x in range(m)}
            val = sum(len(labels[x]) * len(labels[y]) for x, y in edges)
            print(f"SAT: configuration with >= {args.target} exists "
                  f"(model objective recount = {val})")
            print("  edges:", edges)
            print("  labels:", {x: labels[x] for x in range(m) if labels[x]})
        else:
            print(f"UNSAT: no configuration reaches {args.target} (M <= {args.target - 1})")


if __name__ == "__main__":
    main()
