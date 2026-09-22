#!/usr/bin/env python3
"""gen_layer.py -- emit the Lean modules that close `Delta4Assembly.LayerOK n`.

Usage
    gen_layer.py plan   <n>            # partition only; print the shape, emit nothing
    gen_layer.py emit   <n>            # plan + write Lean modules under DaveyThesis2024/Delta4/Generated/
    gen_layer.py build  <n>            # build every emitted module, with the hygiene gate
    gen_layer.py run    <n>            # emit + build + verify totals
    gen_layer.py demo-kill <n>         # hygiene demonstration: kill a build, show FAILURE
    gen_layer.py project               # project the remaining layers from measured ones

Design
    * model_a.py (incremental python) computes every node count.
    * model_b.c  (literal C, recomputes every prune quantity from scratch) recomputes
      them independently.  NOTHING is emitted unless the two agree, mask by mask,
      frontier word by frontier word, subtree count by subtree count.
    * Every frontier and every mask list is emitted as a `List Nat` LITERAL tied to the
      traversal by exactly one kernel equation, never as `(expandP ...).drop a |>.take b`.
    * Every emitted fact carries a node count, because `LayerOK n` alone is
      defeq-transferable between layers.
    * A module counts as built only on exit 0 AND the expected `#print axioms` lines,
      with no `sorryAx` in any of them.  BOTH halves are load-bearing and were measured:
        - a build killed at 3 s had ALREADY printed its whole axiom block (Lean prints
          those from the elaborated environment while the kernel is still checking), so
          the axiom lines alone would have passed it -- only the exit code caught it;
        - a build whose kernel REJECTS a count exits 1 but still prints an axiom line,
          carrying `sorryAx` -- so the axiom scan is the second, independent gate.
      An empty log is always FAILURE, never success.

Output lives INSIDE the package (`DaveyThesis2024/Delta4/Generated/`), so every emitted
module is a tracked file and an ordinary `lean` target.  It is deliberately NOT imported
from `DaveyThesis2024.lean`: the census is ~2 h of kernel time and must not be paid on
every `lake build`.

2026-09-19 revision
    (a) per-mask `K###` constants are `@[irreducible] def`, so a seam wired to the wrong
        mask is a type mismatch instead of a `whnf` timeout (Layer7.lean negative control 2).
        The mask-list lookup that consumes them therefore needs `unseal M K### in`, exactly
        as `Layer7.lean` documents.
    (b) the heavy packer may split ONE mask's chunk declarations across several modules.
        Only `F_eq` and `F_internal` are indivisible.  Before this, a 637-chunk mask became
        one ~25-minute, ~640-declaration module with no checkpoint and no warning, because
        the node cap was only consulted *between* masks.  The chunk counts are now chained
        by a per-mask `step###` ladder (linear) rather than one `rw` chain (quadratic in the
        number of chunks: every rewrite re-traverses a growing `pAdd` spine).
"""

import json
import os
import re
import subprocess
import sys
import time

import model_a as MA

HERE = os.path.dirname(os.path.abspath(__file__))
# repo root: this file lives at <repo>/DaveyThesis2024/Delta4/Generated/generator/
REPO = os.path.abspath(os.path.join(HERE, os.pardir, os.pardir, os.pardir, os.pardir))
GENDIR = os.path.join(REPO, "DaveyThesis2024", "Delta4", "Generated")
GENMOD = "DaveyThesis2024.Delta4.Generated"
OLEANDIR = os.path.join(REPO, ".lake", "build", "lib", "lean",
                        "DaveyThesis2024", "Delta4", "Generated")
TWIN_B = os.path.join(HERE, "model_b")

# ---- measured budgets (see README.md in this directory) ----
CHUNK_CEIL = 3000        # nodes per `decide +kernel` declaration
SLICE_CEIL = 3000        # nodes per light `msCnt` slice
MODULE_NODE_CAP = int(os.environ.get("D4_NODE_CAP", 60000))   # nodes per module (~2.4 ms/node)
MODULE_DECL_CAP = int(os.environ.get("D4_DECL_CAP", 120))     # KERNEL decls per module
                         # (ladder rungs are O(1) and are not counted)
                         # both overridable so the split path can be exercised on a cheap layer
INTERNAL_SOFT_CAP = 8000 # internal nodes above a frontier; `F_eq` is indivisible

OK_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


# ======================================================================== twins

def twin_b_layer(n):
    out = subprocess.run([TWIN_B, "layer", str(n)], capture_output=True, text=True,
                         check=True).stdout
    rows = []
    for line in out.splitlines():
        f = line.split()
        if f and f[0] == "M":
            rows.append((int(f[3]), int(f[4]), int(f[5])))  # K, nodes, viol
    return rows


def twin_b_expand(n, K, d):
    out = subprocess.run([TWIN_B, "expand", str(n), str(K), str(d)],
                         capture_output=True, text=True, check=True).stdout
    internal = None
    states = []
    for line in out.splitlines():
        f = line.split()
        if f[0] == "INTERNAL":
            internal = int(f[1])
        elif f[0] == "S":
            rows = [int(x) for x in f[1:1 + n]]
            nodes, viol = int(f[1 + n]), int(f[2 + n])
            word = 0
            for i, r in enumerate(rows):
                word |= r << (12 * i)
            states.append((word, nodes, viol))
    return internal, states


# ======================================================================= planning

def choose_depth(ctx, target=CHUNK_CEIL):
    """Shallowest depth at which every frontier subtree fits a declaration.

    max-subtree is non-increasing in d (a level splits one state into at most two
    whose counts sum to parent-1), so a binary search is sound."""
    lo, hi = 1, ctx.L
    best = None
    while lo <= hi:
        mid = (lo + hi) // 2
        words, internal, subs = MA.expand(ctx, mid)
        if max(s[0] for s in subs) <= target:
            best = (mid, words, internal, subs)
            hi = mid - 1
        else:
            lo = mid + 1
    if best is None:
        raise RuntimeError("no depth fits: mask %d" % ctx.K)
    return best


def greedy_groups(counts, ceil):
    """Consecutive runs with total <= ceil (a single item over ceil stands alone)."""
    groups, cur, tot = [], [], 0
    for i, c in enumerate(counts):
        if cur and tot + c > ceil:
            groups.append((len(groups), cur, tot))
            cur, tot = [], 0
        cur.append(i)
        tot += c
    if cur:
        groups.append((len(groups), cur, tot))
    return groups


# ---------------------------------------------------------------- module packing

def pack_heavy(heavy_plans, order):
    """Pack heavy-mask work into modules.

    The unit stream per mask is  front, chunk_0 .. chunk_{m-1}, asm.  `front` carries
    `F_eq`/`F_internal`/`F_residual`/`step` and is INDIVISIBLE; the chunks are not, so a
    module boundary may fall anywhere inside one mask's chunk run -- that is fix (b).
    `asm` is the count ladder plus `mask###_count`: no kernel work, so it is free, but it
    must land no earlier than the mask's last chunk."""
    mods, cur = [], []
    cdecls = cnodes = 0

    def flush():
        nonlocal cur, cdecls, cnodes
        if cur:
            mods.append(dict(kind="heavy", units=cur))
            cur, cdecls, cnodes = [], 0, 0

    for i in order:
        hp = heavy_plans[i]
        fd, fn = 3, 2 * hp["internal"]      # F_eq and F_internal each walk the internal tree
        if cur and (cdecls + fd > MODULE_DECL_CAP or cnodes + fn > MODULE_NODE_CAP):
            flush()
        cur.append(("front", i)); cdecls += fd; cnodes += fn
        for k, (off, wid, cnt) in enumerate(hp["chunks"]):
            if cur and (cdecls + 1 > MODULE_DECL_CAP or cnodes + cnt > MODULE_NODE_CAP):
                flush()
            cur.append(("chunk", i, k)); cdecls += 1; cnodes += cnt
        if len(hp["chunks"]) > MODULE_DECL_CAP:
            # a split mask: give its (long, but O(1)-per-rung) ladder its own module
            flush()
            mods.append(dict(kind="heavy", units=[("asm", i)]))
        else:
            cur.append(("asm", i))
    flush()
    for k, m in enumerate(mods):
        m["name"] = "H%02d" % k
    return mods


def heavy_imports(mods):
    front_mod, chunk_mods = {}, {}
    for m in mods:
        for u in m["units"]:
            if u[0] == "front":
                front_mod[u[1]] = m["name"]
            elif u[0] == "chunk":
                chunk_mods.setdefault(u[1], set()).add(m["name"])
    for m in mods:
        need = set()
        for u in m["units"]:
            if u[0] == "chunk":
                need.add(front_mod[u[1]])
            elif u[0] == "asm":
                need.add(front_mod[u[1]])
                need |= chunk_mods.get(u[1], set())
        need.discard(m["name"])
        m["imports"] = sorted(need)
        m["decls_kernel"] = sum(3 if u[0] == "front" else 1 if u[0] == "chunk" else 0
                                for u in m["units"])
    return mods


def plan_layer(n):
    masks = MA.msGen(n)
    ctxs = [MA.Ctx(n, K) for K in masks]
    a_rows = [MA.count_mask(c) for c in ctxs]

    # ---- cross-check 1: per-mask totals, implementation A vs implementation B ----
    b_rows = twin_b_layer(n)
    if len(b_rows) != len(masks):
        raise SystemExit("TWIN MISMATCH: mask count %d vs %d" % (len(masks), len(b_rows)))
    for idx, (K, (an, av), (bK, bn, bv)) in enumerate(zip(masks, a_rows, b_rows)):
        if K != bK or an != bn or av != bv:
            raise SystemExit("TWIN MISMATCH at mask %d: A=(%d,%d,%d) B=(%d,%d,%d)"
                             % (idx, K, an, av, bK, bn, bv))
    if any(v for _, v in a_rows):
        raise SystemExit("VIOLATION predicted -- refusing to emit")

    total = sum(n_ for n_, _ in a_rows)

    # ---- the slice partition of msGen n ----
    heavy = {i for i, (c, _) in enumerate(a_rows) if c > CHUNK_CEIL}
    slices = []          # (kind, [mask indices], nodes)
    run, runtot = [], 0
    for i, (c, _) in enumerate(a_rows):
        if i in heavy:
            if run:
                slices.append(("light", run, runtot)); run, runtot = [], 0
            slices.append(("heavy", [i], c))
            continue
        if run and runtot + c > SLICE_CEIL:
            slices.append(("light", run, runtot)); run, runtot = [], 0
        run.append(i); runtot += c
    if run:
        slices.append(("light", run, runtot))

    # ---- the frontier cut for each heavy mask ----
    heavy_plans = {}
    for i in sorted(heavy):
        ctx = ctxs[i]
        d, words, internal, subs = choose_depth(ctx)
        # ---- cross-check 2: frontier literal, internal count, per-state subtrees ----
        b_internal, b_states = twin_b_expand(n, ctx.K, d)
        if b_internal != internal:
            raise SystemExit("TWIN MISMATCH internal for K=%d d=%d: %d vs %d"
                             % (ctx.K, d, internal, b_internal))
        if len(b_states) != len(words):
            raise SystemExit("TWIN MISMATCH frontier width for K=%d" % ctx.K)
        for k, (w, (sn, sv), (bw, bn, bv)) in enumerate(zip(words, subs, b_states)):
            if w != bw or sn != bn or sv != bv:
                raise SystemExit("TWIN MISMATCH state %d of K=%d: A=(%d,%d,%d) B=(%d,%d,%d)"
                                 % (k, ctx.K, w, sn, sv, bw, bn, bv))
        below = sum(s[0] for s in subs)
        if internal + below != a_rows[i][0]:
            raise SystemExit("ACCOUNTING MISMATCH for K=%d: %d + %d != %d"
                             % (ctx.K, internal, below, a_rows[i][0]))
        if internal > INTERNAL_SOFT_CAP:
            print("WARNING: K=%d d=%d has %d internal nodes (F_eq is indivisible)"
                  % (ctx.K, d, internal), file=sys.stderr)
        chunks = greedy_groups([s[0] for s in subs], CHUNK_CEIL)
        heavy_plans[i] = dict(K=ctx.K, depth=d, frontier=words, internal=internal,
                              below=below, total=a_rows[i][0],
                              chunks=[(g[1][0], len(g[1]), g[2]) for g in chunks])

    modules = heavy_imports(pack_heavy(heavy_plans, sorted(heavy)))

    # ---- light-slice modules ----
    light_ids = [k for k, s in enumerate(slices) if s[0] == "light"]
    sgroup, snodes, smod = [], 0, 0
    for k in light_ids:
        c = slices[k][2]
        if sgroup and (snodes + c > MODULE_NODE_CAP or len(sgroup) >= MODULE_DECL_CAP):
            modules.append(dict(kind="slices", name="S%02d" % smod, slices=sgroup,
                                imports=[], decls_kernel=len(sgroup)))
            smod += 1; sgroup, snodes = [], 0
        sgroup.append(k); snodes += c
    if sgroup:
        modules.append(dict(kind="slices", name="S%02d" % smod, slices=sgroup,
                            imports=[], decls_kernel=len(sgroup)))

    return dict(n=n, masks=masks, counts=[c for c, _ in a_rows], total=total,
                slices=slices, heavy=heavy_plans, modules=modules)


# ======================================================================= emission

def wrap_list(nums, indent="   ", width=96):
    if not nums:
        return None
    out, line = [], indent
    for k, x in enumerate(nums):
        tok = str(x) + ("," if k + 1 < len(nums) else "")
        if len(line) + len(tok) + 1 > width and line.strip():
            out.append(line.rstrip()); line = indent
        line += tok + " "
    if line.strip():
        out.append(line.rstrip())
    return "\n".join(out)


def lit(name, nums):
    body = wrap_list(nums)
    if body is None:
        return "@[irreducible] def %s : List Nat := []\n\n" % name
    return "@[irreducible] def %s : List Nat :=\n  [\n%s]\n\n" % (name, body)


HDR = ("/-\n  AUTO-GENERATED by DaveyThesis2024/Delta4/Generated/generator/gen_layer.py.\n"
       "  DO NOT EDIT -- regenerate instead.\n  %s\n"
       "  Node counts cross-checked by two independent implementations\n"
       "  (model_a.py, incremental; model_b.c, recomputed from scratch).\n-/\n")


def path_of(name):
    return os.path.join(GENDIR, name + ".lean")


def write(name, src):
    os.makedirs(GENDIR, exist_ok=True)
    open(path_of(name), "w").write(src)
    return path_of(name), GENMOD + "." + name


def emit_masks(plan):
    n = plan["n"]
    M = plan["masks"]
    name = "L%dMasks" % n
    src = ("import DaveyThesis2024.Delta4.ChunkP\n\n"
           + HDR % ("Layer %d: the mask list, as a literal." % n)
           + "\nnamespace Delta4Gen.L%d\nopen Delta4Model Delta4Chunk\n\n" % n
           + "/-- The %d mask words of layer %d, as a literal: a slice of it is then a walk\n"
             "    down a cons-list of numerals rather than a re-run of `genMask`.\n"
             "    `irreducible` so a mis-chained peel is a type mismatch, not a `whnf` timeout. -/\n"
             % (len(M), n)
           + lit("M", M)
           + "/-- …tied to the generator by the one kernel evaluation of `msGen`. -/\n"
           + "theorem M_eq : msGen %d = M := by decide +kernel\n\n" % n
           + "theorem M_residual : M.drop %d = [] := by decide +kernel\n\n" % len(M)
           + "/-- One rung of the layer's count ladder.  `h` forces the offsets to chain as\n"
             "    `a ↦ a + b` and `hs` forces the arithmetic, both by `rfl`; each rung is O(1),\n"
             "    so the chain is linear where a single `rw` chain would be quadratic. -/\n"
           + "theorem stepM {a b c : Nat} (h : a + b = c) {x y z : Nat}\n"
             "    (hc : msCnt %d ((M.drop a).take b) = (x, 0))\n"
             "    (hr : msCnt %d (M.drop c) = (y, 0))\n"
             "    (hs : x + y = z) :\n"
             "    msCnt %d (M.drop a) = (z, 0) := by\n"
             "  rw [msCnt_peel %d M a b c h, hc, hr]\n  subst hs\n  rfl\n\n" % (n, n, n, n)
           + "end Delta4Gen.L%d\n\n" % n
           + "#print axioms Delta4Gen.L%d.M_eq\n"
             "#print axioms Delta4Gen.L%d.M_residual\n"
             "#print axioms Delta4Gen.L%d.stepM\n" % (n, n, n))
    p, m = write(name, src)
    return p, m, ["Delta4Gen.L%d.M_eq" % n, "Delta4Gen.L%d.M_residual" % n,
                  "Delta4Gen.L%d.stepM" % n], 0


def emit_front(plan, i):
    n = plan["n"]
    hp = plan["heavy"][i]
    t = "%03d" % i
    F, d, internal, W = hp["frontier"], hp["depth"], hp["internal"], len(hp["frontier"])
    b, e = [], []
    b.append("/-! ### mask index %d: `K = %d`, %d nodes, cut at depth %d.\n"
             "    %d frontier states, %d internal nodes above them, %d below;\n"
             "    `%d + %d = %d` is `goGCnt_fst_eq`, not an assertion. -/\n\n"
             % (i, hp["K"], hp["total"], d, W, internal, hp["below"],
                internal, hp["below"], hp["total"]))
    b.append("/-- `msGen %d` index %d.  `irreducible`: a seam wired to the wrong mask is then a\n"
             "    crisp type mismatch instead of a `whnf` timeout. -/\n" % (n, i))
    b.append("@[irreducible] def K%s : Nat := %d\n\n" % (t, hp["K"]))
    b.append("def dep%s : Nat := %d\n\n" % (t, d))
    b.append("/-- The undecided pairs shared by every depth-%d frontier state. -/\n" % d)
    b.append("abbrev PS%s : List (Nat × Nat) := (pairList %d).drop dep%s\n\n" % (t, n, t))
    b.append("/-- The depth-%d frontier, as a literal `List Nat`. -/\n" % d)
    b.append(lit("F%s" % t, F))
    b.append("/-- The only place the expansion is computed. -/\n")
    b.append("theorem F%s_eq : expandP pruneOK %d K%s dep%s (pairList %d) 0 = F%s := by\n"
             "  decide +kernel\n\n" % (t, n, t, t, n, t))
    b.append("/-- The internal nodes above the frontier: a second, independent kernel fact. -/\n")
    b.append("theorem F%s_internal :\n    expandPNodes pruneOK %d K%s dep%s (pairList %d) 0 = %d := by\n"
             "  decide +kernel\n\n" % (t, n, t, t, n, internal))
    b.append("theorem F%s_residual : F%s.drop %d = [] := by decide +kernel\n\n" % (t, t, W))
    b.append("/-- One rung of this mask's frontier count ladder; O(1). -/\n")
    b.append("theorem step%s {a b c : Nat} (h : a + b = c) {x y z : Nat}\n"
             "    (hc : goAllPCnt pruneOK leafOK %d K%s PS%s ((F%s.drop a).take b) = (x, 0))\n"
             "    (hr : goAllPCnt pruneOK leafOK %d K%s PS%s (F%s.drop c) = (y, 0))\n"
             "    (hs : x + y = z) :\n"
             "    goAllPCnt pruneOK leafOK %d K%s PS%s (F%s.drop a) = (z, 0) := by\n"
             "  rw [goAllPCnt_peel pruneOK leafOK %d K%s PS%s F%s a b c h, hc, hr]\n"
             "  subst hs\n  rfl\n\n"
             % (t, n, t, t, t, n, t, t, t, n, t, t, t, n, t, t, t))
    for s in ("F%s_eq", "F%s_internal", "F%s_residual", "step%s"):
        e.append("Delta4Gen.L%d.%s" % (n, s % t))
    return "".join(b), e


def emit_chunk(plan, i, k):
    n = plan["n"]
    hp = plan["heavy"][i]
    t = "%03d" % i
    off, wid, cnt = hp["chunks"][k]
    s = ("/-- mask %d, frontier chunk %d: states [%d, %d), %d nodes. -/\n"
         "theorem c%s_%d :\n    goAllPCnt pruneOK leafOK %d K%s PS%s "
         "((F%s.drop %d).take %d) = (%d, 0) := by\n  decide +kernel\n\n"
         % (i, k, off, off + wid, cnt, t, k, n, t, t, t, off, wid, cnt))
    return s, ["Delta4Gen.L%d.c%s_%d" % (n, t, k)]


def emit_asm(plan, i):
    n = plan["n"]
    hp = plan["heavy"][i]
    t = "%03d" % i
    ch, W = hp["chunks"], len(hp["frontier"])
    m = len(ch)
    b = ["/-! ### mask index %d: the %d chunk counts, chained, and the mask's node count.\n"
         "    Nothing here traverses the tree: each rung is one `step%s`. -/\n\n" % (i, m, t)]
    b.append("theorem s%s_%d : goAllPCnt pruneOK leafOK %d K%s PS%s (F%s.drop %d) = (0, 0) := by\n"
             "  rw [F%s_residual]\n  rfl\n\n" % (t, m, n, t, t, t, W, t))
    suffix = 0
    for k in range(m - 1, -1, -1):
        off, wid, cnt = ch[k]
        nxt = off + wid
        suffix += cnt
        b.append("theorem s%s_%d : goAllPCnt pruneOK leafOK %d K%s PS%s (F%s.drop %d) = (%d, 0) :=\n"
                 "  step%s (b := %d) (c := %d) rfl c%s_%d s%s_%d rfl\n\n"
                 % (t, k, n, t, t, t, off, suffix, t, wid, nxt, t, k, t, k + 1))
    if suffix != hp["below"]:
        raise SystemExit("LADDER MISMATCH mask %d: %d != %d" % (i, suffix, hp["below"]))
    b.append("/-- **The node count of the whole mask, derived** from the %d chunk declarations\n"
             "    and `F%s_internal` via `goGCnt_fst_eq`/`goGCnt_snd_eq`. -/\n" % (m, t))
    b.append("theorem mask%s_count : searchPCnt %d K%s = (%d, 0) := by\n"
             "  have hfc : goAllPCnt pruneOK leafOK %d K%s PS%s\n"
             "      (expandP pruneOK %d K%s dep%s (pairList %d) 0) = (%d, 0) := by\n"
             "    have h := s%s_0\n"
             "    rw [List.drop_zero] at h\n"
             "    rw [F%s_eq]\n"
             "    exact h\n"
             "  have h1 := goGCnt_fst_eq pruneOK leafOK %d K%s dep%s (pairList %d) 0\n"
             "  have h2 := goGCnt_snd_eq pruneOK leafOK %d K%s dep%s (pairList %d) 0\n"
             "  simp only [hfc, F%s_internal] at h1 h2\n"
             "  exact Prod.ext h1 h2\n\n"
             % (t, n, t, hp["total"], n, t, t, n, t, t, n, hp["below"], t, t,
                n, t, t, n, n, t, t, n, t))
    return "".join(b), ["Delta4Gen.L%d.mask%s_count" % (n, t)]


def emit_heavy(plan, mod):
    n = plan["n"]
    name = "L%d%s" % (n, mod["name"])
    body, exports = [], []
    for u in mod["units"]:
        if u[0] == "front":
            s, e = emit_front(plan, u[1])
        elif u[0] == "chunk":
            s, e = emit_chunk(plan, u[1], u[2])
        else:
            s, e = emit_asm(plan, u[1])
        body.append(s); exports += e
    imports = ["import DaveyThesis2024.Delta4.ChunkP"]
    imports += ["import %s.L%d%s" % (GENMOD, n, x) for x in mod["imports"]]
    what = []
    for u in mod["units"]:
        what.append({"front": "front %d", "chunk": "chunk %d", "asm": "ladder %d"}[u[0]] % u[1])
    src = ("\n".join(imports) + "\n\n"
           + HDR % ("Layer %d, heavy material: %s." % (n, ", ".join(sorted(set(what)))))
           + "\nnamespace Delta4Gen.L%d\nopen Delta4Model Delta4Chunk\n\n" % n
           + "".join(body)
           + "end Delta4Gen.L%d\n\n" % n
           + "".join("#print axioms %s\n" % e for e in exports))
    p, m = write(name, src)
    nodes = sum((2 * plan["heavy"][u[1]]["internal"]) if u[0] == "front"
                else plan["heavy"][u[1]]["chunks"][u[2]][2] if u[0] == "chunk" else 0
                for u in mod["units"])
    return p, m, exports, nodes


def emit_slices(plan, mod):
    n = plan["n"]
    name = "L%d%s" % (n, mod["name"])
    body, exports = [], []
    for k in mod["slices"]:
        kind, ids, nodes = plan["slices"][k]
        off, wid = ids[0], len(ids)
        body.append("/-- layer-%d slice %d: masks [%d, %d), %d nodes. -/\n"
                    % (n, k, off, off + wid, nodes))
        body.append("theorem slice_%d : msCnt %d ((M.drop %d).take %d) = (%d, 0) := by\n"
                    "  decide +kernel\n\n" % (k, n, off, wid, nodes))
        exports.append("Delta4Gen.L%d.slice_%d" % (n, k))
    src = ("import %s.L%dMasks\n\n" % (GENMOD, n)
           + HDR % ("Layer %d, light mask slices %s." % (n, mod["slices"]))
           + "\nnamespace Delta4Gen.L%d\nopen Delta4Model Delta4Chunk\n\n" % n
           + "".join(body)
           + "end Delta4Gen.L%d\n\n" % n
           + "".join("#print axioms %s\n" % e for e in exports))
    p, m = write(name, src)
    return p, m, exports, sum(plan["slices"][k][2] for k in mod["slices"])


def emit_layer(plan, modnames):
    n = plan["n"]
    name = "L%d" % n
    imports = ["import %s.L%dMasks" % (GENMOD, n)]
    imports += ["import %s" % m for m in modnames]
    body, exports = [], []
    for k, (kind, ids, nodes) in enumerate(plan["slices"]):
        if kind != "heavy":
            continue
        i = ids[0]
        t = "%03d" % i
        body.append("-- The mask-list lookup for index %d.  `unseal` is kept because `decide` can\n"
                    "-- ask the *elaborator* to reduce the `Decidable` instance, and there\n"
                    "-- `@[irreducible]` bites (Layer7.lean, \"THE SEAM\").  A doc comment cannot\n"
                    "-- precede `unseal ... in`, hence the line comments.\n" % i)
        body.append("unseal M K%s in\ntheorem M_at_%d : (M.drop %d).take 1 = [K%s] := by\n"
                    "  decide +kernel\n\n" % (t, i, i, t))
        body.append("/-- **The last hop** for mask %d: the per-mask node count becomes the\n"
                    "    one-mask slice `[%d, %d)` of the layer loop. -/\n" % (i, i, i + 1))
        body.append("theorem slice_%d : msCnt %d ((M.drop %d).take 1) = (%d, 0) := by\n"
                    "  rw [M_at_%d, msCnt_singleton]\n  exact mask%s_count\n\n"
                    % (k, n, i, nodes, i, t))
        exports += ["Delta4Gen.L%d.M_at_%d" % (n, i), "Delta4Gen.L%d.slice_%d" % (n, k)]
    ns = len(plan["slices"])
    L = len(plan["masks"])
    body.append("/-! ## The layer, chained.  %d slices, offsets running 0 → %d with no gap:\n"
                "    a dropped or misordered slice fails to typecheck at the seam. -/\n\n"
                % (ns, L))
    body.append("theorem m_%d : msCnt %d (M.drop %d) = (0, 0) := msCnt_nil M_residual\n\n"
                % (ns, n, L))
    suffix, off = 0, L
    for k in range(ns - 1, -1, -1):
        wid = len(plan["slices"][k][1])
        off -= wid
        suffix += plan["slices"][k][2]
        body.append("theorem m_%d : msCnt %d (M.drop %d) = (%d, 0) :=\n"
                    "  stepM (b := %d) (c := %d) rfl slice_%d m_%d rfl\n\n"
                    % (k, n, off, suffix, wid, off + wid, k, k + 1))
    if off != 0 or suffix != plan["total"]:
        raise SystemExit("LAYER LADDER MISMATCH: off=%d suffix=%d total=%d"
                         % (off, suffix, plan["total"]))
    body.append("theorem layer_count : msCnt %d M = (%d, 0) := by\n"
                "  have h := m_0\n  rwa [List.drop_zero] at h\n\n" % (n, plan["total"]))
    body.append("/-- **Layer %d of `checkAll`.**  What `AssemblyLayers.checkAll_of_layers`\n"
                "    consumes — carried by a node count, which is the only thing that\n"
                "    distinguishes one layer's proof from another's. -/\n" % n)
    body.append("theorem layer_ok : Delta4Assembly.LayerOK %d := by\n"
                "  refine layerOK_of_msCnt (N := %d) ?_\n  rw [M_eq]\n  exact layer_count\n\n"
                % (n, plan["total"]))
    exports += ["Delta4Gen.L%d.layer_count" % n, "Delta4Gen.L%d.layer_ok" % n]
    src = ("\n".join(imports) + "\n\n"
           + HDR % ("Layer %d: the assembly — %d masks, %d nodes, 0 violations."
                    % (n, L, plan["total"]))
           + "\nnamespace Delta4Gen.L%d\nopen Delta4Model Delta4Chunk\n\n" % n
           + "".join(body)
           + "end Delta4Gen.L%d\n\n" % n
           + "".join("#print axioms %s\n" % e for e in exports))
    p, m = write(name, src)
    return p, m, exports, 0


def emit_checkall():
    """The module that consumes all ten layers.  Buildable only once layers 3-12 are built."""
    ls = list(range(3, 13))
    src = ("\n".join("import %s.L%d" % (GENMOD, n) for n in ls) + "\n\n"
           + HDR % "The finite check, assembled from the ten generated layers."
           + """
/-!
`Delta4Assembly.checkAll_of_layers` discharges shells 0-2 itself (their mask lists are
empty), so only layers 3-12 are consumed here.  `Generated.L0/L1/L2` are generated for
completeness and are not imported.

Every `layer_ok` below is carried by its own node count -- `LayerOK n` alone is
defeq-transferable between layers, so the node count is the only thing that distinguishes
one layer's proof from another's.  The ten counts are
1, 14, 92, 3764, 28957, 282124, 793508, 1577325, 6, 1, summing to the census figure
2,685,792 with 0 violations.
-/

namespace Delta4Gen
open Davey2024

/-- **The finite check, closed.**  No `native_decide`, no axiom beyond the kernel's own
    three, no `sorry`. -/
theorem checkAll_true : Delta4Assembly.checkAll = true :=
  Delta4Assembly.checkAll_of_layers
"""
           + "    " + " ".join("L%d.layer_ok" % n for n in ls) + "\n\n"
           + """/-- **The sharp Δ = 4 pentagon bound**, unconditional. -/
theorem pentagon_bound_delta4_sharp (G : Flag emptyType) (hTF : IsTriangleFree G)
    (hdeg : maxDegree G ≤ 4) :
    pentagonCount G ≤ 4 * G.size :=
  Delta4Assembly.pentagon_bound_delta4_sharp_of_checkAll checkAll_true G hTF hdeg

end Delta4Gen

#print axioms Delta4Gen.checkAll_true
#print axioms Delta4Gen.pentagon_bound_delta4_sharp
""")
    p, m = write("CheckAll", src)
    print("emitted %s" % p)
    return p, m, ["Delta4Gen.checkAll_true", "Delta4Gen.pentagon_bound_delta4_sharp"], 0


def emit_layer_modules(plan):
    """Ordered build list: [(path, module, expected_axiom_decls, nodes)]."""
    out = [emit_masks(plan)]
    modnames = []
    for mod in plan["modules"]:
        r = emit_heavy(plan, mod) if mod["kind"] == "heavy" else emit_slices(plan, mod)
        modnames.append(r[1])
        out.append(r)
    out.append(emit_layer(plan, modnames))
    return out


# ======================================================================== building

AX_RE = re.compile(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)$")


def check_output(stdout, expected):
    """The hygiene gate.  Empty output is FAILURE, never success."""
    if not stdout.strip():
        return False, "EMPTY OUTPUT (a killed process writes nothing -- not success)"
    seen = {}
    for line in stdout.splitlines():
        m = AX_RE.match(line.strip())
        if m:
            axs = set(a.strip() for a in (m.group(2) or "").split(",") if a.strip())
            seen[m.group(1)] = axs
    for name in expected:
        if name not in seen:
            return False, "MISSING `#print axioms %s` line" % name
        bad = seen[name] - OK_AXIOMS
        if bad:
            return False, "%s depends on %s" % (name, sorted(bad))
    if len(seen) != len(expected):
        return False, ("axiom-line count %d != expected %d (%s)"
                       % (len(seen), len(expected), sorted(set(seen) - set(expected))))
    for line in stdout.splitlines():
        if "error" in line.lower() or "sorry" in line.lower():
            return False, "diagnostic in output: " + line.strip()
    return True, "ok"


def build_cmd(path):
    os.makedirs(OLEANDIR, exist_ok=True)
    olean = os.path.join(OLEANDIR, os.path.basename(path)[:-5] + ".olean")
    return "exec lean -o %s %s" % (olean, path)


def build_module(path, module, expected, timeout=14400, kill_after=None):
    # BSD `time -l` reports peak RSS on macOS; GNU time rejects `-l` and Linux
    # often has no /usr/bin/time at all, so measure only where the flag exists
    timer = (["/usr/bin/time", "-l"]
             if sys.platform == "darwin" and os.path.exists("/usr/bin/time") else [])
    cmd = timer + ["lake", "env", "sh", "-c", build_cmd(path)]
    t0 = time.time()
    proc = subprocess.Popen(cmd, cwd=REPO, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, text=True, start_new_session=True)
    killed = False
    if kill_after is not None:
        try:
            out, err = proc.communicate(timeout=kill_after)
        except subprocess.TimeoutExpired:
            # kill the whole process group: `lean` is a grandchild of /usr/bin/time
            try:
                os.killpg(os.getpgid(proc.pid), 9)
            except Exception:
                proc.kill()
            out, err = proc.communicate()
            killed = True
    else:
        out, err = proc.communicate(timeout=timeout)
    wall = time.time() - t0
    rss = None
    m = re.search(r"(\d+)\s+maximum resident set size", err)
    if m:
        rss = int(m.group(1)) / 2 ** 30
    ok = (proc.returncode == 0)
    why = "exit %s" % proc.returncode
    if killed:
        ok, why = False, "KILLED after %.1fs (exit %s)" % (kill_after, proc.returncode)
    if ok:
        ok, why = check_output(out, expected)
    return dict(module=module, path=path, ok=ok, why=why, wall=round(wall, 1),
                rss_gb=None if rss is None else round(rss, 2),
                returncode=proc.returncode, stdout=out, stderr_tail=err[-2000:])


# ============================================================================ CLI

def do_plan(n, verbose=True):
    plan = plan_layer(n)
    if verbose:
        print("layer %d: %d masks, %d nodes, %d slices (%d heavy), %d modules"
              % (n, len(plan["masks"]), plan["total"], len(plan["slices"]),
                 sum(1 for s in plan["slices"] if s[0] == "heavy"),
                 len(plan["modules"]) + 2))
        for i, hp in sorted(plan["heavy"].items()):
            print("  heavy mask %-4d K=%-16d %7d nodes  depth %2d  %5d states  %6d internal"
                  "  %4d chunks" % (i, hp["K"], hp["total"], hp["depth"],
                                    len(hp["frontier"]), hp["internal"], len(hp["chunks"])))
        for mod in plan["modules"]:
            if mod["kind"] == "heavy":
                nodes = sum((2 * plan["heavy"][u[1]]["internal"]) if u[0] == "front"
                            else plan["heavy"][u[1]]["chunks"][u[2]][2] if u[0] == "chunk" else 0
                            for u in mod["units"])
            else:
                nodes = sum(plan["slices"][k][2] for k in mod["slices"])
            print("  module L%d%-6s %-7s %3d kernel decls  %6d nodes  imports %s"
                  % (n, mod["name"], mod["kind"], mod["decls_kernel"], nodes,
                     mod.get("imports") or "-"))
    return plan


def manifest_path(n):
    return os.path.join(GENDIR, "manifest_L%02d.json" % n)


def do_emit(n):
    plan = do_plan(n)
    mods = emit_layer_modules(plan)
    man = dict(
        layer=n, masks=len(plan["masks"]), nodes=plan["total"],
        chunk_ceiling=CHUNK_CEIL, module_node_cap=MODULE_NODE_CAP,
        module_decl_cap=MODULE_DECL_CAP,
        per_mask=[dict(index=i, K=K, nodes=c,
                       cut=(i in plan["heavy"]),
                       depth=plan["heavy"][i]["depth"] if i in plan["heavy"] else None,
                       frontier=len(plan["heavy"][i]["frontier"]) if i in plan["heavy"] else None,
                       internal=plan["heavy"][i]["internal"] if i in plan["heavy"] else None,
                       chunks=len(plan["heavy"][i]["chunks"]) if i in plan["heavy"] else 0)
                  for i, (K, c) in enumerate(zip(plan["masks"], plan["counts"]))],
        slices=[dict(id=k, kind=s[0], first=s[1][0], width=len(s[1]), nodes=s[2])
                for k, s in enumerate(plan["slices"])],
        modules=[dict(module=m[1], file=os.path.basename(m[0]), decls=m[2], nodes=m[3])
                 for m in mods],
        builds=[])
    os.makedirs(GENDIR, exist_ok=True)
    json.dump(man, open(manifest_path(n), "w"), indent=1)
    print("emitted %d modules; manifest %s" % (len(mods), manifest_path(n)))
    return plan, mods, man


def do_build(n, mods=None, man=None):
    if man is None:
        man = json.load(open(manifest_path(n)))
    if mods is None:
        mods = [(os.path.join(GENDIR, m["file"]), m["module"], m["decls"], m["nodes"])
                for m in man["modules"]]
    man["builds"] = []
    allok = True
    for path, module, expected, nodes in mods:
        r = build_module(path, module, expected)
        r.pop("stdout")
        r["nodes"] = nodes
        print("  %-46s %-7s %7.1fs  %s GB  %s"
              % (module, "OK" if r["ok"] else "FAIL", r["wall"], r["rss_gb"], r["why"]),
              flush=True)
        man["builds"].append(r)
        if not r["ok"]:
            allok = False
            print("     stderr tail:\n" + r["stderr_tail"][-1200:])
            break
    man["build_ok"] = allok
    json.dump(man, open(manifest_path(n), "w"), indent=1)
    return allok, man


def do_demo_kill(n):
    man = json.load(open(manifest_path(n)))
    target = next(m for m in man["modules"] if m["nodes"] > 0)
    path = os.path.join(GENDIR, target["file"])
    print("killing a real build of %s after 3.0 s ..." % target["module"])
    r = build_module(path, target["module"], target["decls"], kill_after=3.0)
    print("  harness verdict: %s   (%s)" % ("OK" if r["ok"] else "FAIL", r["why"]))
    ok2, why2 = check_output("", target["decls"])
    print("  check_output on empty stdout: %s   (%s)" % ("OK" if ok2 else "FAIL", why2))
    full = "".join("'%s' depends on axioms: [propext]\n" % d for d in target["decls"])
    okf, whyf = check_output(full, target["decls"])
    print("  check_output on the COMPLETE axiom block a killed build can emit: %s"
          % ("PASSES -- so the exit code is what catches it" if okf else "FAIL (%s)" % whyf))
    return (not r["ok"]) and (not ok2)


def do_project():
    import glob
    meas = [json.load(open(f)) for f in sorted(glob.glob(os.path.join(GENDIR, "manifest_L*.json")))]
    meas = [m for m in meas if m.get("build_ok")]
    if not meas:
        print("no built manifest to project from"); return
    tot_nodes = sum(m["nodes"] for m in meas)
    tot_wall = sum(b["wall"] for m in meas for b in m["builds"])
    base = sum(b["wall"] for m in meas for b in m["builds"] if b["nodes"] == 0)
    nbase = sum(1 for m in meas for b in m["builds"] if b["nodes"] == 0)
    work = tot_wall - base
    per_node = work / max(1, tot_nodes)
    per_mod = base / max(1, nbase)
    rss = max(b["rss_gb"] for m in meas for b in m["builds"] if b["rss_gb"])
    print("measured over layers %s: %d nodes, %.1f s wall (%.1f s fixed over %d zero-node modules)"
          % ([m["layer"] for m in meas], tot_nodes, tot_wall, base, nbase))
    print("  -> %.2f ms/node, %.1f s per zero-node module, peak RSS %.2f GB" % (per_node * 1000, per_mod, rss))
    for n in (9, 10):
        p = plan_layer(n)
        mods = emit_layer_modules_dryrun(p)
        print("  layer %2d: %7d nodes  %3d slices  %2d heavy  %3d modules  %5d kernel decls"
              % (n, p["total"], len(p["slices"]), len(p["heavy"]), len(p["modules"]) + 2,
                 sum(m["decls_kernel"] for m in p["modules"])))
        print("        projected wall %.1f min serial  (%.1f min at -j2)"
              % ((p["total"] * per_node + (len(p["modules"]) + 2) * per_mod) / 60,
                 (p["total"] * per_node + (len(p["modules"]) + 2) * per_mod) / 120))


def emit_layer_modules_dryrun(p):
    return p["modules"]


def main():
    if len(sys.argv) < 2:
        print(__doc__); return 1
    cmd = sys.argv[1]
    if cmd == "plan":
        do_plan(int(sys.argv[2]))
    elif cmd == "emit":
        do_emit(int(sys.argv[2]))
    elif cmd == "build":
        ok, _ = do_build(int(sys.argv[2]))
        return 0 if ok else 1
    elif cmd == "run":
        n = int(sys.argv[2])
        plan, mods, man = do_emit(n)
        ok, man = do_build(n, mods, man)
        print("\nlayer %d: %s  (%d nodes asserted)" % (n, "CLOSED" if ok else "FAILED", man["nodes"]))
        return 0 if ok else 1
    elif cmd == "demo-kill":
        ok = do_demo_kill(int(sys.argv[2]))
        print("\nhygiene demonstration: %s" % ("harness correctly reported FAILURE" if ok
                                               else "HARNESS BUG -- it accepted a killed build"))
        return 0 if ok else 1
    elif cmd == "checkall":
        emit_checkall()
    elif cmd == "project":
        do_project()
    else:
        print(__doc__); return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
