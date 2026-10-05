# The Δ = 4 layer generator

This directory holds the generator for the machine-written Lean modules in
`DaveyThesis2024/Delta4/Generated/`, which carry the finite check behind

```lean
Delta4Gen.pentagon_bound_delta4_sharp :
  ∀ (G : Flag emptyType), IsTriangleFree G → maxDegree G ≤ 4 → pentagonCount G ≤ 4 * G.size
-- depends on axioms: [propext, Classical.choice, Quot.sound]
```

Those are the three standard kernel axioms.  The proof uses no `native_decide`,
no compiled evaluation, no external enumerator and no domain axiom, and leaves
no hypothesis open.

## Files

| file | role |
|---|---|
| `gen_layer.py` | emits one layer's modules, compiles them, and records a manifest |
| `model_a.py` | search model A — incremental, used by the generator |
| `model_b.c` | search model B — recomputes every prune quantity from scratch |

Models A and B are independent implementations of the same pruned search; the
generator cross-checks their node counts before it writes a layer.  Build the
second with `cc -O2 -o model_b model_b.c`.

## What is checked

`Delta4Assembly.checkAll` ranges over the 862 attachment-mask multisets a vertex
of a triangle-free graph of maximum degree four can present, in 2,685,792 pruned
search nodes.  Each layer is closed by `msCnt n M = (N, 0)` — a node count and a
violation count — with the mask list `M` tied to the generator by a
kernel-proved, axiom-free `M_eq`.  The node count matters: `LayerOK n` is a
closed decidable proposition, so a bare `LayerOK` proof is definitionally
transferable between layers and the count is the only thing that distinguishes
one layer's theorem from another's.

The ten layer counts are 1, 14, 92, 3764, 28957, 282124, 793508, 1577325, 6, 1,
with zero violations throughout.

## Rebuilding

The generated modules are deliberately **not** imported from
`DaveyThesis2024.lean`.  The generator invokes `lean -o` directly and writes no
lake traces, so importing them from the root would make every ordinary
`lake build` re-pay the roughly two-hour census.  The sources are tracked; the
oleans are not.  This is a build-ergonomics decision, not a soundness one.

To reproduce the check from scratch, from this directory:

```sh
python3 gen_layer.py build 9      # ~35 min, 17 modules
python3 gen_layer.py build 10     # ~90 min, 35 modules
python3 gen_layer.py checkall     # emits ../CheckAll.lean
```

Layers 0–8, 11 and 12 take about 14 minutes together (`build <n>` for each).
Peak resident memory is 4.8–6.0 GB per module.  Then compile the assembled
check and read its axiom line:

```sh
cd ../../../..                    # repo root
lake build                        # the hand-written development
lake env sh -c 'LEAN_PATH=$LEAN_PATH:$PWD/.lake/build/lib/lean \
  lean -o .lake/build/lib/lean/DaveyThesis2024/Delta4/Generated/CheckAll.olean \
       DaveyThesis2024/Delta4/Generated/CheckAll.lean'
```

`CheckAll.lean` ends with `#print axioms` on both theorems, so that command
prints

```
'Delta4Gen.checkAll_true' depends on axioms: [propext, Classical.choice, Quot.sound]
'Delta4Gen.pentagon_bound_delta4_sharp' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Staleness: when the generated oleans must be rebuilt

The generated modules are compiled by `lean -o` directly, outside lake, so lake
does not track them and nothing forces a rebuild when something they depend on
changes.  Lean does not re-typecheck an olean when it loads it, so a *semantic*
change anywhere in `DaveyThesis2024/Delta4/` or its imports --- notably
`PentagonDelta4.lean`, which `Delta4/BallInvariance.lean` and
`Delta4/Transport.lean` both import --- can leave stale generated oleans that
still load and still print a clean axiom line while resting on definitions that
no longer exist in that form.

So: **after changing anything in the Delta4 import closure, recompile the
generated tree before trusting its axiom line.**  Comment and docstring edits
are safe; anything touching a definition, a statement or a proof is not.  The
cheap check is to recompile the layers (`python3 gen_layer.py build <n>` for
each) rather than only `CheckAll.lean`, which typechecks its own text but takes
the layer oleans on trust.

The per-layer manifests `../manifest_L*.json` record what was emitted and how
long each module took on the run that produced the tracked sources.
