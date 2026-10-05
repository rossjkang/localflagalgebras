import DaveyThesis2024.PentagonQObjective

/-!
# The objective coefficients are the combinatorial weights

`PentagonQObjective.O_Q_weight` reads the size-8 objective's integer weights off
the certificate, by rounding `-target[k] · 6720 / 10¹²`. The paper defines the
same weights combinatorially:

> For `j ∈ [m]` let `n₁(j)` be the number of labelled embeddings of `τ₁` into
> `F_j` such that the four vertices of `F_j` outside the image are adjacent to
> the vertex labelled `1`, and let `n₂(j)`, `n₃(j)` be the numbers of labelled
> embeddings of `τ₂`, `τ₃` into `F_j` such that the three vertices outside the
> image are adjacent to the vertex labelled `1`. Put `μ_j := 4 n₁(j) + n₂(j) +
> 2 n₃(j)`.

Nothing connected the two. The paper conceded the gap in as many words — "that
the program's objective row is the same expansion is taken as given" — and the
weights have been wrong twice, most recently in September 2026, when they were
the 12-digit roundings rather than the exact rationals `μ_j/6720`.

`O_Q_weight_eq_combinatorial` below closes it, over all 9295 basis flags.

## The three types

They are the objective's three summands in
`local-flags-certificates/examples/bounded_pentagon_alt_approach.rs:71,73,78`,
whose weights `1 + 1 + 2` at `:85` become `4 + 1 + 2` after the `6720/1680 = 4`
normalisation that puts the four-vertex type on the five-vertex scale.

Each type is rooted: vertex `0` here is the paper's "vertex labelled `1`", and
the side condition is that every vertex of the flag outside the image is
adjacent to it. The Rust source states the types in its own colour convention
(`0 = black`); they are given below in the `CG2` convention (`1 = black`), to
match `PentagonQBasis.flagBasisCGraph` after its decoder inverts the packed
bit. See that file's colour-convention paragraph.
-/

namespace Davey2024
namespace PentagonQWeights

open Davey2024.PentagonQBasis

/-- A rooted 2-coloured pattern on `n` vertices; the root is vertex `0`. -/
structure Pat where
  /-- Number of vertices. -/
  n : Nat
  /-- Vertex colours, in the `CG2` convention (`1 = black`). -/
  cols : Array Nat
  /-- Adjacency matrix. -/
  padj : Array (Array Bool)

/-- The 5-cycle `0-1-2-3-4-0` with the given colours. -/
def mkC5 (cols : Array Nat) : Pat :=
  { n := 5, cols := cols,
    padj := (Array.range 5).map (fun i => (Array.range 5).map (fun j =>
      (i + 1) % 5 == j || (j + 1) % 5 == i)) }

/-- `τ₁`: the black-red-red-black path on four vertices, rooted at a black
endpoint. This is the pentagon through the root vertex with the root deleted:
two of its neighbours (black) and two non-neighbours (red). -/
def tau1 : Pat :=
  { n := 4, cols := #[1, 0, 0, 1],
    padj := (Array.range 4).map (fun i => (Array.range 4).map (fun j =>
      i + 1 == j || j + 1 == i)) }

/-- `τ₂`: the 5-cycle with exactly one black vertex, rooted at a red vertex at
distance two from it. -/
def tau2 : Pat := mkC5 #[0, 0, 0, 1, 0]

/-- `τ₃`: the 5-cycle with two non-adjacent black vertices, rooted at the red
vertex having exactly one black neighbour. -/
def tau3 : Pat := mkC5 #[0, 0, 1, 0, 1]

/-- Induced colour-preserving embeddings of `p` into `g`, as the list of their
images in vertex order.

Built by depth-first extension, testing each candidate's colour and its
adjacency to every vertex already placed. Pruning at every level is what keeps
this cheap: the unpruned count of injections is `8·7·6·5 + 2·8·7·6·5·4 =
15120` per flag, but almost all die at the first or second vertex. Note that
`cInducedCount` is unsuitable here — it ranges over the whole function space
`Fin n₁ → Fin n₂`, and carries no root condition. -/
def embeds (g : CGraph 8) (p : Pat) : List (List (Fin 8)) :=
  (List.range p.n).foldl (fun partials i =>
    partials.flatMap (fun asg =>
      (List.finRange 8).filterMap (fun v =>
        if (g.col v).val == p.cols[i]! && !asg.contains v &&
           ((List.range i).all (fun j => g.adj (asg[j]!) v == (p.padj[j]!)[i]!))
        then some (asg ++ [v]) else none))) [[]]

/-- Embeddings of `p` into `g` whose every outside vertex is adjacent to the
image of the root. This is the paper's `n_i`. -/
def rootedCount (g : CGraph 8) (p : Pat) : Nat :=
  (embeds g p).countP (fun asg =>
    (List.finRange 8).all (fun w => asg.contains w || g.adj (asg[0]!) w))

/-- `n₁(k)`: rooted embeddings of `τ₁` into basis flag `k`. -/
def n1 (k : Fin basisSize) : Nat := rootedCount (flagBasisCGraph k) tau1

/-- `n₂(k)`: rooted embeddings of `τ₂` into basis flag `k`. -/
def n2 (k : Fin basisSize) : Nat := rootedCount (flagBasisCGraph k) tau2

/-- `n₃(k)`: rooted embeddings of `τ₃` into basis flag `k`. -/
def n3 (k : Fin basisSize) : Nat := rootedCount (flagBasisCGraph k) tau3

set_option linter.style.nativeDecide false in
/-- **The objective row is the combinatorial expansion.**

For every one of the 9295 size-8 basis flags, the integer weight the
certificate carries is exactly the paper's `μ_k = 4 n₁(k) + n₂(k) + 2 n₃(k)`.

This is what lets `O_Q_coef = O_Q_weight / 6720` be read as the exact rational
`μ_k/6720` of the paper's basis combinatorial identity, rather than as an
opaque number lifted from the certificate file. It does **not** prove that
identity, whose asymptotic content remains
`pentagonQ_basis_combinatorial_identity_step1`.

Scope, twice over.

First, this identifies the weights with the **shipped** target vector. That
this vector is the SDPA program's objective row still rests on the emitter, as
`O_Q_coef`'s docstring records.

Second, and more subtly: the counts here are `rootedCount`, a `countP` over the
`embeds` enumerator above. Until 2026-09-29 nothing connected that enumerator
to anything, so this theorem related the certificate's weights only to *its
output*. `PentagonQWeightsBridge.rootedCount_eq_cRootedCount` now proves, at
every one of the 9295 flags, that `rootedCount` equals a count over the same
function space `cInducedCount` ranges over, subject to the root side condition.

The last link was `cRootedCount = genInducedCount` with that side condition.
`CGraphBridge.cInducedCount_eq_genInducedCount'` does the embedding half, and the
root clause — a predicate on the image — needed its own argument.
`PentagonQRooted.cRootedCount_eq_genRootedCount` supplies it, on the standard
axioms, so the chain to `genInducedCount` **is** closed by proof.

That bridge is obligation (a0) of the development notes, and it is a real
prerequisite: the asymptotic identity's proof needs `μ` at the `GenFlag` level,
and cannot consume this theorem until the two `μ`s are the same function. -/
theorem O_Q_weight_eq_combinatorial :
    ∀ k : Fin basisSize,
      PentagonQObjective.O_Q_weight k = 4 * (n1 k : ℤ) + n2 k + 2 * n3 k := by
  native_decide

end PentagonQWeights
end Davey2024
