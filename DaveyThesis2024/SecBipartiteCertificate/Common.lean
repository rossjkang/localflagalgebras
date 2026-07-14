/-!
# SecBipartiteCertificate Common helpers

Auto-generated from `local-flags-certificates/emit_lean_cert.py`.
Do NOT edit by hand.

Provides String->Int parsers and helper matrix ops shared by every
per-block PSD witness file under `DaveyThesis2024/SecBipartiteCertificate/Block*.lean`.

The Phase 0.3 stress test established that String-literal encoding +
runtime `parseInts` is the only viable way to ship ≥9k Int values
through Lean elaboration (List literals at this size trigger the O(N^2)
whnf-on-cons elaborator path and time out at `maxHeartbeats=4M`).

The LDL identity is encoded ENTRY-WISE as the integer equation:

  ∀ i, j ∈ [0, dim) :
    Σ_k L_num[i][k] · D_num[k] · L_num[j][k] · scaleFactor[k]
      = scaleYFactor · Y_num[i][j] + lambdaShift · I[i][j]

where `scaleFactor[k] = commonScale / (L_den[k]² · D_den[k])`, and the
RHS uses the precomputed scaleY / lambda integer multipliers. All
per-column denoms are kept separate so individual `L_num` entries stay
small (column-scoped denominator).

This is equivalent to the rational identity
  L · diag(D) · Lᵀ = Y_rat + λI
after clearing each column's denominator into the corresponding
`scaleFactor[k]`.
-/

namespace Davey2024.SecBipartiteCertificate

/-- Parse a comma-separated list of Int. Whitespace-tolerant. -/
def parseInts (s : String) : List Int :=
  s.splitOn "," |>.map (fun tok =>
    match tok.trimAscii.toInt? with
    | some n => n
    | none   => 0)

/-- Parse a semicolon-separated list of rows, each a parseInts. -/
def parseMatrix (s : String) : List (List Int) :=
  s.splitOn ";" |>.map parseInts

/-- Componentwise add over `List Int`. -/
def addVec (a b : List Int) : List Int := List.zipWith (· + ·) a b

/-- Scalar-multiply a vector. -/
def scaleVec (s : Int) (v : List Int) : List Int := v.map (s * ·)

/-- Componentwise add over `List (List Int)`. -/
def addMat (A B : List (List Int)) : List (List Int) :=
  List.zipWith addVec A B

/-- Scalar-multiply a matrix. -/
def scaleMat (s : Int) (A : List (List Int)) : List (List Int) :=
  A.map (scaleVec s)

/-- Sum a list of vectors with an explicit zero vector. -/
def foldAddVec (vs : List (List Int)) (zero : List Int) : List Int :=
  vs.foldl addVec zero

/-- The dim x dim identity matrix scaled by `s` (s on each diagonal, 0 elsewhere). -/
def scaledIdentity (dim : Nat) (s : Int) : List (List Int) :=
  (List.range dim).map (fun i =>
    (List.range dim).map (fun j => if i = j then s else 0))

/-- Compute the LDL^T-derived LHS entry `(i,j)` directly:

      Σ_k L_num[i][k] · D_num[k] · L_num[j][k] · scaleFactor[k]

The Lean call uses `Array` indexing internally for speed (each row
becomes an `Array` once and stays cached during native_decide). -/
def ldlEntry
    (L_num : Array (Array Int)) (D_num : Array Int)
    (scaleFactor : Array Int) (k_count : Nat)
    (i j : Nat) : Int := Id.run do
  let row_i := L_num[i]!
  let row_j := L_num[j]!
  let mut acc : Int := 0
  for k in [0:k_count] do
    acc := acc + row_i[k]! * D_num[k]! * row_j[k]! * scaleFactor[k]!
  pure acc

/-- Construct the full LHS matrix `[[ldlEntry i j | j ∈ range]] | i ∈ range]`. -/
def ldlMatrix
    (L_num : Array (Array Int)) (D_num : Array Int)
    (scaleFactor : Array Int) (dim : Nat) : Array (Array Int) :=
  (Array.range dim).map (fun i =>
    (Array.range dim).map (fun j =>
      ldlEntry L_num D_num scaleFactor dim i j))

/-- Construct the RHS matrix `scaleYFactor · Y + lambdaShift · I` over `Array (Array Int)`. -/
def rhsMatrix
    (Y_num : Array (Array Int)) (scaleYFactor lambdaShift : Int)
    (dim : Nat) : Array (Array Int) :=
  (Array.range dim).map (fun i =>
    (Array.range dim).map (fun j =>
      scaleYFactor * Y_num[i]![j]! + (if i = j then lambdaShift else 0)))

/-- Coerce a parsed `List (List Int)` to `Array (Array Int)`. -/
def listListToArrayArray (xs : List (List Int)) : Array (Array Int) :=
  (xs.map List.toArray).toArray

end Davey2024.SecBipartiteCertificate
