import DaveyThesis2024.CGraph4Bridge

-- The 334-entry hex String literal is unavoidably long; suppress the per-line
-- linter (the basis is auto-generated; manual wrapping would defeat the point).
set_option linter.style.longLine false
set_option linter.style.nativeDecide false

/-!
# SecAsymBasis — the 334-element size-5 4-vertex-colour plain-edge ∅-flag basis

The genuine **F-free asymmetric** SEC basis enumerated by the Rust `flag-algebra`
crate for `type G = Colored<Graph, 4>`
(`local-flags-certificates/examples/asymmetric_bipartite_strong_density.rs`),
matching the constraint ordering of the solved SDP
(the development notes, "334 flags"). This is the
basis paired with `AsymSecCertificate.target` (the genuine 334-dim objective,
sprs = 1.1373) — **NOT** the symmetric `SecBipartiteCertificate.target`.

## Encoding

Each basis element is a **plain** (uncoloured-edge) graph on 5 vertices with a
4-valued vertex colouring, encoded as a 30-bit packed integer (8 hex chars):

  * bits 0..19  = 10 edge slots × 2 bits each. Plain edges: value 0 = non-edge,
    value 1 = edge. (No edge colour — this is the F-free host.)
  * bits 20..29 = 5 vertex slots × 2 bits each. **RAW 4-colour value 0–3, no
    projection** (`COMP = [0,1,0,1]`, `X_COLS = {0,1}`, `Y_COLS = {2,3}`).

## CG4 host (no collapse)

Unlike the `CG22` projection (which discards the component bit via
`{0,1}→0, {2,3}→1`), the `CG4` decoder keeps the full raw colour:
  * `adj u v`      = (raw edge value > 0)
  * `vertexCol v`  = raw vertex value (`Fin 4`, identity)

296/334 basis flags use colour 2 or 3, so the CG22 high-bit projection would
collapse the component distinction the objective depends on — hence CG4.

## Auto-generated

Packed by the development notes from
the development notes (dump of `dump_flags`).
Roundtrip-verified against the flag colour/edge signatures. Do NOT edit by hand.
-/

namespace Davey2024.SecAsymBasis

open Davey2024

/-! ## Size and parser infrastructure -/

/-- The total number of basis flags (size-5 ∅-typed, asymmetric F-free). -/
def basisSize : Nat := 334

/-- Number of edge slots per flag (`C(5, 2) = 10`). -/
def edgeSlots : Nat := 10

/-- Bits per edge slot. -/
def edgeBitsPer : Nat := 2

/-- Total edge bits per flag (10 × 2 = 20). -/
def edgeBitsTotal : Nat := 20

/-- Bits per vertex colour (2 bits → raw value 0–3). -/
def vertexBitsPer : Nat := 2

/-- Vertex count. -/
def flagOrder : Nat := 5

/-- Total bits per flag (20 + 10 = 30). -/
def totalBits : Nat := 30

/-- Parse a single hex char (0-9 / a-f / A-F) to its Nat value, else 0. -/
def hexCharToNat (c : Char) : Nat :=
  let v := c.toNat
  if v >= '0'.toNat && v <= '9'.toNat then v - '0'.toNat
  else if v >= 'a'.toNat && v <= 'f'.toNat then 10 + (v - 'a'.toNat)
  else if v >= 'A'.toNat && v <= 'F'.toNat then 10 + (v - 'A'.toNat)
  else 0

/-- Parse a hex String (no `0x` prefix) to a Nat. -/
def parseHexStr (s : String) : Nat :=
  s.foldl (fun acc c => acc * 16 + hexCharToNat c) 0

/-- Parse a comma-separated list of hex tokens to an `Array Nat`. -/
def parseHexArr (s : String) : Array Nat :=
  (s.splitOn ",").foldl (fun arr tok => arr.push (parseHexStr tok)) #[]

/-! ## Basis hex String (auto-generated)

334 entries, each an 8-hex-char (30-bit) packed
adjacency + raw-4-colour-vertex bitmap. Single line (no internal newlines) so
every comma-delimited token parses cleanly. -/

def basisHexStr : String :=
  "00000000,00100000,00500000,01500000,05500000,15500000,10055000,30055000,05555000,25555000,10255000,30255000,10a55000,30a55000,12a55000,32a55000,1aa55000,05755000,25755000,05f55000,25f55000,07f55000,27f55000,0ff55000,14015500,34015500,1c015500,3c015500,14815500,34815500,1c815500,3c815500,16815500,36815500,1e815500,3e815500,01515500,21515500,09515500,29515500,01d15500,21d15500,09d15500,29d15500,03d15500,23d15500,0bd15500,2bd15500,14215500,34215500,1c215500,3c215500,14a15500,34a15500,1ca15500,3ca15500,16a15500,36a15500,1ea15500,01715500,21715500,09715500,29715500,01f15500,21f15500,09f15500,29f15500,03f15500,23f15500,0bf15500,05454040,25454040,0d454040,2d454040,05c54040,25c54040,0dc54040,2dc54040,07c54040,27c54040,0fc54040,2fc54040,10154040,30154040,18154040,38154040,10954040,30954040,18954040,38954040,12954040,32954040,1a954040,3a954040,05654040,25654040,0d654040,2d654040,05e54040,25e54040,0de54040,2de54040,07e54040,27e54040,0fe54040,10354040,30354040,18354040,38354040,10b54040,30b54040,18b54040,38b54040,12b54040,32b54040,1ab54040,04000540,14000540,0c000540,1c000540,01500540,11500540,09500540,19500540,04200540,14200540,0c200540,1c200540,04a00540,14a00540,0ca00540,1ca00540,06a00540,16a00540,01700540,11700540,09700540,19700540,01f00540,11f00540,09f00540,19f00540,03f00540,13f00540,14015540,1c015540,3c015540,01515540,09515540,29515540,14215540,1c215540,3c215540,14a15540,1ca15540,3ca15540,16a15540,1ea15540,01715540,09715540,29715540,01f15540,09f15540,29f15540,03f15540,0bf15540,05050104,25050104,07050104,27050104,0f050104,2f050104,10550104,30550104,12550104,32550104,1a550104,3a550104,05250104,25250104,0d250104,2d250104,07250104,27250104,0f250104,2f250104,05a50104,25a50104,07a50104,27a50104,0fa50104,10750104,30750104,18750104,38750104,12750104,32750104,1a750104,3a750104,10f50104,30f50104,12f50104,32f50104,1af50104,04100504,14100504,0c100504,1c100504,06100504,16100504,0e100504,1e100504,01600504,11600504,09600504,19600504,03600504,13600504,0b600504,1b600504,04300504,14300504,0c300504,1c300504,06300504,16300504,0e300504,1e300504,04b00504,14b00504,0cb00504,1cb00504,06b00504,16b00504,01000014,05000014,15000014,03000014,07000014,17000014,00500014,04500014,14500014,02500014,06500014,16500014,01200014,05200014,15200014,03200014,07200014,17200014,01a00014,05a00014,15a00014,00700014,04700014,14700014,02700014,06700014,16700014,00f00014,04f00014,14f00014,00100001,01100001,05100001,15100001,00600001,01600001,05600001,15600001,00300001,01300001,05300001,15300001,10150001,30150001,05150001,25150001,12150001,32150001,1a150001,07150001,27150001,0f150001,10650001,30650001,05650001,25650001,12650001,32650001,1a650001,07650001,27650001,0f650001,10350001,30350001,05350001,25350001,12350001,32350001,1a350001,07350001,27350001,0f350001,01100401,11100401,01600401,11600401,06600401,16600401,01300401,11300401,06300401,16300401,03300401,13300401,04100505,14100505,01600505,11600505,09600505,19600505,04300505,14300505,0c300505,1c300505,04b00505,14b00505,0cb00505,1cb00505,06b00505,16b00505"

/-! ## Computable basis array -/

/-- The 334-element basis array. Each entry is a 30-bit packed integer per the
    encoding documented at the top of this file. -/
def basisAdjArr : Array Nat := parseHexArr basisHexStr

/-- Sanity check: the basis array has the expected size. -/
theorem basisAdjArr_size : basisAdjArr.size = basisSize := by native_decide

/-! ## Bit-extraction helpers -/

/-- Edge index (u, v) with u < v in the SymNonRefl layout (matches Rust). -/
def edgeIndexNat (u v : Nat) : Nat := v * (v - 1) / 2 + u

/-- Extract a 2-bit window at `pos` from `n`. -/
def twoBitsAt (n : Nat) (pos : Nat) : Nat := (n >>> pos) &&& 3

/-- Decode the raw 2-bit edge value at index `i` (assume `i < 10`). -/
def extractEdgeRaw (e : Nat) (i : Nat) : Nat := twoBitsAt e (i * edgeBitsPer)

/-- Decode the raw 2-bit vertex-colour value at vertex `v` (assume `v < 5`). -/
def extractVertexRaw (e : Nat) (v : Nat) : Nat :=
  twoBitsAt e (edgeBitsTotal + v * vertexBitsPer)

/-- Decode the adjacency between vertices `u` and `v` (need not be ordered).
    Plain edges: adjacent iff the raw edge value is positive. -/
def extractAdj (e : Nat) (u v : Fin flagOrder) : Bool :=
  if u.val < v.val then
    extractEdgeRaw e (edgeIndexNat u.val v.val) > 0
  else if v.val < u.val then
    extractEdgeRaw e (edgeIndexNat v.val u.val) > 0
  else
    false

/-- Decode the CG4 vertex colour as `Fin 4` — the **raw** value 0–3 (identity,
    NO high-bit projection). This is the whole point of CG4: the component bit
    (low bit of the colour) is preserved, unlike the CG22 `extractVertexCol22`. -/
def extractVertexCol4 (e : Nat) (v : Fin flagOrder) : Fin 4 :=
  ⟨extractVertexRaw e v.val % 4, Nat.mod_lt _ (by decide)⟩

/-! ## Basis as `CGraph4 5` and `GenFlag CG4` -/

/-- The `k`-th basis flag, as a computable `CGraph4 5`. -/
def flagBasisCGraph4 (k : Fin basisSize) : CGraph4 flagOrder where
  adj u v := extractAdj (basisAdjArr[k.val]!) u v
  vertexCol v := extractVertexCol4 (basisAdjArr[k.val]!) v

/-- The `k`-th basis flag, as a `GenFlag CG4 (GenFlagType.empty CG4)`.

    This is the public entry point for the restated asymmetric objective
    (L5.C) — paired with `AsymSecCertificate.target`. -/
noncomputable def flagBasis_asym (k : Fin basisSize) :
    GenFlag CG4 (GenFlagType.empty CG4) :=
  (flagBasisCGraph4 k).toGenFlag

/-- The size of every basis flag is 5. -/
theorem flagBasis_asym_size (k : Fin basisSize) :
    (flagBasis_asym k).size = flagOrder := rfl

/-! ## Smoke tests -/

/-- The basis really has the expected number of entries (via `native_decide`). -/
theorem basisAdjArr_card : basisAdjArr.size = 334 := by native_decide

/-- Spot check: the first basis flag is the empty graph with all-zero colours
    (matches the canonical-form enumeration's `flag[0]`). -/
theorem basisAdjArr_first_entry : basisAdjArr[0]! = 0 := by native_decide

/-- Smoke test: the first basis flag's decoder really sees an empty graph. -/
theorem flagBasisCGraph4_zero_no_adj : ∀ u v : Fin flagOrder,
    (flagBasisCGraph4 ⟨0, by native_decide⟩).adj u v = false := by native_decide

/-- Smoke test: the first basis flag's vertex colours are all 0. -/
theorem flagBasisCGraph4_zero_vertexCol_zero : ∀ v : Fin flagOrder,
    (flagBasisCGraph4 ⟨0, by native_decide⟩).vertexCol v = 0 := by native_decide

/-- Provenance spot check: basis flag 25 decodes to colours (0,0,0,1,3) — it
    genuinely uses colour 3 (a `Y_COLS`/comp1 mark that the CG22 high-bit
    projection would fold into a plain colour-1). -/
theorem flagBasisCGraph4_25_colours :
    ((flagBasisCGraph4 ⟨25, by native_decide⟩).vertexCol ⟨0, by native_decide⟩).val = 0 ∧
    ((flagBasisCGraph4 ⟨25, by native_decide⟩).vertexCol ⟨1, by native_decide⟩).val = 0 ∧
    ((flagBasisCGraph4 ⟨25, by native_decide⟩).vertexCol ⟨2, by native_decide⟩).val = 0 ∧
    ((flagBasisCGraph4 ⟨25, by native_decide⟩).vertexCol ⟨3, by native_decide⟩).val = 1 ∧
    ((flagBasisCGraph4 ⟨25, by native_decide⟩).vertexCol ⟨4, by native_decide⟩).val = 3 := by
  native_decide

end Davey2024.SecAsymBasis
