import DaveyThesis2024.PentagonConjecture


/-!
# SDP Certificate Flags for BRRB Bound

All 58 size-5 2-coloured triangle-free flags from the BRRB SDP certificate.
Generated automatically from `flags_enumeration.txt`.

## ⚠️ MISLEADING NAMING (2026-05-05 finding, programmatic verification)

**NONE of the 55 `sdpFN` definitions here structurally equal Rust enumeration
entry `F_N`.** All are colour-flipped: the auto-generation script copied Rust
integer colour values literally without applying the Lean ↔ Rust convention
swap (Rust 0=BLACK, Lean 1=BLACK).

Two categories of sdpFN:

### Category A: 10 valid BRRB flags (match some Rust F_M ≠ F_N)

These coincide with the colour-complement entry in the BRRB enumeration. They
ARE referenced by σᵢ_nonneg goals and linSum_decomposition_identity:

| Lean def | Structurally equals | Used in       |
|----------|---------------------|---------------|
| `sdpF2`  | Rust F6             | (unused — but `certF6` is the right def) |
| `sdpF6`  | Rust F2             | linSum_decomposition_identity LHS |
| `sdpF7`  | Rust F13            | σ₂_nonneg, linSum LHS |
| `sdpF13` | Rust F7             | linSum LHS    |
| `sdpF18` | Rust F20            | linSum LHS    |
| `sdpF20` | Rust F18            | σ₂_nonneg, linSum LHS |
| `sdpF30` | Rust F33            | σ₂_nonneg, linSum LHS |
| `sdpF33` | Rust F30            | linSum LHS    |
| `sdpF35` | Rust F40            | (unused)      |
| `sdpF40` | Rust F35            | (unused)      |

### Category B: 45 invalid (non-BRRB) flags

The remaining 45 sdpFN have structures that fail BRRB validity (BB-edges, or
no connected B-vertex, or both). Examples: `sdpF1` is 5 isolated red vertices
(no B vertex anywhere — fails BRRB connectivity); `sdpF3` is K_{1,4} with
`[B,R,R,R,B]` (B-B edge between centre and one leaf — fails black-indep).

These 45 are **dead defs** — auto-generation artefacts, not referenced by any
cert combination or proof. Phase 6 cleanup should delete them.

### Why σᵢ_nonneg goals and linSum_decomposition_identity still work

The σᵢ_nonneg docstrings in `SdpEvaluation.lean` correctly identify the
actual Rust position (e.g. "cert F₁₃ → Lean sdpF7"). The named-flag
combination evaluates correctly because the references resolve to Lean defs
matching the right Rust structures (just under misleading names).

By contrast, `certFN`, `flagN`, `sdpFlagN` (in `PentagonConjecture.lean`)
are correctly identified — `certF6` = Rust F6 structurally, not `sdpF6`.

### Phase 6 cleanup TODO

1. **Delete the 45 invalid sdpFN** (dead defs).
2. **Rename the 10 valid sdpFN** to indicate actual Rust position
   (`sdpF6` → `sdpF2_named` or similar; or just merge with the existing
   `flagN`/`sdpFlagN`/`certFN` if structurally equivalent).
3. Update all `_iso_sdpFN` theorems and σᵢ_nonneg goal references.

~150-250 LOC of mechanical cleanup. Not blocking any proofs; pure clarity.

### Verification script

`/tmp/verify_sdpfn.py` (one-off) parses both `SdpFlags.lean` and
`flags_enumeration.txt`, verifies each sdpFN's structure against the
Rust enumeration with proper convention conversion, and produces the table
above. Can be re-run if SdpFlags.lean changes.
-/

namespace Davey2024

open Classical

noncomputable def sdpF6 : GenFlag CG2 (GenFlagType.empty CG2) where
  size := 5
  str := (SimpleGraph.fromRel (fun u v : Fin 5 =>
        (u.val = 0 ∧ v.val = 4) ∨
        (u.val = 1 ∧ v.val = 4) ∨
        (u.val = 2 ∧ v.val = 4) ∨
        (u.val = 3 ∧ v.val = 4)),
    fun v : Fin 5 => if v.val = 0 then (1 : Fin 2) else if v.val = 1 then (1 : Fin 2) else if v.val = 2 then (1 : Fin 2) else if v.val = 3 then (1 : Fin 2) else if v.val = 4 then (0 : Fin 2) else 0)
  embedding := ⟨Fin.elim0, fun {a} => Fin.elim0 a⟩
  isInduced := CG2.comap_elim0 _ _
  hsize := Nat.zero_le _

noncomputable def sdpF7 : GenFlag CG2 (GenFlagType.empty CG2) where
  size := 5
  str := (SimpleGraph.fromRel (fun u v : Fin 5 =>
        (u.val = 0 ∧ v.val = 4) ∨
        (u.val = 1 ∧ v.val = 3) ∨
        (u.val = 1 ∧ v.val = 4) ∨
        (u.val = 2 ∧ v.val = 3) ∨
        (u.val = 2 ∧ v.val = 4)),
    fun v : Fin 5 => if v.val = 0 then (0 : Fin 2) else if v.val = 1 then (0 : Fin 2) else if v.val = 2 then (0 : Fin 2) else if v.val = 3 then (1 : Fin 2) else if v.val = 4 then (1 : Fin 2) else 0)
  embedding := ⟨Fin.elim0, fun {a} => Fin.elim0 a⟩
  isInduced := CG2.comap_elim0 _ _
  hsize := Nat.zero_le _

-- sdpF9 already defined as sdpFlag9 in PentagonConjecture.lean

noncomputable def sdpF13 : GenFlag CG2 (GenFlagType.empty CG2) where
  size := 5
  str := (SimpleGraph.fromRel (fun u v : Fin 5 =>
        (u.val = 0 ∧ v.val = 4) ∨
        (u.val = 1 ∧ v.val = 3) ∨
        (u.val = 1 ∧ v.val = 4) ∨
        (u.val = 2 ∧ v.val = 3) ∨
        (u.val = 2 ∧ v.val = 4)),
    fun v : Fin 5 => if v.val = 0 then (1 : Fin 2) else if v.val = 1 then (1 : Fin 2) else if v.val = 2 then (1 : Fin 2) else if v.val = 3 then (0 : Fin 2) else if v.val = 4 then (0 : Fin 2) else 0)
  embedding := ⟨Fin.elim0, fun {a} => Fin.elim0 a⟩
  isInduced := CG2.comap_elim0 _ _
  hsize := Nat.zero_le _

noncomputable def sdpF18 : GenFlag CG2 (GenFlagType.empty CG2) where
  size := 5
  str := (SimpleGraph.fromRel (fun u v : Fin 5 =>
        (u.val = 0 ∧ v.val = 3) ∨
        (u.val = 1 ∧ v.val = 4) ∨
        (u.val = 2 ∧ v.val = 4) ∨
        (u.val = 3 ∧ v.val = 4)),
    fun v : Fin 5 => if v.val = 0 then (0 : Fin 2) else if v.val = 1 then (1 : Fin 2) else if v.val = 2 then (1 : Fin 2) else if v.val = 3 then (1 : Fin 2) else if v.val = 4 then (0 : Fin 2) else 0)
  embedding := ⟨Fin.elim0, fun {a} => Fin.elim0 a⟩
  isInduced := CG2.comap_elim0 _ _
  hsize := Nat.zero_le _

noncomputable def sdpF20 : GenFlag CG2 (GenFlagType.empty CG2) where
  size := 5
  str := (SimpleGraph.fromRel (fun u v : Fin 5 =>
        (u.val = 0 ∧ v.val = 3) ∨
        (u.val = 1 ∧ v.val = 4) ∨
        (u.val = 2 ∧ v.val = 4) ∨
        (u.val = 3 ∧ v.val = 4)),
    fun v : Fin 5 => if v.val = 0 then (1 : Fin 2) else if v.val = 1 then (0 : Fin 2) else if v.val = 2 then (0 : Fin 2) else if v.val = 3 then (0 : Fin 2) else if v.val = 4 then (1 : Fin 2) else 0)
  embedding := ⟨Fin.elim0, fun {a} => Fin.elim0 a⟩
  isInduced := CG2.comap_elim0 _ _
  hsize := Nat.zero_le _

noncomputable def sdpF30 : GenFlag CG2 (GenFlagType.empty CG2) where
  size := 5
  str := (SimpleGraph.fromRel (fun u v : Fin 5 =>
        (u.val = 0 ∧ v.val = 3) ∨
        (u.val = 0 ∧ v.val = 4) ∨
        (u.val = 1 ∧ v.val = 3) ∨
        (u.val = 1 ∧ v.val = 4) ∨
        (u.val = 2 ∧ v.val = 3) ∨
        (u.val = 2 ∧ v.val = 4)),
    fun v : Fin 5 => if v.val = 0 then (0 : Fin 2) else if v.val = 1 then (0 : Fin 2) else if v.val = 2 then (0 : Fin 2) else if v.val = 3 then (1 : Fin 2) else if v.val = 4 then (1 : Fin 2) else 0)
  embedding := ⟨Fin.elim0, fun {a} => Fin.elim0 a⟩
  isInduced := CG2.comap_elim0 _ _
  hsize := Nat.zero_le _

noncomputable def sdpF33 : GenFlag CG2 (GenFlagType.empty CG2) where
  size := 5
  str := (SimpleGraph.fromRel (fun u v : Fin 5 =>
        (u.val = 0 ∧ v.val = 3) ∨
        (u.val = 0 ∧ v.val = 4) ∨
        (u.val = 1 ∧ v.val = 3) ∨
        (u.val = 1 ∧ v.val = 4) ∨
        (u.val = 2 ∧ v.val = 3) ∨
        (u.val = 2 ∧ v.val = 4)),
    fun v : Fin 5 => if v.val = 0 then (1 : Fin 2) else if v.val = 1 then (1 : Fin 2) else if v.val = 2 then (1 : Fin 2) else if v.val = 3 then (0 : Fin 2) else if v.val = 4 then (0 : Fin 2) else 0)
  embedding := ⟨Fin.elim0, fun {a} => Fin.elim0 a⟩
  isInduced := CG2.comap_elim0 _ _
  hsize := Nat.zero_le _

-- sdpF37 already defined as sdpFlag37 in PentagonConjecture.lean

-- sdpF55 already defined as sdpFlag55 in PentagonConjecture.lean

/-! ### cs0 flag isomorphisms to SDP flags

These lemmas show that the cs0 product-forget flags are isomorphic to specific
SDP certificate flags, enabling `phi.eval_iso` rewrites in the cs0 summation.
-/

-- S0F33 ≅ certF4: K_{1,4} R-centre + 2R + 2B leaves (post-fix iso class).
-- S0F33 (centre v0): edges 0-1,0-2,0-3,0-4; colours R,B,B,R,R.
-- certF4 (centre v4): edges 0-4,1-4,2-4,3-4; colours R,R,B,B,R.
-- Iso: v0(R-centre)→v4; v1(B)→v2, v2(B)→v3 (B-leaves); v3(R)→v0, v4(R)→v1 (R-leaves).
set_option maxHeartbeats 800000 in
theorem S0F33_iso_certF4 :
    GenFlagIso (GenFlagType.empty CG2) cs0_flag_S0F33 certF4 := by
  let fwd : Fin 5 → Fin 5 := fun x => match x.val with
    | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | _ => 1
  let inv : Fin 5 → Fin 5 := fun x => match x.val with
    | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | _ => 0
  refine ⟨⟨fwd, inv, fun x => by fin_cases x <;> rfl, fun x => by fin_cases x <;> rfl⟩, ?_, fun i => Fin.elim0 i⟩
  · simp only [colouredGraphUniverse, cs0_flag_S0F33, certF4]
    apply Prod.ext
    · ext u v
      simp only [SimpleGraph.comap_adj, SimpleGraph.fromRel_adj]
      fin_cases u <;> fin_cases v <;> simp [fwd, inv]
    · ext i; fin_cases i <;> simp [fwd, inv]

-- S0F44 ≅ sdpF20: path-like, 2 black + 3 red
set_option maxHeartbeats 800000 in
theorem S0F44_iso_sdpF20 :
    GenFlagIso (GenFlagType.empty CG2) cs0_flag_S0F44 sdpF20 := by
  let fwd : Fin 5 → Fin 5 := fun x => match x.val with
    | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | _ => 2
  let inv : Fin 5 → Fin 5 := fun x => match x.val with
    | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | _ => 1
  refine ⟨⟨fwd, inv, fun x => by fin_cases x <;> rfl, fun x => by fin_cases x <;> rfl⟩, ?_, fun i => Fin.elim0 i⟩
  · simp only [colouredGraphUniverse, cs0_flag_S0F44, sdpF20]
    apply Prod.ext
    · ext u v
      simp only [SimpleGraph.comap_adj, SimpleGraph.fromRel_adj]
      fin_cases u <;> fin_cases v <;> simp [fwd, inv]
    · ext i; fin_cases i <;> simp [fwd, inv]

-- S0F46 ≅ sdpF7: 5-edge flag, 3 red + 2 black
set_option maxHeartbeats 800000 in
theorem S0F46_iso_sdpF7 :
    GenFlagIso (GenFlagType.empty CG2) cs0_flag_S0F46 sdpF7 := by
  let fwd : Fin 5 → Fin 5 := fun x => match x.val with
    | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 0 | _ => 2
  let inv : Fin 5 → Fin 5 := fun x => match x.val with
    | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 2 | _ => 1
  refine ⟨⟨fwd, inv, fun x => by fin_cases x <;> rfl, fun x => by fin_cases x <;> rfl⟩, ?_, fun i => Fin.elim0 i⟩
  · simp only [colouredGraphUniverse, cs0_flag_S0F46, sdpF7]
    apply Prod.ext
    · ext u v
      simp only [SimpleGraph.comap_adj, SimpleGraph.fromRel_adj]
      fin_cases u <;> fin_cases v <;> simp [fwd, inv]
    · ext i; fin_cases i <;> simp [fwd, inv]

-- S0F66 ≅ sdpF30: K_{3,2}, 3 red + 2 black
set_option maxHeartbeats 800000 in
theorem S0F66_iso_sdpF30 :
    GenFlagIso (GenFlagType.empty CG2) cs0_flag_S0F66 sdpF30 := by
  let fwd : Fin 5 → Fin 5 := fun x => match x.val with
    | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | _ => 2
  let inv : Fin 5 → Fin 5 := fun x => match x.val with
    | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | _ => 2
  refine ⟨⟨fwd, inv, fun x => by fin_cases x <;> rfl, fun x => by fin_cases x <;> rfl⟩, ?_, fun i => Fin.elim0 i⟩
  · simp only [colouredGraphUniverse, cs0_flag_S0F66, sdpF30]
    apply Prod.ext
    · ext u v
      simp only [SimpleGraph.comap_adj, SimpleGraph.fromRel_adj]
      fin_cases u <;> fin_cases v <;> simp [fwd, inv]
    · ext i; fin_cases i <;> simp [fwd, inv]

-- S0F34F ≅ certF22: tree deg-seq [3,2,1,1,1], colours [R,B,B,R,R].
-- S0F34F: edges 0-1,0-2,0-3,1-4; colours R,B,B,R,R. v0=deg-3-R, v1=deg-2-B,
--   leaves: v2(B),v3(R),v4(R).
-- certF22: edges 0-3,1-4,2-4,3-4; colours R,R,B,B,R. v4=deg-3-R, v3=deg-2-B,
--   leaves: v0(R),v1(R),v2(B).
-- Iso (involution): v0↔v4, v1↔v3, v2↔v2 (B-leaf to B-leaf).
set_option maxHeartbeats 800000 in
theorem S0F34F_iso_certF22 :
    GenFlagIso (GenFlagType.empty CG2) cs0_flag_S0F34F certF22 := by
  let fwd : Fin 5 → Fin 5 := fun x => match x.val with
    | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | _ => 0
  let inv : Fin 5 → Fin 5 := fwd
  refine ⟨⟨fwd, inv, fun x => by fin_cases x <;> rfl, fun x => by fin_cases x <;> rfl⟩, ?_, fun i => Fin.elim0 i⟩
  · simp only [colouredGraphUniverse, cs0_flag_S0F34F, certF22]
    apply Prod.ext
    · ext u v
      simp only [SimpleGraph.comap_adj, SimpleGraph.fromRel_adj]
      fin_cases u <;> fin_cases v <;> simp [fwd]
    · ext i; fin_cases i <;> simp [fwd]

-- S0F34T ≅ certF8: 4-cycle + leaf, deg-seq [3,2,2,2,1], colours [R,B,B,R,R].
-- S0F34T: edges 0-1,0-2,0-3,1-4,3-4; colours R,B,B,R,R. v0=deg-3-R+leaf v2(B);
--   cycle v0-v1-v4-v3-v0 with colours R-B-R-R.
-- certF8: edges 0-4,1-3,1-4,2-3,2-4; colours B,R,B,R,R. v4=deg-3-R+leaf v0(B);
--   cycle v4-v1-v3-v2-v4 with colours R-R-R-B.
-- Iso: v0→v4 (deg-3-R); v2→v0 (B-leaf); v1→v2 (B on cycle adjacent to deg-3-R);
--   v3→v1 (other R cycle neighbour of deg-3); v4→v3 (R between B and R).
set_option maxHeartbeats 800000 in
theorem S0F34T_iso_certF8 :
    GenFlagIso (GenFlagType.empty CG2) cs0_flag_S0F34T certF8 := by
  let fwd : Fin 5 → Fin 5 := fun x => match x.val with
    | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | _ => 3
  let inv : Fin 5 → Fin 5 := fun x => match x.val with
    | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | _ => 0
  refine ⟨⟨fwd, inv, fun x => by fin_cases x <;> rfl, fun x => by fin_cases x <;> rfl⟩, ?_, fun i => Fin.elim0 i⟩
  · simp only [colouredGraphUniverse, cs0_flag_S0F34T, certF8]
    apply Prod.ext
    · ext u v
      simp only [SimpleGraph.comap_adj, SimpleGraph.fromRel_adj]
      fin_cases u <;> fin_cases v <;> simp [fwd, inv]
    · ext i; fin_cases i <;> simp [fwd, inv]

-- S0F36F ≅ certF11: 4-cycle + leaf, deg-seq [3,2,2,2,1], colours [R,B,B,R,R].
-- S0F36F: edges 0-1,0-2,0-3,1-4,2-4; colours R,B,B,R,R. v0=deg-3-R+leaf v3(R);
--   cycle v0-v1-v4-v2-v0 with colours R-B-R-B.
-- certF11: edges 0-4,1-3,1-4,2-3,2-4; colours R,B,B,R,R. v4=deg-3-R+leaf v0(R);
--   cycle v4-v1-v3-v2-v4 with colours R-B-R-B.
-- Iso: v0→v4 (deg-3-R+leaf), v3→v0 (R-leaf), v4→v3 (R-cycle-opposite),
--   v1→v1, v2→v2 (B on cycle).
set_option maxHeartbeats 800000 in
theorem S0F36F_iso_certF11 :
    GenFlagIso (GenFlagType.empty CG2) cs0_flag_S0F36F certF11 := by
  let fwd : Fin 5 → Fin 5 := fun x => match x.val with
    | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 0 | _ => 3
  let inv : Fin 5 → Fin 5 := fun x => match x.val with
    | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 4 | _ => 0
  refine ⟨⟨fwd, inv, fun x => by fin_cases x <;> rfl, fun x => by fin_cases x <;> rfl⟩, ?_, fun i => Fin.elim0 i⟩
  · simp only [colouredGraphUniverse, cs0_flag_S0F36F, certF11]
    apply Prod.ext
    · ext u v
      simp only [SimpleGraph.comap_adj, SimpleGraph.fromRel_adj]
      fin_cases u <;> fin_cases v <;> simp [fwd, inv]
    · ext i; fin_cases i <;> simp [fwd, inv]

-- S0F36T ≅ certF31: K_{3,2} with mixed colours, deg-seq [3,3,2,2,2].
-- S0F36T: edges 0-1,0-2,0-3,1-4,2-4,3-4; colours R,B,B,R,R. Bipartite parts:
--   {v0(R-deg3), v4(R-deg3)} and {v1(B), v2(B), v3(R)}.
-- certF31: edges 0-3,0-4,1-3,1-4,2-3,2-4; colours R,B,B,R,R. Bipartite parts:
--   {v3(R-deg3), v4(R-deg3)} and {v0(R), v1(B), v2(B)}.
-- Iso (involution): v0↔v3, v4↔v4 (deg-3 R), v1↔v1, v2↔v2 (B).
set_option maxHeartbeats 800000 in
theorem S0F36T_iso_certF31 :
    GenFlagIso (GenFlagType.empty CG2) cs0_flag_S0F36T certF31 := by
  let fwd : Fin 5 → Fin 5 := fun x => match x.val with
    | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | _ => 4
  let inv : Fin 5 → Fin 5 := fwd
  refine ⟨⟨fwd, inv, fun x => by fin_cases x <;> rfl, fun x => by fin_cases x <;> rfl⟩, ?_, fun i => Fin.elim0 i⟩
  · simp only [colouredGraphUniverse, cs0_flag_S0F36T, certF31]
    apply Prod.ext
    · ext u v
      simp only [SimpleGraph.comap_adj, SimpleGraph.fromRel_adj]
      fin_cases u <;> fin_cases v <;> simp [fwd]
    · ext i; fin_cases i <;> simp [fwd]

-- S0F45F ≅ sdpF35: 4-edge path-like flag
set_option maxHeartbeats 800000 in
/-- `t2_v1_d.forget ≅ sdpF20`. Mapping (v0,v1,v2,v3,w) → (v4,v3,v1,v2,v0). -/
theorem t2_v1_d_forget_iso :
    GenFlagIso (GenFlagType.empty CG2) t2_v1_d.forget sdpF20 := by
  let fwd : Fin 5 → Fin 5 := fun x => match x.val with
    | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 2 | _ => 0
  let inv : Fin 5 → Fin 5 := fun x => match x.val with
    | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 1 | _ => 0
  refine ⟨⟨fwd, inv, fun x => by fin_cases x <;> rfl, fun x => by fin_cases x <;> rfl⟩, ?_, fun i => Fin.elim0 i⟩
  simp only [colouredGraphUniverse, t2_v1_d, sdpF20, GenFlag.forget]
  apply Prod.ext
  · ext u v
    simp only [SimpleGraph.comap_adj, SimpleGraph.fromRel_adj]
    fin_cases u <;> fin_cases v <;> simp [fwd, inv]
  · ext i; fin_cases i <;> simp [fwd, inv]

set_option maxHeartbeats 800000 in
/-- `t2_v1_e.forget ≅ sdpF7`. Mapping (v0,v1,v2,v3,w) → (v4,v1,v2,v0,v3). -/
theorem t2_v1_e_forget_iso :
    GenFlagIso (GenFlagType.empty CG2) t2_v1_e.forget sdpF7 := by
  let fwd : Fin 5 → Fin 5 := fun x => match x.val with
    | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 0 | _ => 3
  let inv : Fin 5 → Fin 5 := fun x => match x.val with
    | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 4 | _ => 0
  refine ⟨⟨fwd, inv, fun x => by fin_cases x <;> rfl, fun x => by fin_cases x <;> rfl⟩, ?_, fun i => Fin.elim0 i⟩
  simp only [colouredGraphUniverse, t2_v1_e, sdpF7, GenFlag.forget]
  apply Prod.ext
  · ext u v
    simp only [SimpleGraph.comap_adj, SimpleGraph.fromRel_adj]
    fin_cases u <;> fin_cases v <;> simp [fwd, inv]
  · ext i; fin_cases i <;> simp [fwd, inv]

set_option maxHeartbeats 800000 in
/-- `t2_v1_h.forget ≅ sdpF7` (S₂-pair partner of t2_v1_e). Mapping
    (v0,v1,v2,v3,w) → (v4,v1,v0,v2,v3). -/
theorem t2_v1_h_forget_iso :
    GenFlagIso (GenFlagType.empty CG2) t2_v1_h.forget sdpF7 := by
  let fwd : Fin 5 → Fin 5 := fun x => match x.val with
    | 0 => 4 | 1 => 1 | 2 => 0 | 3 => 2 | _ => 3
  let inv : Fin 5 → Fin 5 := fun x => match x.val with
    | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 4 | _ => 0
  refine ⟨⟨fwd, inv, fun x => by fin_cases x <;> rfl, fun x => by fin_cases x <;> rfl⟩, ?_, fun i => Fin.elim0 i⟩
  simp only [colouredGraphUniverse, t2_v1_h, sdpF7, GenFlag.forget]
  apply Prod.ext
  · ext u v
    simp only [SimpleGraph.comap_adj, SimpleGraph.fromRel_adj]
    fin_cases u <;> fin_cases v <;> simp [fwd, inv]
  · ext i; fin_cases i <;> simp [fwd, inv]

set_option maxHeartbeats 800000 in
/-- `t2_v1_f.forget ≅ sdpF30` (K_{3,2}). Mapping (v0,v1,v2,v3,w) → (v3,v0,v1,v2,v4). -/
theorem t2_v1_f_forget_iso :
    GenFlagIso (GenFlagType.empty CG2) t2_v1_f.forget sdpF30 := by
  let fwd : Fin 5 → Fin 5 := fun x => match x.val with
    | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | _ => 4
  let inv : Fin 5 → Fin 5 := fun x => match x.val with
    | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | _ => 4
  refine ⟨⟨fwd, inv, fun x => by fin_cases x <;> rfl, fun x => by fin_cases x <;> rfl⟩, ?_, fun i => Fin.elim0 i⟩
  simp only [colouredGraphUniverse, t2_v1_f, sdpF30, GenFlag.forget]
  apply Prod.ext
  · ext u v
    simp only [SimpleGraph.comap_adj, SimpleGraph.fromRel_adj]
    fin_cases u <;> fin_cases v <;> simp [fwd, inv]
  · ext i; fin_cases i <;> simp [fwd, inv]

end Davey2024
