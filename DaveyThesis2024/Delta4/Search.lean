import DaveyThesis2024.Delta4.Model

/-!
# Δ = 4 finite model: the search traversal and its completeness spike

§3b of the merged Stage-4 plan.  The plan time-boxes traversal completeness at fourteen days;
this is the first instalment, and the file states explicitly what is closed and what is open.
-/

namespace Delta4Model

/-! ###########################################################################
    ##  SPIKE (plan §3b): traversal completeness for the PRUNE-FREE search.  ##
    ###########################################################################

  Everything above this line is the canonical model, pasted verbatim.
  Everything below is new.  Nothing above is redefined.

  ## A.  `edg` is a single global bit of `A`

  `row A i` is base-4096 digit `i`, `edg A i j` is its bit `j`, so `edg A i j` is
  global bit `12*i + j` of `A` whenever `j < 12`.  This one lemma replaces all of
  the plan's obligation-7 digit arithmetic. -/

theorem pow_4096 (i : Nat) : (4096 : Nat) ^ i = 2 ^ (12 * i) := by
  rw [Nat.pow_mul]

theorem edg_eq_testBit (A i j : Nat) (hj : j < 12) :
    edg A i j = (A.testBit (12 * i + j)).toNat := by
  have hrow : row A i = (A >>> (12 * i)) % 2 ^ 12 := by
    rw [Nat.shiftRight_eq_div_pow, row, pow_4096]
  rw [edg, bitv_eq_toNat_testBit, hrow, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftRight, decide_eq_true hj, Bool.true_and]

theorem edg_zero (p q : Nat) : edg 0 p q = 0 := by
  simp [edg, row, bitv]

/-! ## B.  Committing one edge

  `addEdge` is a bitwise `|||`, **not** `A + 4096^i*2^j + 4096^j*2^i`.  The plan
  budgeted 200 lines (obligation 7) for the additive version's "fresh digit, no
  carry" side condition.  With `|||` there is no side condition at all: the update
  is idempotent, needs no freshness hypothesis, and `Nat.lor` is kernel-accelerated
  exactly like the `&&&` that `Box` already uses. -/

def addEdge (A i j : Nat) : Nat := A ||| 2 ^ (12 * i + j) ||| 2 ^ (12 * j + i)

theorem edg_addEdge (A i j p q : Nat) (hi : i < 12) (hj : j < 12) (hq : q < 12) :
    edg (addEdge A i j) p q =
      if (p = i ∧ q = j) ∨ (p = j ∧ q = i) then 1 else edg A p q := by
  rw [edg_eq_testBit _ _ _ hq, edg_eq_testBit _ _ _ hq, addEdge,
    Nat.testBit_or, Nat.testBit_or, Nat.testBit_two_pow, Nat.testBit_two_pow]
  by_cases h : (p = i ∧ q = j) ∨ (p = j ∧ q = i)
  · rw [if_pos h]
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  · rw [if_neg h]
    have h1 : ¬ (12 * i + j = 12 * p + q) := fun hh => h (Or.inl (by omega))
    have h2 : ¬ (12 * j + i = 12 * p + q) := fun hh => h (Or.inr (by omega))
    simp [h1, h2]

/-! ## C.  The pair list

  `pairList n` lists every pair `(i,j)` with `j < i < n`, once, in the pair order
  of plan §5 D8.  `K` plays no role, so it is not a parameter. -/

def pairsFrom (i : Nat) : Nat → List (Nat × Nat)
  | 0     => []
  | j + 1 => (i, j) :: pairsFrom i j

def pairList : Nat → List (Nat × Nat)
  | 0     => []
  | i + 1 => pairsFrom i i ++ pairList i

theorem mem_pairsFrom {i m p q : Nat} : (p, q) ∈ pairsFrom i m ↔ p = i ∧ q < m := by
  induction m with
  | zero => simp [pairsFrom]
  | succ m ih =>
      simp only [pairsFrom, List.mem_cons, Prod.mk.injEq, ih]
      omega

theorem mem_pairList {n p q : Nat} : (p, q) ∈ pairList n ↔ q < p ∧ p < n := by
  induction n with
  | zero => simp [pairList]
  | succ n ih =>
      simp only [pairList, List.mem_append, mem_pairsFrom, ih]
      omega

/-- Well-formedness of the *remaining* list: canonically ordered, in range,
    duplicate-free.  A static property of the list, not part of the invariant. -/
def WF (n : Nat) : List (Nat × Nat) → Prop
  | []      => True
  | p :: ps => p.2 < p.1 ∧ p.1 < n ∧ p ∉ ps ∧ WF n ps

theorem WF.tail {n : Nat} {p : Nat × Nat} {ps : List (Nat × Nat)}
    (h : WF n (p :: ps)) : WF n ps := h.2.2.2

theorem WF.mem_bounds {n : Nat} : ∀ {ps : List (Nat × Nat)}, WF n ps →
    ∀ r ∈ ps, r.2 < r.1 ∧ r.1 < n
  | [],      _, _, hr => absurd hr (List.not_mem_nil)
  | p :: ps, h, r, hr => by
      rcases List.mem_cons.1 hr with rfl | hr
      · exact ⟨h.1, h.2.1⟩
      · exact WF.mem_bounds h.2.2.2 r hr

theorem wf_pairsFrom (n i : Nat) (hi : i < n) :
    ∀ m, m ≤ i → ∀ ps, WF n ps → (∀ q, (i, q) ∉ ps) → WF n (pairsFrom i m ++ ps) := by
  intro m
  induction m with
  | zero => intro _ ps h _; simpa [pairsFrom] using h
  | succ m ih =>
      intro hm ps h hd
      refine ⟨by omega, hi, ?_, ih (by omega) ps h hd⟩
      intro hmem
      rcases List.mem_append.1 hmem with hmem | hmem
      · exact absurd (mem_pairsFrom.1 hmem).2 (Nat.lt_irrefl m)
      · exact hd m hmem

theorem wf_pairList (n : Nat) : ∀ m, m ≤ n → WF n (pairList m) := by
  intro m
  induction m with
  | zero => intro _; trivial
  | succ m ih =>
      intro hm
      exact wf_pairsFrom n m (by omega) m (Nat.le_refl m) (pairList m) (ih (by omega))
        (fun q hq => absurd (mem_pairList.1 hq).2 (Nat.lt_irrefl m))

/-! ## D.  The prefix invariant, and hereditarity of the take-guard -/

/-- A strict version of `sumUpto_le`; the only new fold lemma the spike needs. -/
theorem sumUpto_lt (f g : Nat → Nat) : ∀ n j : Nat, j < n →
    (∀ i, i < n → f i ≤ g i) → f j < g j → sumUpto f n 0 < sumUpto g n 0 := by
  intro n
  induction n with
  | zero => intro j hj; exact absurd hj (Nat.not_lt_zero j)
  | succ n ih =>
      intro j hj hle hlt
      rw [sumUpto_succ, sumUpto_succ]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
      · have h1 := ih j h (fun i hi => hle i (Nat.lt_succ_of_lt hi)) hlt
        have h2 := hle n (Nat.lt_succ_self n)
        omega
      · subst h
        have h1 := sumUpto_le f g j (fun i hi => hle i (Nat.lt_succ_of_lt hi))
        omega

/-- `(p,q)` is still to be decided, in either orientation. -/
def inPs (ps : List (Nat × Nat)) (p q : Nat) : Prop := (p, q) ∈ ps ∨ (q, p) ∈ ps

/-- **The prefix invariant — exactly two conjuncts** (plan §3c day-3 gate: ≤ 3).
    It mentions only `ps`, the list *remaining*: neither the past of the search nor
    its future.  `agree` is "already decided pairs are already correct";
    `clr` is "undecided pairs carry no edge yet". -/
structure Inv (n A Acur : Nat) (ps : List (Nat × Nat)) : Prop where
  agree : ∀ p, p < n → ∀ q, q < n → ¬ inPs ps p q → edg Acur p q = edg A p q
  clr   : ∀ p q, inPs ps p q → edg Acur p q = 0

/-- The invariant makes the partial graph a subgraph of the target. -/
theorem Inv.le {n A Acur : Nat} {ps : List (Nat × Nat)} (h : Inv n A Acur ps)
    {p q : Nat} (hp : p < n) (hq : q < n) : edg Acur p q ≤ edg A p q := by
  by_cases hm : inPs ps p q
  · rw [h.clr p q hm]; exact Nat.zero_le _
  · exact Nat.le_of_eq (h.agree p hp q hq hm)

/-- Taking an undecided edge of the target strictly raises the committed degree. -/
theorem Inv.deg_lt {n A Acur : Nat} {ps : List (Nat × Nat)} (h : Inv n A Acur ps)
    {i j : Nat} (hi : i < n) (hj : j < n) (hmem : inPs ps i j) (hij : edg A i j = 1) :
    deg n Acur i < deg n A i := by
  refine sumUpto_lt _ _ n j hj (fun q hq => h.le hi hq) ?_
  rw [h.clr i j hmem, hij]
  exact Nat.zero_lt_one

/-- The take-guard: capacity at both ends, root-mask disjointness (B3), and no
    common shell neighbour (B5).  Every clause is **antitone in the edge set**,
    which is what makes the matching branch always explorable. -/
def takeGuard (n K A i j : Nat) : Bool :=
  decide (kwt K i + deg n A i < 4)
  && decide (kwt K j + deg n A j < 4)
  && decide (msk K i &&& msk K j = 0)
  && allUpto (fun t => decide (edg A i t * edg A j t = 0)) n

/-- **Hereditarity.**  If the *target* has the edge `i~j` and it is still
    undecided, the guard passes at the *current* partial graph. -/
theorem takeGuard_of_box {n K A Acur : Nat} {ps : List (Nat × Nat)}
    (hbox : Box n K A = true) (hinv : Inv n A Acur ps)
    {i j : Nat} (hi : i < n) (hj : j < n) (hmem : (i, j) ∈ ps) (hij : edg A i j = 1) :
    takeGuard n K Acur i j = true := by
  have hji : edg A j i = 1 := by rw [← box_edg_symm hbox hi hj]; exact hij
  have hdisj := box_edge_disjoint hbox hi hj hij
  have c1 : kwt K i + deg n Acur i < 4 := by
    have h1 := box_deg_cap hbox hi
    have h2 := hinv.deg_lt hi hj (Or.inl hmem) hij
    omega
  have c2 : kwt K j + deg n Acur j < 4 := by
    have h1 := box_deg_cap hbox hj
    have h2 := hinv.deg_lt hj hi (Or.inr hmem) hji
    omega
  have c3 : msk K i &&& msk K j = 0 := by
    rcases ((box_iff n K A).1 hbox).edgeDisj i hi j hj with h0 | ⟨hm, _⟩
    · omega
    · exact hm
  have c4 : allUpto (fun t => decide (edg Acur i t * edg Acur j t = 0)) n = true := by
    rw [allUpto_eq_true_iff]
    intro t ht
    have h1 : edg Acur i t ≤ edg A i t := hinv.le hi ht
    have h2 : edg Acur j t ≤ edg A j t := hinv.le hj ht
    have h3 : edg A i t * edg A j t = 0 := hdisj.2 t
    simp only [decide_eq_true_eq]
    rcases Nat.mul_eq_zero.1 h3 with h | h
    · have hz : edg Acur i t = 0 := by omega
      simp [hz]
    · have hz : edg Acur j t = 0 := by omega
      simp [hz]
  simp only [takeGuard, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨c1, c2⟩, c3⟩, c4⟩

/-! ## E.  The prune-free search and its completeness

  `leafP` is a *parameter* rather than a stub: the only thing the traversal proof
  needs of it is that it reads `A` through `edg` on `[0,n)²`, which is stated as
  `hcongr`.  §F discharges `hcongr` for the real `leafOK`, so nothing here is
  vacuous. -/

def goNP (leafP : Nat → Nat → Nat → Bool) (n K : Nat) : List (Nat × Nat) → Nat → Bool
  | [],      A => leafP n K A
  | p :: ps, A =>
      goNP leafP n K ps A
        && (if takeGuard n K A p.1 p.2 then goNP leafP n K ps (addEdge A p.1 p.2) else true)

def searchNP (leafP : Nat → Nat → Nat → Bool) (n K : Nat) : Bool :=
  goNP leafP n K (pairList n) 0

theorem goNP_complete (leafP : Nat → Nat → Nat → Bool) (n K A : Nat)
    (hbox : Box n K A = true)
    (hcongr : ∀ X Y : Nat, (∀ p, p < n → ∀ q, q < n → edg X p q = edg Y p q) →
      leafP n K X = leafP n K Y) :
    ∀ ps : List (Nat × Nat), WF n ps → ∀ Acur : Nat, Inv n A Acur ps →
      goNP leafP n K ps Acur = true → leafP n K A = true := by
  have hn12 : n ≤ 12 := (box_size hbox).2
  intro ps
  induction ps with
  | nil =>
      intro _ Acur hinv h
      rw [goNP] at h
      rw [← hcongr Acur A (fun p hp q hq => hinv.agree p hp q hq (by simp [inPs]))]
      exact h
  | cons p ps ih =>
      obtain ⟨i, j⟩ := p
      intro hwf Acur hinv h
      obtain ⟨hji, hin, hnotin, hwf'⟩ := hwf
      have hjn : j < n := Nat.lt_trans hji hin
      rw [goNP, Bool.and_eq_true] at h
      obtain ⟨hskip, htake⟩ := h
      -- the two orientations of the head pair, as membership facts
      have hhead : ∀ x y : Nat, inPs ((i, j) :: ps) x y ↔
          ((x = i ∧ y = j) ∨ (x = j ∧ y = i) ∨ inPs ps x y) := by
        intro x y
        simp only [inPs, List.mem_cons, Prod.mk.injEq]
        constructor
        · rintro (⟨⟨rfl, rfl⟩ | hx⟩ | ⟨⟨rfl, rfl⟩ | hx⟩)
          · exact Or.inl ⟨rfl, rfl⟩
          · exact Or.inr (Or.inr (Or.inl hx))
          · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
          · exact Or.inr (Or.inr (Or.inr hx))
        · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | (hx | hx))
          · exact Or.inl (Or.inl ⟨rfl, rfl⟩)
          · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
          · exact Or.inl (Or.inr hx)
          · exact Or.inr (Or.inr hx)
      -- the head pair, in either orientation, is not in the tail
      have hfresh : ∀ x y : Nat, inPs ps x y →
          ¬ ((x = i ∧ y = j) ∨ (x = j ∧ y = i)) := by
        rintro x y hx (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · rcases hx with hx | hx
          · exact hnotin hx
          · exact absurd (WF.mem_bounds hwf' _ hx).1 (by omega)
        · rcases hx with hx | hx
          · exact absurd (WF.mem_bounds hwf' _ hx).1 (by omega)
          · exact hnotin hx
      by_cases hij : edg A i j = 1
      · -- TAKE: the target has this edge, so the guard passes and we descend right
        have hji' : edg A j i = 1 := by rw [← box_edg_symm hbox hin hjn]; exact hij
        have hg : takeGuard n K Acur i j = true :=
          takeGuard_of_box hbox hinv hin hjn (List.mem_cons_self) hij
        rw [if_pos hg] at htake
        refine ih hwf' (addEdge Acur i j) ⟨?_, ?_⟩ htake
        · intro x hx y hy hni
          rw [edg_addEdge _ _ _ _ _ (by omega) (by omega) (by omega)]
          by_cases hc : (x = i ∧ y = j) ∨ (x = j ∧ y = i)
          · rw [if_pos hc]
            rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hij.symm
            · exact hji'.symm
          · rw [if_neg hc]
            exact hinv.agree x hx y hy (fun hh => by
              rcases (hhead x y).1 hh with h1 | h1 | h1
              · exact hc (Or.inl h1)
              · exact hc (Or.inr h1)
              · exact hni h1)
        · intro x y hxy
          have hb : x < n ∧ y < n := by
            rcases hxy with hm | hm
            · exact ⟨(WF.mem_bounds hwf' _ hm).2, by
                have := WF.mem_bounds hwf' _ hm; omega⟩
            · exact ⟨by have := WF.mem_bounds hwf' _ hm; omega,
                (WF.mem_bounds hwf' _ hm).2⟩
          rw [edg_addEdge _ _ _ _ _ (by omega) (by omega) (by omega),
            if_neg (hfresh x y hxy)]
          exact hinv.clr x y ((hhead x y).2 (Or.inr (Or.inr hxy)))
      · -- SKIP: the target has no edge here, so the left branch already matches
        have hij0 : edg A i j = 0 := by
          have := edg_le_one A i j; omega
        have hji0 : edg A j i = 0 := by rw [← box_edg_symm hbox hin hjn]; exact hij0
        refine ih hwf' Acur ⟨?_, ?_⟩ hskip
        · intro x hx y hy hni
          by_cases hc : (x = i ∧ y = j) ∨ (x = j ∧ y = i)
          · have h0 : edg Acur x y = 0 :=
              hinv.clr x y ((hhead x y).2 (Or.elim hc Or.inl (fun hh => Or.inr (Or.inl hh))))
            rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · rw [h0, hij0]
            · rw [h0, hji0]
          · exact hinv.agree x hx y hy (fun hh => by
              rcases (hhead x y).1 hh with h1 | h1 | h1
              · exact hc (Or.inl h1)
              · exact hc (Or.inr h1)
              · exact hni h1)
        · intro x y hxy
          exact hinv.clr x y ((hhead x y).2 (Or.inr (Or.inr hxy)))

theorem inv_zero {n K A : Nat} (hbox : Box n K A = true) : Inv n A 0 (pairList n) where
  agree := by
    intro p hp q hq hni
    have hpq : p = q := by
      rcases Nat.lt_or_ge p q with h | h
      · exact absurd (Or.inr (mem_pairList.2 ⟨h, hq⟩) : inPs (pairList n) p q) hni
      · rcases Nat.eq_or_lt_of_le h with h2 | h2
        · exact h2.symm
        · exact absurd (Or.inl (mem_pairList.2 ⟨h2, hp⟩) : inPs (pairList n) p q) hni
    subst hpq
    rw [edg_zero, box_edg_irrefl hbox hp]
  clr := by intro p q _; exact edg_zero p q

/-- **THE SPIKE.**  Traversal completeness for the prune-free search, against the
    real `Box` — not a weakened one (plan §3c, days 12–14). -/
theorem searchNP_complete (leafP : Nat → Nat → Nat → Bool) (n K A : Nat)
    (hbox : Box n K A = true)
    (hcongr : ∀ X Y : Nat, (∀ p, p < n → ∀ q, q < n → edg X p q = edg Y p q) →
      leafP n K X = leafP n K Y)
    (h : searchNP leafP n K = true) :
    leafP n K A = true :=
  goNP_complete leafP n K A hbox hcongr (pairList n) (wf_pairList n n (Nat.le_refl n)) 0
    (inv_zero hbox) h

/-! ## F.  The real leaf test satisfies `hcongr`

  `leafOK` reads `A` only through `edg A p q` with `p, q < n`.  Discharging this
  turns §E's parametric statement into a concrete one, so the spike is not
  vacuous and the day-14 "stub" never has to be revisited. -/

/-- Two packed adjacencies agree on the whole shell. -/
def EdgAgree (n X Y : Nat) : Prop := ∀ p, p < n → ∀ q, q < n → edg X p q = edg Y p q

theorem deg_congr {n X Y : Nat} (h : EdgAgree n X Y) {i : Nat} (hi : i < n) :
    deg n X i = deg n Y i :=
  sumUpto_congr (fun q hq => h i hi q hq)

theorem slack_congr {n K X Y : Nat} (h : EdgAgree n X Y) {i : Nat} (hi : i < n) :
    slack n K X i = slack n K Y i := by
  unfold slack; rw [deg_congr h hi]

theorem twoT_congr {n K X Y : Nat} (h : EdgAgree n X Y) : twoT n K X = twoT n K Y :=
  sumUpto_congr (fun i hi => sumUpto_congr (fun j hj => by rw [h i hi j hj]))

theorem shellW_congr {n K X Y : Nat} (h : EdgAgree n X Y) (a : Nat) {y : Nat} (hy : y < n) :
    shellW n K X a y = shellW n K Y a y := by
  have hs : sumUpto (fun i => hasL K i a * edg X y i) n 0
      = sumUpto (fun i => hasL K i a * edg Y y i) n 0 :=
    sumUpto_congr (fun i hi => by rw [h y hy i hi])
  unfold shellW; rw [hs]

theorem creditAt_congr {n K X Y : Nat} (h : EdgAgree n X Y) (a : Nat) :
    creditAt n K X a = creditAt n K Y a := by
  have hs : sumUpto (fun y => 3 * shellW n K X a y) n 0
      = sumUpto (fun y => 3 * shellW n K Y a y) n 0 :=
    sumUpto_congr (fun y hy => by rw [shellW_congr h a hy])
  unfold creditAt; rw [hs]

theorem credit_congr {n K X Y : Nat} (h : EdgAgree n X Y) : credit n K X = credit n K Y :=
  sumUpto_congr (fun a _ => creditAt_congr h a)

theorem dhatRoot_congr {n K X Y : Nat} (h : EdgAgree n X Y) (a b : Nat) :
    dhatRoot n K X a b = dhatRoot n K Y a b :=
  sumUpto_congr (fun y hy => by rw [shellW_congr h a hy])

theorem dhatShell_congr {n K X Y : Nat} (h : EdgAgree n X Y) (a : Nat) {y : Nat}
    (hy : y < n) : dhatShell n K X a y = dhatShell n K Y a y := by
  have h1 : sumUpto (fun b => if b = a then 0 else
        if rootW n K a b = 0 then 0 else hasL K y b) 4 0
      = sumUpto (fun b => if b = a then 0 else
        if rootW n K a b = 0 then 0 else hasL K y b) 4 0 := rfl
  have h2 : sumUpto (fun z => if z = y then 0 else
        if shellW n K X a z = 0 then 0 else edg X y z) n 0
      = sumUpto (fun z => if z = y then 0 else
        if shellW n K Y a z = 0 then 0 else edg Y y z) n 0 := by
    refine sumUpto_congr (fun z hz => ?_)
    by_cases hzy : z = y
    · simp [hzy]
    · simp only [if_neg hzy]
      rw [shellW_congr h a hz, h y hy z hz]
  unfold dhatShell; rw [h1, h2, slack_congr h hy]

theorem chargeAt_congr {n K X Y : Nat} (h : EdgAgree n X Y) (a : Nat) :
    chargeAt n K X a = chargeAt n K Y a := by
  have h1 : sumUpto (fun b => if b = a then 0 else
        dhatRoot n K X a b * cert (rootW n K a b)) 4 0
      = sumUpto (fun b => if b = a then 0 else
        dhatRoot n K Y a b * cert (rootW n K a b)) 4 0 := by
    refine sumUpto_congr (fun b _ => ?_)
    by_cases hba : b = a
    · simp [hba]
    · simp only [if_neg hba]; rw [dhatRoot_congr h a b]
  have h2 : sumUpto (fun y => dhatShell n K X a y * cert (shellW n K X a y)) n 0
      = sumUpto (fun y => dhatShell n K Y a y * cert (shellW n K Y a y)) n 0 := by
    refine sumUpto_congr (fun y hy => ?_)
    rw [dhatShell_congr h a hy, shellW_congr h a hy]
  unfold chargeAt; rw [h1, h2]

theorem charge_congr {n K X Y : Nat} (h : EdgAgree n X Y) : charge n K X = charge n K Y :=
  sumUpto_congr (fun a _ => chargeAt_congr h a)

theorem leafOK_congr {n K X Y : Nat} (h : EdgAgree n X Y) : leafOK n K X = leafOK n K Y := by
  unfold leafOK; rw [twoT_congr h, charge_congr h, credit_congr h]

/-- **THE SPIKE, concrete.**  `leafP := leafOK`: no stub anywhere. -/
theorem searchNP_leafOK_complete (n K A : Nat) (hbox : Box n K A = true)
    (h : searchNP leafOK n K = true) : leafOK n K A = true :=
  searchNP_complete leafOK n K A hbox (fun _ _ hE => leafOK_congr hE) h

/-! ## H.  The degree cache `D` — closing the rest of plan obligation 7

  §E dropped the plan's `D` accumulator, because `D` is a *cache*
  (`dg D t = deg n A t`) and carrying it would have added a third invariant
  conjunct.  This section puts it back as a **refinement**: `goNPD` (the plan's
  literal signature) is proved *equal* to `goNP`, so completeness transfers with
  no change to §E's two-conjunct invariant.

  `bumpDeg D i j = D + 16^i + 16^j` is the one place where carries still have to
  be ruled out, so the base-16 digit lemmas below are exactly the surviving
  content of obligation 7. -/

@[inline] def dg (D t : Nat) : Nat := D / 16 ^ t % 16

theorem pow16_pos (t : Nat) : 0 < (16 : Nat) ^ t := Nat.pow_pos (by decide)

theorem dg_zero (t : Nat) : dg 0 t = 0 := by simp [dg]

theorem dg_bump_self {D i : Nat} (h : dg D i < 15) : dg (D + 16 ^ i) i = dg D i + 1 := by
  unfold dg at h ⊢
  rw [Nat.add_div_right _ (pow16_pos i)]
  omega

theorem dg_bump_lt (D i t : Nat) (h : t < i) : dg (D + 16 ^ i) t = dg D t := by
  obtain ⟨k, rfl⟩ : ∃ k, i = t + 1 + k := ⟨i - t - 1, by omega⟩
  have hsp : (16 : Nat) ^ (t + 1 + k) = 16 ^ t * (16 * 16 ^ k) := by
    simp [Nat.pow_add, Nat.mul_assoc]
  unfold dg
  rw [hsp, Nat.add_mul_div_left _ _ (pow16_pos t), Nat.add_mul_mod_self_left]

theorem dg_bump_gt {D i t : Nat} (h : i < t) (hlt : dg D i < 15) :
    dg (D + 16 ^ i) t = dg D t := by
  have hp1 := pow16_pos (i + 1)
  have hw : D % 16 ^ (i + 1) / 16 ^ i = dg D i := by
    unfold dg; rw [Nat.pow_succ]; exact Nat.mod_mul_right_div_self D (16 ^ i) 16
  have hwlt : D % 16 ^ (i + 1) + 16 ^ i < 16 ^ (i + 1) := by
    have h1 : D % 16 ^ (i + 1) / 16 ^ i < 15 := by rw [hw]; exact hlt
    have h2 : D % 16 ^ (i + 1) < 15 * 16 ^ i :=
      (Nat.div_lt_iff_lt_mul (pow16_pos i)).1 h1
    have h3 : (16 : Nat) ^ (i + 1) = 16 ^ i * 16 := Nat.pow_succ 16 i
    omega
  have hdm := Nat.div_add_mod D (16 ^ (i + 1))
  have hsplit : D + 16 ^ i
      = (D % 16 ^ (i + 1) + 16 ^ i) + 16 ^ (i + 1) * (D / 16 ^ (i + 1)) := by
    omega
  have hdiv : (D + 16 ^ i) / 16 ^ (i + 1) = D / 16 ^ (i + 1) := by
    rw [hsplit, Nat.add_mul_div_left _ _ hp1, Nat.div_eq_of_lt hwlt, Nat.zero_add]
  obtain ⟨k, rfl⟩ : ∃ k, t = i + 1 + k := ⟨t - i - 1, by omega⟩
  unfold dg
  rw [Nat.pow_add 16 (i + 1) k, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hdiv]

theorem dg_add_pow (D i t : Nat) (h : dg D i < 15) :
    dg (D + 16 ^ i) t = dg D t + (if t = i then 1 else 0) := by
  rcases Nat.lt_trichotomy t i with ht | ht | ht
  · rw [dg_bump_lt D i t ht, if_neg (by omega), Nat.add_zero]
  · subst ht; rw [dg_bump_self h, if_pos rfl]
  · rw [dg_bump_gt ht h, if_neg (by omega), Nat.add_zero]

def bumpDeg (D i j : Nat) : Nat := D + 16 ^ i + 16 ^ j

theorem dg_bumpDeg {D i j : Nat} (hij : j < i) (hi : dg D i < 15) (hj : dg D j < 15)
    (t : Nat) :
    dg (bumpDeg D i j) t = dg D t + (if t = i then 1 else 0) + (if t = j then 1 else 0) := by
  have h1 : dg (D + 16 ^ i) j = dg D j := by
    rw [dg_add_pow D i j hi, if_neg (by omega), Nat.add_zero]
  unfold bumpDeg
  rw [dg_add_pow (D + 16 ^ i) j t (by omega), dg_add_pow D i t hi]

/-! ### `deg` under `addEdge` -/

theorem sumUpto_bump (f g : Nat → Nat) : ∀ n j : Nat, j < n →
    (∀ i, i < n → i ≠ j → f i = g i) → f j = g j + 1 →
    sumUpto f n 0 = sumUpto g n 0 + 1 := by
  intro n
  induction n with
  | zero => intro j hj; exact absurd hj (Nat.not_lt_zero j)
  | succ n ih =>
      intro j hj hoff hat
      rw [sumUpto_succ, sumUpto_succ]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
      · have h1 := ih j h (fun i hi hne => hoff i (Nat.lt_succ_of_lt hi) hne) hat
        have h2 := hoff n (Nat.lt_succ_self n) (by omega)
        omega
      · subst h
        have h1 : sumUpto f j 0 = sumUpto g j 0 :=
          sumUpto_congr (fun i hi => hoff i (Nat.lt_succ_of_lt hi) (by omega))
        omega

theorem sumUpto_const_zero (n : Nat) : sumUpto (fun _ => 0) n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumUpto_succ, ih]

theorem deg_zero_graph (n t : Nat) : deg n 0 t = 0 := by
  unfold deg
  rw [sumUpto_congr (g := fun _ => 0) (fun q _ => edg_zero t q), sumUpto_const_zero]

theorem deg_addEdge_at {n A i j : Nat} (hn : n ≤ 12) (hi : i < n) (hj : j < n)
    (hne : i ≠ j) (hf : edg A i j = 0) : deg n (addEdge A i j) i = deg n A i + 1 := by
  unfold deg
  refine sumUpto_bump _ _ n j hj (fun q hq hqj => ?_) ?_
  · have hc : ¬ ((i = i ∧ q = j) ∨ (i = j ∧ q = i)) := by
      rintro (⟨-, h2⟩ | ⟨h1, -⟩)
      · exact hqj h2
      · exact hne h1
    rw [edg_addEdge _ _ _ _ _ (by omega) (by omega) (by omega), if_neg hc]
  · rw [edg_addEdge _ _ _ _ _ (by omega) (by omega) (by omega),
      if_pos (Or.inl ⟨rfl, rfl⟩), hf]

theorem deg_addEdge_at' {n A i j : Nat} (hn : n ≤ 12) (hi : i < n) (hj : j < n)
    (hne : i ≠ j) (hf : edg A j i = 0) : deg n (addEdge A i j) j = deg n A j + 1 := by
  unfold deg
  refine sumUpto_bump _ _ n i hi (fun q hq hqi => ?_) ?_
  · have hc : ¬ ((j = i ∧ q = j) ∨ (j = j ∧ q = i)) := by
      rintro (⟨h1, -⟩ | ⟨-, h2⟩)
      · exact hne h1.symm
      · exact hqi h2
    rw [edg_addEdge _ _ _ _ _ (by omega) (by omega) (by omega), if_neg hc]
  · rw [edg_addEdge _ _ _ _ _ (by omega) (by omega) (by omega),
      if_pos (Or.inr ⟨rfl, rfl⟩), hf]

theorem deg_addEdge_off {n A i j t : Nat} (hn : n ≤ 12) (hi : i < n) (hj : j < n)
    (hti : t ≠ i) (htj : t ≠ j) : deg n (addEdge A i j) t = deg n A t := by
  unfold deg
  refine sumUpto_congr (fun q hq => ?_)
  have hc : ¬ ((t = i ∧ q = j) ∨ (t = j ∧ q = i)) := by
    rintro (⟨h1, -⟩ | ⟨h1, -⟩)
    · exact hti h1
    · exact htj h1
  rw [edg_addEdge _ _ _ _ _ (by omega) (by omega) (by omega), if_neg hc]

/-! ### The cached traversal, and its agreement with §E's -/

def takeGuardD (n K A D i j : Nat) : Bool :=
  decide (kwt K i + dg D i < 4)
  && decide (kwt K j + dg D j < 4)
  && decide (msk K i &&& msk K j = 0)
  && allUpto (fun t => decide (edg A i t * edg A j t = 0)) n

def goNPD (leafP : Nat → Nat → Nat → Bool) (n K : Nat) :
    List (Nat × Nat) → Nat → Nat → Bool
  | [],      A, _ => leafP n K A
  | p :: ps, A, D =>
      goNPD leafP n K ps A D
        && (if takeGuardD n K A D p.1 p.2
            then goNPD leafP n K ps (addEdge A p.1 p.2) (bumpDeg D p.1 p.2) else true)

def searchNPD (leafP : Nat → Nat → Nat → Bool) (n K : Nat) : Bool :=
  goNPD leafP n K (pairList n) 0 0

/-- `A` carries no edge on any undecided pair. -/
def Clear (ps : List (Nat × Nat)) (A : Nat) : Prop := ∀ p q, inPs ps p q → edg A p q = 0

theorem goNPD_eq_goNP (leafP : Nat → Nat → Nat → Bool) (n K : Nat) (hn : n ≤ 12) :
    ∀ ps : List (Nat × Nat), WF n ps → ∀ A D : Nat, Clear ps A →
      (∀ t, t < n → dg D t = deg n A t) →
      goNPD leafP n K ps A D = goNP leafP n K ps A := by
  intro ps
  induction ps with
  | nil => intro _ A D _ _; rfl
  | cons p ps ih =>
      obtain ⟨i, j⟩ := p
      intro hwf A D hclr hcache
      obtain ⟨hji, hin, hnotin, hwf'⟩ := hwf
      have hjn : j < n := Nat.lt_trans hji hin
      have hweak : ∀ x y, inPs ps x y → inPs ((i, j) :: ps) x y := by
        rintro x y (hx | hx)
        · exact Or.inl (List.mem_cons_of_mem _ hx)
        · exact Or.inr (List.mem_cons_of_mem _ hx)
      have hfresh : ∀ x y : Nat, inPs ps x y → ¬ ((x = i ∧ y = j) ∨ (x = j ∧ y = i)) := by
        rintro x y hx (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · rcases hx with hx | hx
          · exact hnotin hx
          · exact absurd (WF.mem_bounds hwf' _ hx).1 (by omega)
        · rcases hx with hx | hx
          · exact absurd (WF.mem_bounds hwf' _ hx).1 (by omega)
          · exact hnotin hx
      have hclr' : Clear ps A := fun x y hxy => hclr x y (hweak x y hxy)
      have hg : takeGuardD n K A D i j = takeGuard n K A i j := by
        unfold takeGuardD takeGuard
        rw [hcache i hin, hcache j hjn]
      rw [goNPD, goNP, hg, ih hwf' A D hclr' hcache]
      by_cases hgt : takeGuard n K A i j = true
      · rw [if_pos hgt, if_pos hgt]
        have hcap := hgt
        unfold takeGuard at hcap
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcap
        have hdi : dg D i < 15 := by rw [hcache i hin]; omega
        have hdj : dg D j < 15 := by rw [hcache j hjn]; omega
        have hfij : edg A i j = 0 := hclr i j (Or.inl List.mem_cons_self)
        have hfji : edg A j i = 0 := hclr j i (Or.inr List.mem_cons_self)
        have hrec : goNPD leafP n K ps (addEdge A i j) (bumpDeg D i j)
            = goNP leafP n K ps (addEdge A i j) := by
          refine ih hwf' (addEdge A i j) (bumpDeg D i j) (fun x y hxy => ?_) (fun t ht => ?_)
          · have hb : y < 12 := by
              rcases hxy with hm | hm
              · have := WF.mem_bounds hwf' _ hm; omega
              · have := WF.mem_bounds hwf' _ hm; omega
            rw [edg_addEdge _ _ _ _ _ (by omega) (by omega) hb, if_neg (hfresh x y hxy)]
            exact hclr x y (hweak x y hxy)
          · rw [dg_bumpDeg hji hdi hdj t, hcache t ht]
            by_cases hti : t = i
            · subst hti
              rw [deg_addEdge_at hn hin hjn (by omega) hfij, if_pos rfl, if_neg (by omega),
                Nat.add_zero]
            · by_cases htj : t = j
              · subst htj
                rw [deg_addEdge_at' hn hin hjn (by omega) hfji, if_neg (by omega), if_pos rfl,
                  Nat.add_zero]
              · rw [deg_addEdge_off hn hin hjn hti htj, if_neg hti, if_neg htj,
                  Nat.add_zero]
        rw [hrec]
      · rw [if_neg hgt, if_neg hgt]

theorem searchNPD_eq_searchNP (leafP : Nat → Nat → Nat → Bool) (n K : Nat) (hn : n ≤ 12) :
    searchNPD leafP n K = searchNP leafP n K :=
  goNPD_eq_goNP leafP n K hn (pairList n) (wf_pairList n n (Nat.le_refl n)) 0 0
    (fun p q _ => edg_zero p q) (fun t _ => by rw [dg_zero, deg_zero_graph])

/-- **THE SPIKE, in the plan's own signature** (`goNPD` carries `D`). -/
theorem searchNPD_complete (n K A : Nat) (hbox : Box n K A = true)
    (h : searchNPD leafOK n K = true) : leafOK n K A = true := by
  rw [searchNPD_eq_searchNP leafOK n K (box_size hbox).2] at h
  exact searchNP_leafOK_complete n K A hbox h

end Delta4Model
