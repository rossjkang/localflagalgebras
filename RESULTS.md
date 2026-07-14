# Results correspondence: papers ↔ Lean

This document places each **theorem-headed result in the two papers' introductions**
side by side with its **Lean 4 formalisation**, and lists the **user-defined
definitions** each result rests on and the **user-defined (domain) axioms** it
depends on — with, for every axiom, the mathematical statement it stands in for.

- **Paper 1** — *Local flag algebras.*
- **Paper 2** — *Strong edge-colouring via local flag algebras.*

All Lean names live in namespace `Davey2024` (or the sub-namespaces noted), under
`DaveyThesis2024/`. The authoritative, build-enforced axiom record is
[`DaveyThesis2024/AxiomCheck.lean`](DaveyThesis2024/AxiomCheck.lean) (`#guard_msgs`
around `#print axioms`, so `lake build` fails if any axiom set changes).

---

## 1. Axiom legend

Lean reports the axiom set of a theorem with `#print axioms`. Two kinds appear.

**Standard Lean axioms** (not project assumptions — the trusted base of the system):

| Axiom | Meaning |
|---|---|
| `propext` | propositional extensionality |
| `Classical.choice` | the axiom of choice |
| `Quot.sound` | soundness of quotients |
| `Lean.ofReduceBool`, `Lean.trustCompiler` | *compiled-evaluation* axioms — added only when a proof uses `native_decide` (trusts that the compiled Boolean evaluator agrees with the kernel) |

A result whose axiom set is a subset of these is **proved outright**, with no
domain assumption. Results that additionally avoid `ofReduceBool`/`trustCompiler`
are checked entirely in the kernel (no `native_decide`).

**User-defined (domain) axioms** — the named mathematical assumptions specific to
this project. Every one is catalogued in §5 with the statement it encodes and
its justification. There are exactly **two families**:

- **SDP-certificate bridge axioms** (Paper 1: 2; Paper 2: 3 per SEC headline) —
  the numerical output, basis-locality, and combinatorial bridging of the
  semidefinite-programming certificates, whose full re-derivation in Lean is
  deferred (see §5). Paper 2's SEC axioms are the **F-faithful (`_F`) family**
  (see §5).
- **Cited-literature axioms** — the Hurley–de Joannis de Verclos–Kang sparse
  colouring lemma (Paper 2 SEC), and the Kim–Vu concentration and
  Pippenger–Spencer covering theorems (Paper 2 random-bipartite), transcribed
  verbatim because Mathlib lacks the infrastructure.

Everything else — the local flag algebra framework, the extremal graphs, the
per-vertex counting, the clique / induced-matching bounds, and the whole
WLOG-biregular reduction behind the asymmetric bound — is proved from the
standard axioms alone.

---

## 2. User-defined definitions (the framework)

These are the foundational constructs the theorem *statements* are phrased in.
File references are `file:line` under `DaveyThesis2024/`.

### 2.1 Flags and the local flag algebra

| Lean | Paper symbol | Meaning |
|---|---|---|
| `Flag` (`Basic.lean:211`), `FlagType` (`:192`), `emptyType` (`:198`) | (F, θ), σ, ∅ | a σ-flag = finite graph with an induced embedding of the type σ; `Flag emptyType` = a plain unlabelled graph |
| `GenFlag` / `GenFlagType` (`Basic.lean:126/119`), universes `CG2` (`PentagonConjecture.lean:2828`), `CG22` (`CG22.lean:81`), `CG4` (`CG4.lean`) | coloured flags | the same, over a vertex- (CG2), vertex+edge- (CG22), or 4-vertex-colour (CG4, the F-free asymmetric host) coloured relational universe |
| `Flag.forget` (`Basic.lean:231`) | ↓F | drop the labelling |
| `FlagClass` (`FlagIso.lean:68`) | 𝓕^σ | isomorphism classes of σ-flags (the algebra basis) |
| `FlagAlg` (`LocalFlagAlgebra.lean:71`) | 𝓛^σ | the local flag algebra = finitely-supported real combinations of flag classes |
| `localFlagProduct` / `FlagAlg.mul` (`LocalFlagAlgebra.lean:190/384`) | F · F′ | the flag-algebra product |
| `averaging` (`LocalFlagAlgebra.lean:5352`) | ⟦·⟧_σ | the unlabelling / averaging operator into 𝓛^∅ |
| `LimitFunctional` (`LocalFlagAlgebra.lean:4748`), `.evalAlg` (`:5141`) | φ ∈ Φ^σ | a limit functional φ(F) = limₖ ρ(F;Gₖ): non-negative, φ(σ)=1, iso-invariant, an algebra homomorphism; `evalAlg` extends it linearly to 𝓛^σ |
| `SemanticCone` (`LocalFlagAlgebra.lean:5194`) | positivity cone | { v : φ(v) ≥ 0 for all limit functionals φ }; `φ(f²) ≥ 0` |
| `IsLocalFlag` (`Basic.lean:657`), `IsBoundedDensity` (`:645`) | local σ-flag | bounded local density, hereditarily under label extension — the "local" of *local* flag algebra |

### 2.2 Densities and graph parameters

| Lean | Paper symbol | Meaning |
|---|---|---|
| `genInducedCount` / `inducedCount` (`Basic.lean:182/321`) | c(F; G) | number of induced copies of F in G |
| `localDensity` (`Basic.lean:508`) | ρ(F; G) | induced count normalised by `C(Δ(G), |F|−|σ|)` — divided by the **degree** binomial, not the order binomial (this is what makes the algebra *local*) |
| `genUnlabelledDensity` (`LocalFlagAlgebra.lean:6334`) | ρ (÷ Aut) | local density additionally divided by `|Aut(F)|` (the convention `evalAlg` uses) |
| `maxDegree` (`PentagonConjecture.lean:169`) | Δ(G) | maximum degree |
| `maxDegreeOn` (`BipartiteL2Clique.lean:351`) | Δ_A, Δ_B | max degree over one side of a bipartition |
| `IsTriangleFree` (`PentagonConjecture.lean:174`), `IsRegular` (`:179`), `IsBipartite` (`StrongEdgeColouring.lean:281`) | — | no K₃; Δ-regular; bipartite |
| `GraphClass` / `GraphParam` (`Basic.lean:500/503`); `ColouredGraphClass` (`PentagonConjecture.lean:2357`); `secGenGraphClassF` (`SecBridge.lean:309`) | 𝒢, Δ | the hereditary graph family and its degree parameter (concrete pentagon / F-faithful SEC classes) |

### 2.3 Paper-1-specific objects

| Lean | Paper | Meaning |
|---|---|---|
| `pentagonCount` (`PentagonConjecture.lean:158`), `pentagonCountAt` (`:163`) | P(G), P(G,v) | number of induced C₅'s (through a vertex v) |
| `clebschGraph` / `clebschFlag` (`PentagonConjecture.lean:110/114`) | Cl = SRG(16,5,0,2) | the Clebsch graph (folded 5-cube, XOR neighbour rule) |
| `petersenGraph` / `petersenFlag` (`PentagonDelta3.lean:193/203`) | Petersen | the Petersen graph (Δ=3 extremum) |
| `c12Graph` / `c12Flag` (`PentagonDelta4Witness.lean:32/42`) | C₁₂(2,3) | the Δ=4 witness circulant |

### 2.4 Paper-2-specific objects

| Lean | Paper | Meaning |
|---|---|---|
| `strongChromaticIndex` (`StrongEdgeColouring.lean:165`), `chiPrimeS` (`SECRandomBipartite.lean:88`) | χ′ₛ(G) | strong chromatic index (Flag version; `ℕ∞`-valued `SimpleGraph` version for the random result) |
| `lineGraphSqFlag` (`StrongEdgeColouring.lean:677`) | L(G)² | square of the line graph (edges of G, adjacent iff within distance 2 in L(G)) |
| `cliqueNumber` (`BipartiteOmegaL2.lean:56`) | ω | maximum clique size |
| `inducedMatchingNumber` (`InducedMatchingAsymmetric.lean:73`) | ν_s(G) | induced (strong) matching number = α(L(G)²) |
| `edgeFinset` (`StrongEdgeColouring.lean:203`) | E(G) | edge set as ordered pairs; `.card = |E(G)|` |
| `IsAsymmetricBipartite p` (`SecAsymmetricBipartiteBridge.lean:67`) | ratio r=p, high side Δ-regular | bipartite, one side Δ-regular, other side degrees ≤ p·Δ |
| `IsAsymmetricBipartiteMaxDeg p` (`SecAsymHighSide.lean:51`) | ratio r=p, side **maximum** degrees | the paper's max-degree class: bipartite, high side degrees ≤ Δ, low side ≤ p·Δ (weaker than `IsAsymmetricBipartite`; the Thm 1.3 hypothesis) |
| `deltaA` / `deltaB` (`SECRandomBipartite.lean:133/139`) | Δ_A, Δ_B | per-side max degrees in the random model |
| `probBipartiteRandom` (`SECRandomBipartite.lean:168`) | G(n_A,n_B,p) | the random bipartite model: each of the n_A·n_B cross slots an independent Bernoulli(p) edge |

---

## 3. Paper 1 — pentagon densities

Notation: P = `pentagonCount`, n = `G.size`, Δ = `maxDegree G`, all over
`G : Flag emptyType` with `hG : IsTriangleFree G`. **All Paper 1 bounds are
unconditional** (no "Δ large" hypothesis): the flag-algebra bound is asymptotic
in Δ, but `pentagon_asymptotic_suffices` (`PentagonConjecture.lean:1677`) lifts it
to every graph via blow-ups, since P/(nΔ⁴) is blow-up invariant.

> **§8 (Bruhn–Joos sparsity) — reproduced, not formalised.** Paper 1 §8 recovers
> the Bruhn–Joos constant `3/2` (their Lemma 2.1: the strong neighbourhood of an
> edge induces ≤ (3/2)Δ⁴ + 5Δ³ edges in L(G)²) from a size-4 SDP
> (`local-flags-certificates/examples/bruhn_joos.rs`; CSDP optimum 1.5). As an
> established external result it is **not** given a Lean statement — hence it has
> no row below and no `AxiomCheck` entry.

### Theorem 1.1 — simple pentagon bound

- **Math:** `P(G) ≤ |G|·Δ(G)⁴ / 40` for every triangle-free G.
- **Lean:** `pentagon_bound_simple` (`SdpEvaluation.lean:10027`)
  ```lean
  theorem pentagon_bound_simple (G : Flag emptyType) (hG : IsTriangleFree G) :
      (pentagonCount G : ℝ) * (5 * 8) ≤ G.size * maxDegree G ^ 4
  ```
- **Defs used:** `Flag`, `IsTriangleFree`, `pentagonCount`, `maxDegree`.
- **Axioms:** `propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound` — **standard only** (size-5 SDP checked by `native_decide`); **no user axioms**.

### Theorem 1.2 — tighter pentagon bound

- **Math:** `P(G) ≤ 0.02073·|G|·Δ(G)⁴`.
- **Lean:** `pentagon_bound_full` (`PentagonBound.lean:127`)
  ```lean
  theorem pentagon_bound_full (G : Flag emptyType) (hG : IsTriangleFree G) :
      (pentagonCount G : ℝ) ≤ 0.02073 * G.size * maxDegree G ^ 4
  ```
- **Defs used:** as 1.1, plus the size-8 per-vertex functional `pentagonQ`.
- **Axioms:** standard (incl. `native_decide`) **+ 2 user axioms** —
  `PentagonQBridge.pentagonQ_basis_combinatorial_identity_step1` and
  `PentagonQBridge.phi_evalAlg_O_Q_alg_le_bound` (§5.1, §5.3).

### Conjecture 1.3 — sharp bounded-degree pentagon constant *(open)*

- **Math:** `P(G) ≤ (12/625)·|G|·Δ(G)⁴`, sharp on Cl and its blow-ups. *A conjecture — not formalised as a theorem.* Its **tightness** is Lemma 1.4.

### Lemma 1.4 — Clebsch-blowup tightness

- **Math:** for every k ≥ 1, Cl[k] is triangle-free with |Cl[k]| = 16k, Δ = 5k,
  P = 192k⁵, so the ratio is exactly 12/625.
- **Lean:** `clebsch_blowup_tight` (`PentagonUnique.lean:2036`)
  ```lean
  theorem clebsch_blowup_tight :
      ∀ D₀ : ℕ, ∃ G : Flag emptyType,
        IsTriangleFree G ∧ D₀ ≤ maxDegree G ∧
        pentagonCount G * 625 = G.size * maxDegree G ^ 4 * 12
  ```
- **Defs used:** `clebschGraph`/`clebschFlag`, blow-up, `pentagonCount`, `maxDegree`.
- **Axioms:** `propext, Classical.choice, Quot.sound` — **standard only, no `native_decide`, no user axioms** *(verified directly).*

### Theorem 1.5 — Clebsch characterisation at Δ = 5

- **Math:** every triangle-free G with Δ ≤ 5 has `P(G) ≤ 12|G|`, with equality iff
  every component is Cl; so Conjecture 1.3 holds at Δ = 5, uniquely on disjoint Cl's.
- **Lean (bound):** `pentagon_delta5_tight` (`PentagonConjecture.lean:1650`)
  ```lean
  theorem pentagon_delta5_tight (G : Flag emptyType)
      (hTF : IsTriangleFree G) (hdeg : maxDegree G ≤ 5) :
      pentagonCount G ≤ 12 * G.size
  ```
- **Lean (extremal):** `pentagon_delta5_extremal_iff` (`PentagonUnique.lean:2098`)
  ```lean
  theorem pentagon_delta5_extremal_iff (G : Flag emptyType) (hTF : IsTriangleFree G)
      (hdeg : maxDegree G ≤ 5) :
      pentagonCount G = 12 * G.size ↔
        ∀ v : Fin G.size, ∃ φ : Fin 16 → Fin G.size, Function.Injective φ ∧ φ 0 = v ∧
          (∀ i j, clebschGraph.Adj i j ↔ G.graph.Adj (φ i) (φ j)) ∧
          (∀ i u, G.graph.Adj (φ i) u → ∃ j, φ j = u)
  ```
  (the RHS = "every vertex sits in an induced, degree-closed copy of Cl" = disjoint union of Clebsch graphs).
- **Defs used:** `clebschGraph`, `pentagonCount`, `maxDegree`, `IsTriangleFree`.
- **Axioms:** `propext, Classical.choice, Quot.sound` — **standard only, no `native_decide`, no user axioms** *(verified).*

### Theorem 1.6 — small maximum degree (Δ = 3, 4)

- **Math:** (i) Δ ≤ 3 ⟹ `P ≤ (6/5)|G|`, equality iff every component is Petersen;
  (ii) Δ ≤ 4 ⟹ `P ≤ (24/5)|G|`. (With Thm 1.5 + the trivial Δ ≤ 2 case, the
  conjecture holds for all Δ ≤ 5.)
- **Lean:**
  - `pentagon_bound_delta3` (`PentagonDelta3.lean:165`): `… maxDegree G ≤ 3 → 5 * pentagonCount G ≤ 6 * G.size`
  - `pentagon_delta3_extremal_iff` (`PentagonDelta3Unique.lean:736`): `5 * P = 6n ↔` every vertex in an induced closed `petersenGraph` copy
  - `pentagon_bound_delta4` (`PentagonDelta4.lean:167`): `… maxDegree G ≤ 4 → 5 * pentagonCount G ≤ 24 * G.size`
  - `pentagon_delta4_witness` (`PentagonDelta4Witness.lean:137`) and `pentagonCountAt_le_24_tight` (`:242`): the C₁₂(2,3) / 11-vertex witnesses attaining the Δ=4 ratio.
- **Defs used:** `pentagonCount`, `pentagonCountAt`, `maxDegree`, `petersenGraph`, `c12Graph`.
- **Axioms:** all `propext, Classical.choice, Quot.sound` — **standard only (kernel `decide`, no `native_decide`), no user axioms.**

---

## 4. Paper 2 — strong edge-colouring

Notation: χ′ₛ = `strongChromaticIndex`, Δ = `maxDegree G`, over `G : Flag emptyType`
(the random result uses a `SimpleGraph` on `Fin n_A ⊕ Fin n_B`). **The SEC bounds
require Δ large**: this is formalised as `∃ D₀, ∀ G, D₀ ≤ maxDegree G → …`.

Each headline comes in a **thesis-tight** form (the paper's constants 1.73, 1.6255,
1.6632·p) and a slightly looser **default** form (1.74, 1.63) restated for citation
parity. **Both forms rest on the same loose
`_F` certificate-output axiom** (`… ≤ 10.644` / `≤ 4.093` / `≤ 4.5496`); the
constant gap is only the `ι`-slack absorbed into the stated coefficient.

### Theorem 1.1 — general SEC bound

- **Math:** `χ′ₛ(G) ≤ 1.73·Δ(G)²` for Δ large.
- **Lean (tight):** `strong_chromatic_index_bound_thesis_tight` (`StrongChromaticIndex.lean:899`)
  ```lean
  theorem strong_chromatic_index_bound_thesis_tight :
      ∃ D₀ : ℕ, ∀ G : Flag emptyType, D₀ ≤ maxDegree G →
        (strongChromaticIndex G : ℝ) ≤ 1.73 * (maxDegree G : ℝ) ^ 2
  ```
  **Default (1.74):** `strong_chromatic_index_bound` (`:810`).
- **Defs used:** `strongChromaticIndex`, `maxDegree`, `lineGraphSqFlag` (in the proof).
- **Axioms:** `propext, Classical.choice, Quot.sound` **+ 4 user axioms** —
  `hurley_colouring_lemma`, `SecBridge.flagBasis_sec_isLocalFlag_F`,
  `SecBridge.sec_combinatorial_identity_F`, and the SDP-output bound
  `SecBridge.phi_evalAlg_O_sec_alg_le_bound_F` (§5.1–5.3). No `native_decide`.

### Theorem 1.2 — bipartite SEC bound

- **Math:** `χ′ₛ(G) ≤ 1.6255·Δ(G)²` for bipartite G, Δ large.
- **Lean (tight):** `strong_chromatic_index_bipartite_thesis_tight` (`StrongChromaticIndex.lean:918`)
  ```lean
  theorem strong_chromatic_index_bipartite_thesis_tight :
      ∃ D₀ : ℕ, ∀ G : Flag emptyType, IsBipartite G → D₀ ≤ maxDegree G →
        (strongChromaticIndex G : ℝ) ≤ 1.6255 * (maxDegree G : ℝ) ^ 2
  ```
  **Default (1.63):** `strong_chromatic_index_bipartite` (`:828`).
- **Defs used:** as 1.1, plus `IsBipartite`.
- **Axioms:** standard **+ 4 user axioms** — `hurley_colouring_lemma`,
  `SecBipartiteBridge.flagBasis_sec_bip_isLocalFlag_F`,
  `SecBipartiteBridge.sec_combinatorial_identity_bipartite_F`,
  `SecBipartiteBridge.phi_evalAlg_O_sec_bip_alg_le_bound_F`.

### Theorem 1.3 — asymmetric SEC bound

- **Math:** for rational r = p ∈ (0,1] and bipartite G with side **maximum**
  degrees Δ_A ≥ Δ_B = p·Δ_A, Δ_A large, `χ′ₛ(G) ≤ 1.6633·Δ_A·Δ_B`
  (equivalently `≤ 1.6632·p·Δ²`, since Δ_A = Δ, Δ_B = p·Δ).
- **Lean (paper-exact per-p form):**
  `strong_chromatic_index_asymmetric_bipartite_thesis_tight` (`StrongChromaticIndex.lean:1132`)
  ```lean
  theorem strong_chromatic_index_asymmetric_bipartite_thesis_tight
      (p : ℝ) (hp1 : 0 < p) (hp2 : p ≤ 1) :
      ∃ D₀ : ℕ, ∀ G : Flag emptyType,
        SecAsymHighSide.IsAsymmetricBipartiteMaxDeg p G → D₀ ≤ maxDegree G →
        (strongChromaticIndex G : ℝ) ≤ 1.6632 * p * (maxDegree G : ℝ) ^ 2
  ```
  Stated on the paper's **max-degree class** `IsAsymmetricBipartiteMaxDeg`. The proof
  runs the **WLOG-biregular reduction**: a high-side completion
  (`SecAsymHighSide.highSide_reduction`) makes the high side exactly Δ-regular, then a
  low-side completion to an exactly `(Δ, ⌊pΔ⌋)`-biregular host
  (`SecAsymReduction.asym_biregular_reduction`, built on
  `SecAsymBiregularCompletion`), each step preserving Δ and not decreasing χ′ₛ; the
  biregular helper `sec_asym_thesis_tight_biregular` (`:1101`) then applies the
  CG4 certificate. A backward-parity corollary
  `…_thesis_tight_regular` (`:1169`) restates it on `IsAsymmetricBipartite`.
- **Lean (p-free Δ²-form):** `strong_chromatic_index_asymmetric_bipartite` (`:1081`)
  and `…_tight` (`:1049`) prove `≤ 1.6633·Δ²`. These carry **no asymmetric identity
  axiom**: an asymmetric-bipartite graph is bipartite and `1.6255 ≤ 1.6633`, so they
  route through `strong_chromatic_index_bipartite_thesis_tight` and rest on the
  **bipartite** `_F` axioms.
- **Defs used:** `strongChromaticIndex`, `maxDegree`, `IsAsymmetricBipartiteMaxDeg`,
  `IsAsymmetricBipartite`, `IsBiregularFloor`.
- **Axioms (per-p form):** standard **+ 4 user axioms** — `hurley_colouring_lemma`,
  `SecAsymmetricBipartiteBridge.flagBasis_asym_isLocalFlag_F`,
  `SecAsymmetricBipartiteBridge.sec_combinatorial_identity_asymmetric_F`,
  `SecAsymmetricBipartiteBridge.phi_evalAlg_O_asym_CG4_le_bound` (all in
  `SecAsymBridgeF.lean`; §5.1–5.3). The p-free forms instead use the 4 bipartite
  axioms of Thm 1.2. No `native_decide`, no separate regularity axiom.

### Theorem 1.4 — asymmetric strong clique number

- **Math:** for bipartite G with sides A, B, `ω(L(G)²) ≤ Δ_A·Δ_B`.
- **Lean:** `omega_lineGraphSq_le_mul_bipartite` (`BipartiteOmegaL2.lean:999`)
  ```lean
  theorem omega_lineGraphSq_le_mul_bipartite
      (G : Flag emptyType) (S : Finset (Fin G.size))
      (hS : ∀ u v : Fin G.size, G.graph.Adj u v → (u ∈ S ↔ v ∉ S)) :
      cliqueNumber (lineGraphSqFlag G) ≤ maxDegreeOn G S * maxDegreeOn G Sᶜ
  ```
  (symmetric corollary `omega_lineGraphSq_le_sq_bipartite` (`:1020`): `≤ Δ²`).
- **Defs used:** `cliqueNumber`, `lineGraphSqFlag`, `maxDegreeOn`.
- **Axioms:** `propext, Classical.choice, Quot.sound` — **standard only, no user axioms** (purely combinatorial).

### Theorem 1.5 — asymmetric induced matching number

- **Math:** for bipartite G, `|E(G)| ≤ ν_s(G)·Δ_A·Δ_B`, i.e. `ν_s(G) ≥ |E(G)|/(Δ_A·Δ_B)`.
- **Lean:** `edges_le_nu_s_mul_mul_bipartite` (`InducedMatchingAsymmetric.lean:383`)
  ```lean
  theorem edges_le_nu_s_mul_mul_bipartite
      (G : Flag emptyType) (S : Finset (Fin G.size))
      (hS : ∀ u v : Fin G.size, G.graph.Adj u v → (u ∈ S ↔ v ∉ S)) :
      (edgeFinset G).card ≤ inducedMatchingNumber G * maxDegreeOn G S * maxDegreeOn G Sᶜ
  ```
  (symmetric corollary `edges_le_nu_s_mul_sq_bipartite` (`:511`): `≤ ν_s·Δ²`).
- **Defs used:** `edgeFinset`, `inducedMatchingNumber`, `maxDegreeOn`.
- **Axioms:** `propext, Classical.choice, Quot.sound` — **standard only, no user axioms** (purely combinatorial).

### Theorem 1.6 — a.a.s. Brualdi–Quinn Massey (random bipartite)

- **Math:** for fixed p ∈ (0,1) and bounded aspect ratio `max(n_A,n_B) ≤ C·min(n_A,n_B)`,
  the random bipartite `G ∼ G(n_A,n_B,p)` satisfies `χ′ₛ(G) ≤ Δ_A(G)·Δ_B(G)`
  asymptotically almost surely (as `min(n_A,n_B) → ∞`).
- **Lean:** `SECRandomBipartite.secRandomBipartite_aas` (`SecRandomBipartite/Closure.lean:962`)
  ```lean
  theorem secRandomBipartite_aas (p : ℝ) (hp_lb : 0 < p) (hp_ub : p < 1)
      (C : ℝ) (hC : 1 ≤ C) :
      ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n_A n_B : ℕ,
        min n_A n_B ≥ N → (max n_A n_B : ℝ) ≤ C * (min n_A n_B : ℝ) →
        probBipartiteRandom n_A n_B p
          (fun G => ∀ [DecidableRel G.Adj], chiPrimeS G ≤ (deltaA G * deltaB G : ℕ∞))
        ≥ 1 - ε
  ```
  ("a.a.s." is spelled out: for every ε > 0 the event probability is ≥ 1 − ε
  once `min n_A n_B` is large enough.)
- **Defs used:** `probBipartiteRandom` (the G(n_A,n_B,p) model), `chiPrimeS`, `deltaA`, `deltaB`.
- **Axioms:** `propext, Classical.choice, Quot.sound` **+ 2 verbatim literature axioms** —
  `SecRandomBipartite.KimVu.kim_vu_concentration_verbatim` and
  `SecRandomBipartite.PippengerSpencer.pippenger_spencer_covering_verbatim` (§5.5).

---

## 5. User-defined axioms — catalogue and mathematical content

Every user axiom below is guarded in `AxiomCheck.lean`. For each: the Lean
statement (elided where a matrix/array body is long), the mathematical fact it
encodes, and its justification.

> **Soundness.** These are the *only* project-specific assumptions. The
> certificate axioms are numerical/combinatorial facts about explicit finite SDP
> certificates (each corroborated by a `native_decide`-checked witness and/or a
> fully-proved smaller-scale peer); the literature axioms are verbatim published
> theorems.

### 5.1 SDP-output bound axioms (weak duality)

Each states that a limit functional's evaluation of an SDP objective is at most the
solver's measured dual optimum, on the certificate's regular (F-faithful) class. The
bounds are *loose* (strictly above the CSDP optima, so cert-supported), and each is
gated by a regularity/`PhiRegular`-shape hypothesis. Justified by the SDPA-LR / CSDP
optima (~10⁻⁸ precision), `native_decide`-verified per-block LDL/PSD + slack-budget
witnesses in the `*Certificate.lean` files, and a proved size-5 peer.

| Axiom (file:line) | Encodes | Feeds |
|---|---|---|
| `PentagonQBridge.phi_evalAlg_O_Q_alg_le_bound` (`:9954`) | `φ(O_Q) ≤ 0.4146` (SDPA optimum ≈ 0.41458); halves to the per-pentagon 0.2073 | Paper 1, Thm 1.2 |
| `SecBridge.phi_evalAlg_O_sec_alg_le_bound_F` (`:669`) | `φ(O_sec) ≤ 10.644` | Paper 2, Thm 1.1 |
| `SecBipartiteBridge.phi_evalAlg_O_sec_bip_alg_le_bound_F` (`:377`) | `φ ≤ 4.093` (bipartite factor 1/8) | Paper 2, Thm 1.2 |
| `SecAsymmetricBipartiteBridge.phi_evalAlg_O_asym_CG4_le_bound` (`SecAsymBridgeF.lean:571`) | `φ ≤ 8·secAsymDensityBound = 4.5496` (F-free CG4, p = 1; `4.5496 > 4.5490937` CSDP optimum) | Paper 2, Thm 1.3 (per-p form) |

### 5.2 Basis-locality axioms

Each states every SDP basis flag is a *local* flag (bounded induced-copy count
O(Δ^size) ⟹ bounded density). The algorithmic `native_decide` witness is deferred;
the mathematical claim is proved at the identical size-8 scale by the *theorem*
`PentagonQBridge.flagBasis_isLocalFlag` (Paper 1's analogue is not an axiom).

- `SecBridge.flagBasis_sec_isLocalFlag_F` (`:701`) — the 17,950 size-5 SEC basis flags → Paper 2 Thm 1.1
- `SecBipartiteBridge.flagBasis_sec_bip_isLocalFlag_F` (`:404`) — the 3,808 bipartite basis flags → Paper 2 Thm 1.2
- `SecAsymmetricBipartiteBridge.flagBasis_asym_isLocalFlag_F` (`SecAsymBridgeF.lean:586`) — the 334 F-free CG4 basis flags → Paper 2 Thm 1.3

### 5.3 Combinatorial-bridge-identity axioms

Each equates the raw per-graph combinatorial density (pentagon count, or
edges-in-neighbourhood of L(G)²) with the certificate-coefficient-weighted sum of
basis-flag densities, along any regular Δ-increasing sequence. The coefficient
vectors are the SDPA objective emitted by `emit_lean_cert.py`. The natural proof is
a ~1000-LOC tuple↔embedding bijection; deferred because class-enumeration at
hand-coded density is ~10⁵ LOC. Corroborated by the proved size-5 peer
`brrb_averaging_identity`.

- `PentagonQBridge.pentagonQ_basis_combinatorial_identity_step1` (`:8827`) —
  `2·P(v)/Δ⁵ = Σ_j O_Q_coef_j · ρ(F_j)` (factor 2 = each pentagon-extension tuple counted by its two S∩N(v) vertices) → Paper 1 Thm 1.2
- `SecBridge.sec_combinatorial_identity_F` (`:586`) —
  the F-faithful `edgesInNbhd(L(G)²,·)/C(Δ,2) = (1/16)·Σ_j O_sec_coef_j · ρ(F_j)` (per-F-edge form) → Paper 2 Thm 1.1
- `SecBipartiteBridge.sec_combinatorial_identity_bipartite_F` (`:301`) — as above, factor 1/8 → Paper 2 Thm 1.2
- `SecAsymmetricBipartiteBridge.sec_combinatorial_identity_asymmetric_F` (`SecAsymBridgeF.lean:524`) — factor 1/8 over the 334 CG4 flags, **gated on `IsAsymmetricBipartite 1 ∧ IsRegular`** (the L5 soundness re-gate; the identity is exact only on genuinely regular hosts) → Paper 2 Thm 1.3

### 5.4 Regularity — a hypothesis, not an axiom

There is **no** standalone asymmetric-regularity axiom. Instead the asymmetric
identity §5.3 is *gated* on genuine `IsRegular`, and the headline reaches arbitrary
max-degree hosts through the **proved** WLOG-biregular reduction — high-side
completion (`SecAsymHighSide`), low-side completion to an exact `(Δ, ⌊pΔ⌋)`-biregular
host (`SecAsymBiregularCompletion`), and χ′ₛ-monotonicity along the induced embedding
(`SecAsymReduction`). All three modules depend only on the standard Lean axioms.

### 5.5 The Hurley sparse-colouring lemma (Paper 2, all SEC headlines)

- `hurley_colouring_lemma` (`StrongEdgeColouring.lean:343`) — **verbatim
  Hurley–de Joannis de Verclos–Kang 2022** (arXiv:2007.07874 / SODA 2021,
  `col_result`):
  ```lean
  axiom hurley_colouring_lemma (sigma iota : ℝ)
      (hsigma : 0 < sigma) (hsigma1 : sigma ≤ 1) (hiota : 0 < iota) :
      ∃ X₀ : ℕ, ∀ G : Flag emptyType, X₀ ≤ maxDegree G →
        (∀ v : Fin G.size, (edgesInNeighbourhood G v : ℝ) ≤
          (1 - sigma) * (Nat.choose (maxDegree G) 2 : ℝ)) →
        (chromaticNumber G : ℝ) ≤ (1 - colouringEps sigma + iota) * (maxDegree G : ℝ)
  ```
  A σ-*sparse* graph (every neighbourhood spans ≤ (1−σ)·C(Δ,2) edges) has
  `χ(G) ≤ (1 − ε(σ) + ι)·Δ`, where `ε(σ) = σ/2 − σ^{3/2}/6`. The SEC application
  verifies L(G)² is σ-sparse (from the SDP bound) and applies this — the
  probabilistic-colouring "Step 2" of the Molloy–Reed strategy. Cited because
  Mathlib lacks it. Its **degree-scale corollary** `hurley_colouring_scale`
  (`SecFPadding.lean:382`, a K_{D,D}-padding argument) is a proved *theorem*, not an
  axiom (guarded in `AxiomCheck.lean` to certify it adds no new axiom).

### 5.6 Verbatim literature axioms (Paper 2, random bipartite)

Both cited verbatim because Mathlib lacks polynomial-concentration and
semirandom-nibble infrastructure.

- `SecRandomBipartite.KimVu.kim_vu_concentration_verbatim`
  (`SecRandomBipartite/KimVuEffects.lean:271`) — **Kim & Vu, Combinatorica 20
  (2000)**: for a degree-k polynomial f of independent Boolean variables with
  partial-derivative effect bounds E, E′, `Pr(|f − 𝔼f| > a_k·√(E·E′)·λ^k) ≤
  C·exp(−λ + (k−1)·log #vars)` with `a_k = 8^k√(k!)`.
- `SecRandomBipartite.PippengerSpencer.pippenger_spencer_covering_verbatim`
  (`SecRandomBipartite/PippengerSpencer.lean:63`) — **Pippenger–Spencer, JCTA 51
  (1989) / Kahn 1996** (almost-regular nibble): a k-uniform, (1±δ)-regular
  hypergraph with codegree ≤ δ·D has a matching covering all but ≤ ⌈ε·n⌉ vertices.

---

## 6. Summary table

| Paper · result | Lean theorem | User axioms |
|---|---|---|
| **1** · 1.1 simple bound | `pentagon_bound_simple` | none |
| **1** · 1.2 tighter bound | `pentagon_bound_full` | 2 (pentagon-Q bridge) |
| **1** · 1.4 Clebsch-blowup tightness | `clebsch_blowup_tight` | none |
| **1** · 1.5 Δ=5 characterisation | `pentagon_delta5_tight`, `pentagon_delta5_extremal_iff` | none |
| **1** · 1.6 small degree (Δ=3,4) | `pentagon_bound_delta3`(+`_extremal_iff`), `pentagon_bound_delta4`(+witnesses) | none |
| **2** · 1.1 general SEC | `strong_chromatic_index_bound[_thesis_tight]` | 4 (Hurley + 3 general `_F` cert) |
| **2** · 1.2 bipartite SEC | `strong_chromatic_index_bipartite[_thesis_tight]` | 4 (Hurley + 3 bipartite `_F` cert) |
| **2** · 1.3 asymmetric SEC | `strong_chromatic_index_asymmetric_bipartite[_thesis_tight]` | 4 (Hurley + 3 asymmetric `_F` cert for the per-p form; the p-free form reuses the bipartite axioms) |
| **2** · 1.4 strong clique ω(L(G)²) | `omega_lineGraphSq_le_mul_bipartite` | none |
| **2** · 1.5 induced matching ν_s | `edges_le_nu_s_mul_mul_bipartite` | none |
| **2** · 1.6 a.a.s. Brualdi–Quinn Massey | `secRandomBipartite_aas` | 2 (Kim–Vu, Pippenger–Spencer, verbatim) |

Distinct user axioms across the whole project: **2** (Paper 1 pentagon-Q) + **1**
Hurley + **9** SEC certificate bridge axioms (general/bipartite/asymmetric ×
{output, locality, bridge-identity}, all F-faithful) + **2** verbatim literature =
**14** — a small, catalogued set; everything else, including the WLOG-biregular
reduction, is proved from the standard Lean axioms.
