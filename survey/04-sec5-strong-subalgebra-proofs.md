# Section 5 of Zhuk 2404.01080 — "Proof of the properties of strong subuniverses"

Deep read of `/tmp/claude-1000/-home-alvaro-claude-zeb/b3d460d7-227a-4a0c-983d-31fbf26d8692/scratchpad/papers/src2404/StrongSubalgebras.tex`
(3144 source lines, of which ~700 are commented-out dead material).
Cross-referenced against `main.tex` §2 (L1064–1931, definitions and statements),
`necessaryClaims.tex` (§2.4), and `refs.bib`.
Statement numbers below are the *printed* numbers from the compiled PDF
(`papers/zhuk2404.txt`); labels are the LaTeX labels, which is what a blueprint
should key on.

---

## 0. Orientation: what §5 is and how big it is

§5 proves **everything** stated without proof in §2.2/§2.3 (the "strong/linear
subuniverse calculus"), plus 37 new auxiliary statements of its own. Structure:

| Subsection | Title | src lines | new stmts | restated §2 stmts |
|---|---|---|---|---|
| 5.1 | Additional definitions | 48–70 | — | — |
| 5.2 | Subuniverses of types BA, C, S | 71–345 | 61–74 (14) | — |
| 5.3 | Intersection property | 347–1020 | 75–80 (6) | — |
| 5.4 | Properties of PC or Linear congruences | 1022–1735 | 81–87 (7) | 7, 8, 9, 10 |
| 5.5 | Types interaction | 1736–1927 | 88, 89 (2) | — |
| 5.6 | Factorization of strong subalgebras | 1928–2296 | 90–94 (5) | — |
| 5.7 | Proof of the remaining statements from §2.3 | 2297–3143 | 95, 96, 97 (3) | 11, 12, 13, 14, 16, 17, 18, 20, 21, 22, 23, 24, 25 |

**54 statements total** (37 new = Lemmas 61–97; 17 restatements of §2 results).
Of the 37 new ones, **12 are imported verbatim or by a one-line "see [ref]"**
(§3 below). Total proof text ≈ **1646 non-blank non-comment source lines**;
two proofs alone (Lemmas 77 and 78) account for **350** of them, i.e. 21%.

Notation reminders (from §2, needed to read anything below):

* `C <_T^A B` for `T ∈ {BA, C, S, D, L, PC}` — six subuniverse types. `D` =
  "dividing": ∃ irreducible congruence σ on **A** with (1) `B² ⊆ σ*`, (2)
  `C = B ∩ E` for a block `E` of σ, (3) `B/σ` is BA-and-center-free. `L`/`PC` =
  `D` with σ linear / PC. `S` = ∃ `D ≤ C` with `D <_{BA} B` **and** `D <_C B`.
* `C ⋘^A B` — chain `C = B_n <_{T_n}^A … <_{T_1}^A B_0 = B` with
  `T_i ∈ {BA, C, S, D}` (note: **not** L or PC; L/PC are refinements of D and a
  chain records only D). `n = 0` allowed, so ⋘ is reflexive. `B ⋘ A` := `B ⋘^A A`.
* `C ≤_{MT}^A B` — `C = C_1 ∩ … ∩ C_t ≠ ∅` with each `C_i <_T^A B`, `T ∈ {L, PC, D}`.
* `σ*` — for irreducible σ, the minimum `δ ≤ A×A` with `δ ⊋ σ` stable under σ.
* bridge `δ ≤ D_1² × D_2²` from σ₁ to σ₂; `δ̃(x,y) := δ(x,x,y,y)`.
* `Ḃ⋘`, `≤̇`, `<̇` (dotted) allow the empty set.
* **Convention** (main.tex L1534, easy to miss): in `C <_{T(σ)}^A B` with
  `T ∈ {BA, C, S}`, σ is by convention the **full** congruence `A²`. §5 relies on
  this silently and heavily (Lemma 77, Lemma 78).

---

## 1. Inventory

Legend for **Proof**: `n L` = n non-blank non-comment source lines of proof;
`IMPORT` = no proof, cited to the literature; `DELEG` = proof body is a pointer
to the literature.

### 5.2 — Subuniverses of types BA, C, S (L71–345)

| # | Label | Statement (faithful) | Proof |
|---|---|---|---|
| 61 | `LEMBACenterSPossibleIntersections` | `B <_{T₁} A`, `C <_{T₂} A`, `B ∩ C = ∅`, `T₁,T₂ ∈ {BA,C,S}` ⟹ `T₁ = T₂ ∈ {BA,C}`. | IMPORT [zhuk2021strong, Lem 6.25] |
| 62 | `LEMBACenterSImplyPPDefinition` | `R ≤ Aⁿ` defined by a pp-formula Φ containing a relation `S`; Φ′ obtained from Φ by replacing **every** occurrence of `S` by `S' <_T S`, `T ∈ {BA,C}`. Then Φ′ defines `R'` with `R' ≤_T R`. | IMPORT [DecidingAbsorption, Lem 2.9]; [zhuk2021strong, Lem 6.1, Thm 6.9] |
| 63 | `LEMBACenterImplyIntersection` | `B ≤_T A`, `C ≤ A`, `T ∈ {BA,C}` ⟹ `B ∩ C ≤_T C`. | none ("The above lemma implies an easier claim") |
| 64 | `LEMStrongNonemptyIntersection` | `C ⋘^A B ⋘ A` and `D <_{BA,C} B` ⟹ `C ∩ D ≠ ∅`. | 15 L |
| 65 | `LEMBACenterSImplyFactor` | `B ≤_T A`, σ a congruence on A, `T ∈ {BA,C,S}` ⟹ `B/σ ≤_T A/σ`. | DELEG 6 L (T=BA "straightforward"; T=C → [zhuk2021strong, Lem 6.8]; T=S "combination") |
| 66 | `LemAbsorptionImpliesEssential` | `B ≤ A`, `n ≥ 2`. `B` is absorbing with an operation of arity `n` ⟺ ¬∃ `S ≤ Aⁿ` with `S ∩ Bⁿ = ∅` and `S ∩ (B^{i-1} × A × B^{n-i}) ≠ ∅` ∀i. | IMPORT [DecidingAbsorption, Prop 2.14]; [zhuk2021strong, Lem 3.2] |
| 67 | `LEMBACenterSOnPowerImplies` | `B <_T Aⁿ`, `T ∈ {BA,C,S}` ⟹ ∃ `C <_T A`. | DELEG 6 L ([zhuk2021strong, Lem 6.24]; "for T=S just repeat the same proof word to word") |
| 68 | `LEMBACenterLinkedness` | `R ≤_sd A₁×A₂`, `B₁,B₂` absorbing subuniverses of `A₁,A₂`, `R ∩ (B₁×B₂) ≤_sd B₁×B₂`, `R` linked ⟹ `R ∩ (B₁×B₂)` linked. | IMPORT [barto2012absorbing, Prop 2.15(i)] |
| 69 | `LEMCentralRelationImplies` | `R ≤_sd A×B`, `C = {c ∈ A : ∀b ∈ B, (c,b) ∈ R}`. Then `C` is a central subuniverse of **A**, or **B** has a nontrivial binary absorbing subuniverse. | IMPORT [zhuk2021strong, Thm 6.15] |
| 70 | `LEMLinkedImpliesBACenter` | `R ⪇_sd A×B`, `R` linked ⟹ ∃ BA or central subuniverse on **A** or **B**. | IMPORT [ZebsNotes, Thm 3.11.1] |
| 71 | `LEMAbsorbingEquality` | `0_A ⊆ σ ≤ A²`, `ω <_{BA} σ` ⟹ `ω ∩ 0_A ≠ ∅`. | IMPORT [zhuk2020proof, Lem 7.2] |
| 72 | `LEMBAConLeftOrCenterOnRight` | `R ≤_sd A×B`, **A** BA-and-center-free, `LeftLinked(R) = A²`, `C = {c ∈ B : A×{c} ⊆ R}`. Then `C ≠ ∅` and `C ≤_{BA,C} B`. | 33 L (self-contained; the paper notes it "can be derived from Lemmas 3.11.2/3.11.3 of [ZebsNotes]") |
| 73 | `LEMReverseHomomorphism` | `f : A ↠ A'` surjective hom, `T ∈ {BA,C,S,L,D}`. Then `C' <_{T(σ)}^{A} B' ⟹ f⁻¹(C') <_{T(f⁻¹(σ))}^{A} f⁻¹(B')`. | 19 L (BA/C DELEG to [ZebsNotes §3.15]) |
| 74 | `CORReverseHomomorphism` | `R ≤_sd A₁×…×A_n`, `C₁ <_{T(σ)}^{A₁} B₁ ≤ A₁`, `T ∈ {BA,C,S,L,D}` ⟹ `R ∩ (C₁×A₂×…×A_n) <_{T(σ)}^R R ∩ (B₁×A₂×…×A_n)`. | 6 L |

### 5.3 — Intersection property (L347–1020)

| # | Label | Statement | Proof |
|---|---|---|---|
| 75 | `LEMTotallySymmetricWithoutBACenter` | `R ≤ Aⁿ` totally symmetric, **A** BA-and-center-free, `pr₁,₂(R) = A²`, and `(a₁,…,a_n) ∈ R ⟹ (a₁,a₁,a₂,…,a_{n-1}) ∈ R`. Then `R = Aⁿ`. | 20 L (induction on n) |
| 76 | `LEMTotallySymmetricRelationForIrreducible` | σ a dividing congruence for `B ≤ A`; `R ≤ (A/σ)ⁿ` reflexive, totally symmetric, closed under `(a₁,…,a_n) ↦ (a₁,a₁,a₂,…,a_{n-1})`. Then `(B/σ)ⁿ ⊆ R` or `R = {(a/σ,…,a/σ) : a ∈ A}`. | 13 L |
| 77 | `LEMSelfIntersectionPC` | `B_k <_{T_k(σ_k)}^A … <_{T_1(σ_1)}^A B_0 = A`, δ a congruence on A, all `T_i ∈ {BA,C,S,D}`, `m ∈ [k]`, `T_m = D`. Then `((B_k ∘ δ) ∩ B_{m-1})/σ_m ∈ {B_{m-1}/σ_m, B_m/σ_m}`; and in the second case `σ_m ⊇ δ ∩ σ_1 ∩ … ∩ σ_{m-1}`. | **141 L** (induction on k; Case 1 `k=m` with subcases 1A/1B and subsubcases 1B1–1B3; Case 2 `k>m` with 2A/2B/2C) |
| 78 | `LEMIntersectionPCLinearIsGood` | `B ⋘ A`, `C ⋘ A`, `B ∩ C ≠ ∅`. **(d)** If δ is a dividing congruence for `B ≤ A` then `\|(B∩C)/δ\| = 1` or `(B∩C)/δ = B/δ`; moreover if `\|(B∩C)/δ\| = 1` then `δ ⊇ δ_1 ∩ … ∩ δ_s` where `δ_1,…,δ_s` are the dividing congruences from the definitions of `B ⋘ A` and `C ⋘ A`. **(s)** If `G <_{BA,C} B` then `G ∩ C ≠ ∅`. | **209 L** (induction on `k+ℓ`; (s) 3 cases; (d) Case 1 / Case 2 with subcases 2A(2A1–2A3), 2B(2B1–2B3), 2C) |
| 79 | `CORIntersectionPCLinearIsGood` | `R ≤_sd A₁×A₂`, `B₁ ⋘ A₁`, `B₂ ⋘ A₂`, σ a dividing congruence for `B₁ ⋘ A₁`. Then `pr₁(R ∩ (B₁×B₂))/σ` is empty, of size 1, or `= B₁/σ`. | 15 L |
| 80 | `CORParallelogramPropertyForD` | `B₁ ⋘ A`, `B₂ ⋘ A`, `C₁,C₁' <_{D(σ₁)}^A B₁`, `C₂,C₂' <_{D(σ₂)}^A B₂`, `C₁'∩C₂ ≠ ∅`, `C₁∩C₂' ≠ ∅`, `C₁'∩C₂' ≠ ∅` ⟹ `C₁∩C₂ ≠ ∅`. | 38 L |

### 5.4 — Properties of PC or Linear congruences (L1022–1735)

Preceded by definitions of *polynomially equivalent*, *affine*, *Abelian* (the
term-condition definition, main text L1067–1073).

| # | Label | Statement | Proof |
|---|---|---|---|
| 81 | `LEMAbelianEquivalentDefinition` | **A** Abelian ⟺ ∃ congruence δ on **A²** such that `{(a,a) : a ∈ A}` is a block of δ. | IMPORT [hobby1988structure] |
| 82 | `LemBridgeEquivalentToAbelianness` | **A** Abelian ⟺ ∃ bridge δ from `0_A` to `0_A` with `δ̃ = pr₁,₂(δ) = pr₃,₄(δ) = A²`. | 7 L |
| 83 | `LEMAbelianEqualAffineForWNU` | Finite **A** with a WNU term operation: Abelian ⟺ affine. | IMPORT [hobby1988structure] |
| 84 | `LEMNiceBridgeGivesAbelianGroup` | σ a congruence on **A**, δ a bridge σ→σ with `pr₁,₂(δ) = δ̃ = A²` and `δ(x₁,x₂,x₃,x₄) = δ(x₃,x₄,x₁,x₂)`. Then ∃ abelian group `(G;+,−)` with `(A/σ; δ/σ) ≅ (G; x₁−x₂=x₃−x₄)`. | 26 L |
| 85 | `LEMBlockOfGoodBridgeDoesNotHaveBAC` | δ a bridge from `0_A` to `0_A`, `pr₁,₂(δ) ⊆ δ̃`, `pr₁,₂(δ)` linked ⟹ **A** is BA-and-center-free. | **89 L** (induction on \|A\|; Cases 1/2, sub-cases T=BA / T=C) |
| 86 | `LEMNontrivialReflexiveBridgeImplies` | σ irreducible on **A**, δ a bridge σ→σ with `δ̃ ⊋ σ`. Then (1) `σ*` is a congruence; (2) `B/σ` is BA-and-center-free for each block `B` of `σ*`; (3) if δ is symmetric in the two pairs, ∃ prime `p` s.t. for each block `B` of `σ*`, `(B/σ; (δ ∩ B⁴)/σ) ≅ (Z_p^{n_B}; x₁−x₂=x₃−x₄)`, `n_B ≥ 0`. | 59 L |
| **7** | `LEMLinearEquivalentConditions` | σ irreducible ⟹ [σ linear ⟺ ∃ bridge δ from σ to σ with `δ̃ ⊋ σ`]. | 11 L |
| 87 | `LEMPCCongruencePropertyInductiveStep` | σ a congruence on **A**, δ a **reflexive** bridge σ→σ with (1) `δ(x₁,x₂,x₃,x₄) = δ(x₃,x₄,x₁,x₂)`; (2) `(a,b,a,b),(b,a,b,a) ∈ δ` ∀`(a,b) ∈ pr₁,₂(δ)`; (3) `RightLinked(pr₁,₂,₃(δ)) = A²`. Then ∃`a ≠ b` with `(a,a,b,b) ∈ δ`. | 52 L (induction on \|A\|; Cases 1/2/3) |
| **9** | `LEMPCBridgesAreTrivial` | σ a PC congruence on A. Any reflexive bridge δ σ→σ with `pr₁,₂(δ) = pr₃,₄(δ) = σ*` equals `σ(x₁,x₃) ∧ σ(x₂,x₄)` or `σ(x₁,x₄) ∧ σ(x₂,x₃)`. | **89 L** (auxiliary bridge ξ; Cases 1/2/3; subcases 1A/1B via constructed relations ζ₁, ζ₂) |
| **8** | `LEMNoBridgeBetweenDifferentTypes` | σ₁ linear, σ₂ irreducible, δ a bridge σ₁→σ₂ ⟹ σ₂ linear. | **92 L** (constructs δ′, δ″, ω, ξ₁, ξ₂, ζ) |
| **10** | `LEMBridgeTOPCCongruence` | δ a bridge from a PC congruence σ₁ on **A₁** to an irreducible σ₂ on **A₂**, `pr₁,₂(δ) = σ₁*`, `pr₃,₄(δ) = σ₂*`. Then (1) σ₂ is PC; (2) `A₁/σ₁ ≅ A₂/σ₂`; (3) `{(a/σ₁,b/σ₂) : (a,b) ∈ δ̃}` is bijective; (4) `δ = δ̃(x₁,x₃) ∧ δ̃(x₂,x₄)` or `δ̃(x₁,x₄) ∧ δ̃(x₂,x₃)`. | 16 L |

### 5.5 — Types interaction (L1736–1927)

| # | Label | Statement | Proof |
|---|---|---|---|
| 88 | `LEMBridgeBetweenCongruences` | ω, σ₁, σ₂ congruences on **A**, `ω ∩ σ₁ = ω ∩ σ₂`, `ω ∖ σ₁ ≠ ∅` ⟹ ∃ bridge δ from σ₁ to σ₂ with `δ̃ = σ₁ ∘ σ₂`. | 24 L (proof given although cited as [zhuk2020proof, Lem 8.19]) |
| 89 | `LEMTwoStableIntersection` | `C₁ <_{T₁(σ₁)}^A B₁ ⋘ A`, `C₂ <_{T₂(σ₂)}^A B₂ ⋘ A`, `T_i ∈ {BA,C,S,D}`, `C₁∩B₂ ≠ ∅`, `B₁∩C₂ ≠ ∅`, `C₁∩C₂ = ∅`. Then (1) `T₁ = T₂ ∈ {BA,C,D}`; (2) if `T₁ = T₂ = D` then ∃ bridge δ from σ₁ to σ₂ with `δ̃ = σ₁ ∘ σ₂`. | 54 L |

### 5.6 — Factorization of strong subalgebras (L1928–2296)

| # | Label | Statement | Proof |
|---|---|---|---|
| 90 | `LEMCenterCanBePushedIn` | `R ≤_sd A₁×A₂`, `R ∩ (B₁×B₂) ≠ ∅`, `B₁ ⋘ A₁`, `B₂ ⋘ A₂`, σ a congruence on `A₁`, `B₁/σ` BA-and-center-free, ∃`c ∈ A₂` with `(E×{c}) ∩ R ≠ ∅` ∀`E ∈ B₁/σ`. Then such a `c` exists **in `B₂`**. | 50 L |
| 91 | `LEMLeftLinkedStayFull` | same setting; `(LeftLinked(R) ∩ B₁²)/σ = (B₁/σ)²` ⟹ `LeftLinked(R ∩ (B₁×B₂))/σ = (B₁/σ)²`. | 38 L |
| 92 | `LEMCongruenceEitherCutOrDoNothing` | σ a dividing congruence for `B ⋘ A`, δ a congruence on A, `(δ ∩ B²)/σ ≠ B²/σ`. Let ω = intersection of all dividing congruences coming from `B ⋘ A`. Then (1) `δ ∩ B² ⊆ σ ∩ B²`; (2) `σ ⊇ δ ∩ ω`; (3) `(δ ∨ (σ∩ω)) ∩ B² = σ ∩ B²`; (4) `(δ ∨ (σ∩ω)) ∩ ω = σ ∩ ω`. | 44 L |
| 93 | `LEMMainExistenceOfIrreducibleCongruence` | `B ⋘ A`, σ a congruence on A with `\|B/σ\| > 1` and `B/σ` BA-and-center-free ⟹ ∃ dividing congruence δ for `B ⋘ A` with `δ ⊇ σ`. | 24 L |
| 94 | `LEMFactorByDelta` | δ a congruence on A, `C <_{T(σ)}^A B ⋘ A`, `T ∈ {PC,L}`. Then `C/δ = B/δ`, or `C/δ <_S B/δ`, or `C/δ <_T^{A/δ} B/δ`; and in the last case `δ ∩ B² ⊆ σ ∩ B²`. | 45 L |

### 5.7 — Remaining statements from §2.3 (L2297–3143)

| # | Label | Statement | Proof |
|---|---|---|---|
| **13** | `LEMUbiquity` | `B ⋘ A`, `\|B\| > 1` ⟹ ∃`C <_T^A B` with `T ∈ {BA,C,L,PC}`. | 8 L |
| **20** | `LEMIntersectALL` | `B ⋘ A`, `D ⋘ A` ⟹ (i) `B ∩ D ⋘̇ A`; (t) `C <_{T(σ)}^A B ⟹ C ∩ D ≤̇_{T(σ)}^A B ∩ D`. | 35 L |
| **14** | `LEMPropagation` | `f : A ↠ A'`. (f) `C ⋘^A B ⟹ f(C) ⋘ f(B)`; (b) `C' ⋘^{A'} B' ⟹ f⁻¹(C') ⋘ f⁻¹(B)`; (ft) `C <_{T(σ)}^A B ⋘ A ⟹ f(C)=f(B)` or `f(C) <_S f(B)` or `f(C) <_T^{A'} f(B)`; (bt) as Lemma 73; (fs) `T ∈ {BA,C,S}`, `C <_T B ⟹ f(C) ≤_T f(B)`; (fm) `C ≤_{MT}^A B ⋘ A` and `f(B)` S-free `⟹ f(C) ≤_{MT}^{A'} f(B)`; (bm) `C' ≤_{MT}^{A'} B' ⋘ A' ⟹ f⁻¹(C) ≤_{MT}^A f⁻¹(B)`. | 50 L (only (fm) is substantial) |
| **16** | `CORPropagateFromFactor` | δ a congruence on A, `B,C ≤ A`: (f) `C/δ ⋘^{A/δ} B/δ ⟺ C∘δ ⋘^A B∘δ`; (t) same with `<_T`. | 8 L |
| **17** | `CORPropagateMultiplyByCongruence` | δ a congruence on A: (f) `C ⋘^A B ⟹ C∘δ ⋘^A B∘δ`; (t) `C <_{T(σ)}^A B ⋘ A ⟹ (C∘δ = B∘δ` or `C∘δ <_S^A B∘δ` or `C∘δ <_T^A B∘δ)`; (e) if also `δ ⊆ σ` then `C∘δ <_T^A B∘δ`. | 17 L |
| **18** | `CORPropagateToRelations` | `R ≤_sd A₁×…×A_n`, `B_i ⋘ A_i`: (r) `R ∩ ∏B_i ⋘̇ R`; (r1) `pr₁(R ∩ ∏B_i) ⋘̇ A₁`; (b) `∀i C_i ⋘^{A_i} B_i ⟹ R ∩ ∏C_i ⋘̇^R R ∩ ∏B_i`; (b1) projected version; (m) `∀i C_i ≤_{MT}^{A_i} B_i ⟹ R ∩ ∏C_i ≤̇_{MT}^R R ∩ ∏B_i`; (m1) projected version, assuming `pr₁(R ∩ ∏B_i)` S-free. | 39 L |
| **21** | `THMMainStableIntersection` | `C_i <_{T_i(σ_i)}^A B_i ⋘ A`, `T_i ∈ {BA,C,S,L,PC}`, `n ≥ 2`, `⋂C_i = ∅`, `B_j ∩ ⋂_{i≠j} C_i ≠ ∅` ∀j. Then (ba) all `T_i = BA`; or (l) all `T_i = L` and ∀k,ℓ ∃ bridge δ from σ_k to σ_ℓ with `δ̃ = σ_k ∘ σ_ℓ`; or (c) `n = 2`, `T₁=T₂=C`; or (pc) `n = 2`, `T₁=T₂=PC`, `σ₁ = σ₂`. | 32 L |
| **22** | `CORMainStableIntersection` | relational version of Thm 21: `R ≤_sd A₁×…×A_n`, `C_i <_{T_i(σ_i)}^{A_i} B_i ⋘ A_i`, `R ∩ ∏C_i = ∅`, `R ∩ (C₁×…×B_j×…×C_n) ≠ ∅` ∀j. Conclusions as above with `δ̃ = σ_k ∘ pr_{k,ℓ}(R) ∘ σ_ℓ` in (l), and in (pc) `A₁/σ₁ ≅ A₂/σ₂` with `{(a/σ₁,b/σ₂) : (a,b) ∈ R}` bijective. | 32 L |
| **23** | `LEMMultiTypeStillStable` | `C ≤_{MT}^A B ⟹ C <_T^A … <_T^A B` and `C ⋘^A B`. | 10 L |
| **11** | `LEMLInearOnTheTopIsEasy` | σ linear on `A ∈ V_n` with `σ* = A²` ⟹ `A/σ ≅ Z_p` for a prime p. | 13 L |
| **12** | `LEMPCOnTheTopIsEasy` | σ a PC congruence on A with `σ* = A²` ⟹ `A/σ` is a PC (polynomially complete) algebra. | 14 L |
| 95 | `LEMPreserveLinkdnessOneStepAUX` | `R ≤_sd A₁×A₂`, `C_i ≤_{D(σ_i)}^{A_i} B_i ⋘ A_i` (source says `⋘ A₁` — typo), `S` = rectangular closure of R, `R ∩ (B₁×C₂) ≠ ∅`, `R ∩ (C₁×B₂) ≠ ∅`, `S ∩ (C₁×C₂) ≠ ∅` ⟹ `R ∩ (C₁×C₂) ≠ ∅`. | 59 L |
| 96 | `LEMPreserveLinkdnessOneStep` | `R ≤_sd A₁×A₂`, `C₁ ≤_{D(σ)}^{A₁} B₁ ⋘ A₁`, `B₂ ⋘ A₂`, `S` = rect. closure, `R ∩ (B₁×B₂) ≠ ∅`, `S ∩ (C₁×B₂) ≠ ∅` ⟹ `R ∩ (C₁×B₂) ≠ ∅`. | 12 L |
| **24** | `LEMPreserveLinkdness` | same with `C_i ≤_{MD}^{A_i} B_i ⋘ A_i`, `S ∩ (C₁×C₂) ≠ ∅` ⟹ `R ∩ (C₁×C₂) ≠ ∅`. | 5 L |
| 97 | `LEMMultiplyByAllLinear` | `C₁ <_{MT}^A B₁ ⋘ A`, `T ∈ {PC,L,D}`, `B₂ ⋘ A`, `C₁ ∩ B₂ = ∅`, `B₁ ∩ B₂ ≠ ∅`. Then `(C₁ ∘ (ω₁∩…∩ω_s)) ∩ B₂ = ∅` where ω₁,…,ω_s are **all** congruences of type T on **A** with `ω_i* ⊇ B₁²`. | 44 L (downward induction on \|B₁\|) |
| **25** | `LEMMaximalMultExtention` | `C₁ <_{MT}^A B₁ ⋘ A`, `B₂ ⋘ A`, `C₁ ∩ B₂ = ∅`, `B₁ ∩ B₂ ≠ ∅`, σ a **maximal** congruence with `(C₁∘σ) ∩ B₂ = ∅`. Then `σ = ω₁ ∩ … ∩ ω_s` for congruences ω_i of type T with `ω_i* ⊇ B₁²`. | 27 L |

---

## 2. Subsection-by-subsection digest

### 5.1 Additional definitions (L48–70) — 3 definitions, no proofs

1. **"Symmetric" is redefined**: "In this section we call a relation *symmetric*
   if any permutation of its variables gives the same relation" — i.e. *totally
   symmetric*. Only used in Lemmas 75/76.
2. `LeftLinked(R)` for `R ≤ A₁×…×A_n`: the minimal equivalence relation on
   `pr₁(R)` such that `(a₁,a₂,…,a_n),(b₁,a₂,…,a_n) ∈ R ⟹ (a₁,b₁) ∈ LeftLinked(R)`.
   `RightLinked(R)` symmetrically on `pr_n(R)`.
3. **central relation**: `R ⪇ A×B` is *central* if ∃`b ∈ B` with `A×{b} ⊆ R`.
   (Note the properness `⪇`, and note that this is a *relation* property while
   "central subuniverse" is a different notion — both are used within the same
   paragraphs.)

### 5.2 Subuniverses of types BA, C, S (L71–345)

This is the **import layer**. 10 of the 14 statements are cited to
[zhuk2021strong], [DecidingAbsorption], [barto2012absorbing], [ZebsNotes] or
[zhuk2020proof]; only Lemmas 64, 72, 73, 74 are proved here (and 73's BA/C case
is delegated to [ZebsNotes §3.15]).

The two proved workhorses:

* **Lemma 72** (`LEMBAConLeftOrCenterOnRight`) is the technical engine used
  everywhere later (Lemmas 87, 91, 94). Proof structure: (i) define
  `W_n = {(a₁,…,a_n) : ∃b ∀i R(a_i,b)}`; if `W_{|A|} = A^{|A|}` then `C ≠ ∅`;
  otherwise take minimal `n ≥ 2` with `W_n ≠ Aⁿ`, observe
  `LeftLinked(W_n) = A²`, view `W_n ≤ A × A^{n-1}` and apply Lemmas 70 + 67 to
  contradict BA-and-center-freeness. (ii) `C` is central by Lemma 69. (iii) `C`
  is BA: else Lemma 66 (n=2) supplies `S ≤ B×B`; the pp-defined
  `W = {(a₁,…,a_{|A|}) : ∃(b,c) ∈ S, c ∈ C, ∀i R(a_i,b)}` is `<_C A^{|A|}` by
  Lemma 62, and Lemma 67 yields a center on A.
* **Lemma 73/Cor 74** give "pull back along a surjection" for all six types; the
  D/L/PC case is by the observation `A'/σ = A/f⁻¹(σ)`, `B'/σ ≅ B/f⁻¹(σ)`.

### 5.3 Intersection property (L347–1020) — the heart of the section

Goal (stated in the introduction to the subsection): *if `C ⋘ A` and δ is a
dividing congruence for `B ⋘ A`, then `(B∩C)/δ` is empty, a singleton, or all of
`B/δ`.* This trichotomy is what makes the whole subuniverse calculus work.

* **Lemma 75 → 76** are the "totally symmetric relation" lemmas. 76 is the
  dichotomy used to launch both big inductions: for a reflexive totally
  symmetric shift-closed `R ≤ (A/σ)ⁿ`, either `R` is the diagonal or it swallows
  `(B/σ)ⁿ`. Proof of 76: if `pr₁,₂(R)` is equality, symmetry forces `R` diagonal;
  else irreducibility of σ forces `pr₁,₂(R) ⊇ σ*/σ ⊇ (B/σ)²` and Lemma 75 applies
  to `R ∩ (B/σ)ⁿ`.
* **Lemma 77** (`LEMSelfIntersectionPC`, 141 L). "Self-intersection": how a
  single chain `B_k ⋘ A` interacts with an arbitrary congruence δ, measured at
  the m-th dividing congruence σ_m. Induction on k. The recurring device: build
  the `|A|`-ary relation
  `S_n = {(a₁/σ_k,…,a_{|A|}/σ_k) : ∀i,j (a_i,a_j) ∈ δ ∩ ⋂_{ℓ<k} σ_ℓ, ∀i a_i ∈ B_n}`,
  take the minimal n at which `(B_{k-1}/σ_k)^{|A|} ⊄ S_n`, and case on the type
  `T_n`: BA/C ⟹ (Lemmas 62+65+67) a BA/central subuniverse on `B_{k-1}/σ_k`,
  contradiction; S ⟹ Lemma 64 keeps the intersection nonempty and yields *both*
  BA and central; D ⟹ build a relation `R ≤ (A/σ_k)^{|A|} × A/σ_n`, use the
  inductive hypothesis to show its last projection is full, then Lemma 69 on the
  resulting central relation.
* **Lemma 78** (`LEMIntersectionPCLinearIsGood`, 209 L). Same machine, now for
  two chains `B ⋘ A`, `C ⋘ A`, by induction on `k + ℓ` (with `k,ℓ` chosen
  minimal). Part (s) (BA/C subuniverses of B meet C) is proved first and is used
  inside part (d). Part (d) runs the `S_{m,n}` double family with subcases 2A
  (walk down the B-chain), 2B (walk down the C-chain), 2C (done). Subsubcase 2A3
  is where Lemma 77 is invoked.
* **Cor 79** transports (d) to a subdirect binary relation via `f_i⁻¹`
  (Lemma 73). **Cor 80** is a "parallelogram property for D-type reductions": if
  three of the four intersections `C_i ∩ C_j'` are nonempty, so is the fourth.
  Proof splits on whether `(B₁∩B₂)/σ_i` is a singleton, and otherwise studies
  `S = {(a/σ₁, a/σ₂) : a ∈ B₁∩B₂} ≤_sd (B₁/σ₁)×(B₂/σ₂)` — either S is full
  (Lemma 69) or S is a bijection.

### 5.4 Properties of PC or Linear congruences (L1022–1735)

The only subsection with genuinely *algebraic* (as opposed to combinatorial)
content: Abelian ⟹ affine ⟹ module, hence `Z_p^n`.

* **82** turns the Hobby–McKenzie characterisation of Abelian (81) into the
  bridge language: `A` Abelian ⟺ ∃ bridge `0_A → 0_A` with all three projections
  full. Backward direction: "compose the bridge with itself sufficiently many
  times to obtain a reflexive symmetric transitive relation on `A²`".
* **84**: a symmetric bridge σ→σ with full projections gives
  `(A/σ; δ/σ) ≅ (G; x₁−x₂=x₃−x₄)` for an abelian group G. Uses: 82+83 ⟹ `A/σ`
  affine ⟹ polynomially equivalent to an **R**-module; congruences of modules
  come from submodules; the diagonal is a block ⟹ the submodule is `{x = y}`;
  then `δ = δ_0` because `δ/σ` is preserved by `x−y+z` and `pr₁,₂(δ) = A²`.
* **85**: the "block of a good bridge is BA-and-center-free" lemma, by induction
  on `|A|`. Symmetrises the bridge first, then assumes `B <_T A` and picks
  `(a,b) ∈ ω ∩ ((A∖B)×B)`; Case 1 (a proper subalgebra contains a,b) recurses;
  Case 2 (`{a} ∘ ω = A`) builds `ξ(x₁,x₂) = σ(a,x₁,x₂,b)`, `C = B ∘ ξ`, and
  produces `∅ ≠ C' <_T C <_T A` to recurse on.
* **86**: from a bridge σ→σ with `δ̃ ⊋ σ` derive that `σ*` is a congruence, its
  blocks are BA-and-center-free, and (for symmetric δ) each block carries a
  `Z_p^{n_B}` structure with **one common prime p**. The prime-uniformity step
  pp-defines `p₁·x₁ = p₁·x₂` from `x₁−x₂ = x₃−x₄` and contradicts irreducibility.
* **Lemma 7** (`LEMLinearEquivalentConditions`) is then two lines: `1 ⟹ 2` from
  the definition; `2 ⟹ 1` by symmetrising δ and applying 86.
* **87**: the inductive engine for **Lemma 9**. Under three technical conditions
  on a reflexive bridge δ, produce `a ≠ b` with `(a,a,b,b) ∈ δ`. Case 1 restricts
  to a nontrivial BA/central `B` (using Lemma 68 to preserve linkedness); Case 2
  handles a singleton BA/central `{a}` by an explicit 3-tuple computation with a
  ternary absorbing operation; Case 3 (BA-and-center-free) uses Lemma 72 + Lemma
  71 to find `(a,a) ∈ C`.
* **Lemma 9** (`LEMPCBridgesAreTrivial`): builds `ξ(x₁,x₂,x₅,x₆) = ∃x₃x₄
  δ(x₁,x₂,x₃,x₄) ∧ δ(x₅,x₆,x₃,x₄)` and splits on
  `RightLinked(pr₁,₂,₃(ξ))` / `RightLinked(pr₁,₂,₄(ξ))` being σ or ⊇ σ*.
  In Case 1 it constructs two candidate bridges ζ₁, ζ₂ and shows one of them
  forces `pr₁,₃(δ) = σ` or `pr₁,₄(δ) = σ`. In Cases 2/3 it applies 87 to `ξ ∩ B⁴`.
* **Lemma 8** (`LEMNoBridgeBetweenDifferentTypes`): a chain of bridge
  constructions (δ′, δ″ ⟹ ω with `pr₁,₃(ω) = ω̃ = δ̃`; then ξ₁, ξ₂ trivial by
  Lemma 9 ⟹ ω is "symmetric in its first two coordinates"; then ζ witnesses σ₂
  linear).
* **Lemma 10** (`LEMBridgeTOPCCongruence`) is a corollary of 8 + 9.

### 5.5 Types interaction (L1736–1927) — 2 statements

* **88** builds the canonical bridge from `ω ∩ σ₁ = ω ∩ σ₂`, `ω ∖ σ₁ ≠ ∅`.
  (Cited to [zhuk2020proof, Lem 8.19] but re-proved in 24 lines; the proof is
  complete and easy — a good early formalization target.)
* **89** is the pairwise core of Theorem 21: two subuniverses of chains with
  empty intersection but nonempty "relaxed" intersections must have the same
  type, and in the D case are joined by a bridge. The four cases (`T₁ = S`;
  `T₁,T₂ ∈ {BA,C}`; mixed; `T₁ = T₂ = D`) each reduce to Lemma 78 or Lemma 61.

### 5.6 Factorization of strong subalgebras (L1928–2296) — 5 statements

Goal: `Lemma 94` (factor a PC/L subuniverse by an arbitrary congruence and keep
its type). Path: 90 (push a center into `B₂`) → 91 (left-linkedness survives
restriction to `B₁ × B₂`) → 92 (a congruence either does nothing to `B` mod σ or
is swallowed by σ) → 93 (existence of a dividing congruence above any congruence
with BA-and-center-free quotient) → 94.

Lemma 91's proof is the prettiest argument in the section: define
`R_n = (R ∘ R⁻¹)^n`; either `R₁` already fills `(B₁/σ)²` (then Lemmas 72 + 90
give a center inside `B₂`), or take the **maximal `n = 2^k`** with
`(R_n ∩ B₁²)/σ ≠ (B₁/σ)²` and derive a contradiction from Lemma 69.

### 5.7 Remaining statements from §2.3 (L2297–3143) — 13 restatements + 3 new lemmas

Mostly short assembly proofs on top of 5.2–5.6:

* 13 (Ubiquity) ← 93. 20 (IntersectALL) ← 63 + 78. 14 (Propagation) ← 73 + 94
  (only (fm) needs work: an induction on `t` plus the identity
  `(C₁∩…∩C_t)/δ = C₁/δ ∩ … ∩ C_t/δ`, valid because `(C_i ∘ δ) ∩ B = C_i`).
* 16, 17, 18 are formal consequences of 14 and 20 (18(r) via `f_i⁻¹`).
* 21 (Main Stable Intersection) ← 89 + 8, reducing `n > 2` to `n = 2` by
  absorbing `C₃ ∩ … ∩ C_n` into `B₂`. 22 ← 21 via `f_i⁻¹` plus a translation of
  `σ_k' ∘ σ_ℓ'` back to `σ_k ∘ pr_{k,ℓ}(R) ∘ σ_ℓ`.
* 11 ← §2.4 Lemma 27 [zhuk2020proof Cor 8.17.1] (perfect linear congruence);
  12 ← 22 (`{a_i} <_{PC}^{A/σ} A/σ`, minimal-arity relation argument).
* 95/96/24 (`PreserveLinkdness`) and 97/25 (`MaximalMultExtention`) close the
  section; 97 is a **downward** induction ("on the size of `B₁` starting with
  `B₁ = A`", i.e. the inductive hypothesis is for *larger* `B₁`).

---

## 3. External imports — every result used but not proved in §5

### 3.1 Cited inside §5

| Used as | Source | Statement in the source |
|---|---|---|
| Lemma 61 | **[zhuk2021strong] = Zhuk, "Strong Subalgebras and the CSP", JMVLSC 36 (2021), Lemma 6.25** | possible types of two disjoint strong subuniverses |
| Lemma 62 | **[DecidingAbsorption] = Barto & Kazda, "Deciding absorption", IJAC 26 (2016), Lemma 2.9**; also **[zhuk2021strong] Lemma 6.1 and Theorem 6.9** | pp-definitions preserve BA / central |
| Lemma 65 (T=C) | **[zhuk2021strong] Lemma 6.8** | central subuniverses survive factorization |
| Lemma 66 | **[DecidingAbsorption] Proposition 2.14**; **[zhuk2021strong] Lemma 3.2** | n-ary absorption ⟺ no "essential" witness relation |
| Lemma 67 | **[zhuk2021strong] Lemma 6.24** (BA, C); "repeat word to word" for S | BA/central on a power ⟹ BA/central on the base |
| Lemma 68 | **[barto2012absorbing] = Barto & Kozik, LMCS 8 (2012), Proposition 2.15(i)** | linkedness survives restriction to absorbing subuniverses |
| Lemma 69 | **[zhuk2021strong] Theorem 6.15** | a "center" of a subdirect relation is a central subuniverse unless the other side has a BA subuniverse |
| Lemma 70 | **[ZebsNotes] = Z. Brady, "Notes on CSPs and Polymorphisms", arXiv:2210.07383, Theorem 3.11.1** | proper linked subdirect relation ⟹ BA or center on one side |
| Lemma 71 | **[zhuk2020proof] = Zhuk, JACM 67(5) (2020), Lemma 7.2** | a BA subuniverse of a reflexive binary relation meets the diagonal |
| Lemma 72 | (proved here; noted as derivable from **[ZebsNotes] Lemmas 3.11.2, 3.11.3**) | |
| Lemma 73 (BA, C cases) | **[ZebsNotes] Section 3.15** | preimages of BA/central subuniverses |
| Lemma 81 | **[hobby1988structure] = Hobby & McKenzie, "The Structure of Finite Algebras", AMS 1988** (no number given) | Abelian ⟺ diagonal is a block of a congruence on `A²` |
| Lemma 83 | **[hobby1988structure]** (no number given) | for finite algebras with a WNU term: Abelian ⟺ affine |
| Lemma 88 | **[zhuk2020proof] Lemma 8.19** — but a full 24-line proof is given here anyway | |

### 3.2 Used by §5 but stated elsewhere in the paper (§2 / §2.4)

| Used at | Statement | Provenance |
|---|---|---|
| Lemma 87, Case 2 (implicitly) | `LEMCenterImpliesTernaryAbsorption` (main.tex L1355): a central subuniverse is a ternary absorbing subuniverse | **[zhuk2021strong] Corollary 6.11.1** |
| Lemma 11 (`LEMLInearOnTheTopIsEasy`) | `LEMBuildingPerfectCongruence` (necessaryClaims L14): σ irreducible on `A ∈ V_n`, δ a bridge σ→σ with `δ̃ = A²` ⟹ σ is a perfect linear congruence | **[zhuk2020proof] Corollary 8.17.1** |
| Lemma 8, Lemma 82 (implicitly, "compose the bridge with itself") | `LEMBridgeComposition` (necessaryClaims L23) | **[zhuk2020proof] Lemma 6.3** |
| Cor 17(f), Cor 18(m1), Lemma 25 | **`CORPropagationModuloCongruence` (main.tex L1682, printed as Corollary 15)** | **NEVER PROVED ANYWHERE** — see hazard H1 |

### 3.3 Silent imports (used, never cited)

* **Congruences of modules correspond to submodules** (Lemma 84) — standard, uncited.
* **In an idempotent affine algebra, `x − y + z` is a *term* operation**
  (Lemma 84 uses "δ/σ is preserved by the Maltsev operation `x−y+z`" although
  affineness only gives a *polynomial*). True for idempotent algebras but not
  argued.
* **Pol–Inv Galois correspondence** (Lemma 12): "to show `A/σ` is a PC algebra it
  is sufficient to show that any reflexive `R ≤ (A/σ)^m` is a conjunction of
  equalities". Correct (a relation is preserved by all constants iff it is
  reflexive) but relies on the finite Pol–Inv theorem, uncited.
* **Idempotency**: `{a} ≤ A` for every `a ∈ A` is used repeatedly (Lemma 85
  Case 2, Lemma 87 Case 2, Lemma 12) without comment.

### 3.4 Maróti–McKenzie

The only Maróti–McKenzie import ([miklos], *Existence theorems for weakly
symmetric operations*, Algebra Universalis 59 (2008), Lemma 4.7 — existence of a
special WNU `w' ∈ Clo(w)` of arity `n^{n!}`) is **§2.4 Lemma 26 and is not used
anywhere inside §5**. It reaches §5 only indirectly, via the standing hypothesis
`A ∈ V_n` in Lemma 11.

### 3.5 Internal dependency structure (the DAG, and one cycle)

Reading order that respects dependencies for the bulk of §5:

```
62,63,65,66,67,68,69,70,71 (imports)
  ├─► 64 ─┐
  ├─► 72 ─┼─► 75 ─► 76 ─► 77 ─► 78 ─► 79, 80, 20, 89
  └─► 73 ─► 74                       │
                                     ├─► 90 ─► 91 ─► 92 ─► 93 ─► 13
                                     └─► 94 ─► 14 ─► 16,17,18
81,83 ─► 82 ─► 84 ─► 86 ─► Lemma 7 ─┐
72,71,68 ─────────► 87 ─► Lemma 9 ──┴─► Lemma 8 ─► Lemma 10, 94, 21
78, 89, Lemma 8 ─► 21 ─► 22 ─► 12, 95, 96, 97 ─► 24, 25
```

**The one cycle** (see hazard H2): `Lemma 9 ⇒ Lemma 7 ⇒ 86 ⇒ 85 ⇒ Corollary 22
⇒ Theorem 21 ⇒ Lemma 8 ⇒ Lemma 9`.

Also note the **non-topological presentation**: Lemma 64 (L114) uses Lemma 65
(L138); Lemma 85 (L1144, §5.4) uses Corollary 22 (L2660, §5.7); Lemma 92 (L2086)
uses Lemma 77 (L419) with an *extended* chain.

---

## 4. The five hardest proofs

Ranked by a combination of length, case-tree depth, number of ad-hoc
constructions, and how much is left to the reader.

### H-1. Lemma 78 = `LEMIntersectionPCLinearIsGood` (209 L, L644–936)

The load-bearing theorem of the whole subuniverse calculus (everything in
5.5–5.7 goes through it). Difficulty:

* Simultaneous induction on `k + ℓ` over **two** ⋘-chains, with `k, ℓ` "chosen
  minimal", and with sub-invocations that use the statement **symmetrically**
  (swapping the roles of `B` and `C`) and with **different δ** (`ω_n` instead of
  the given δ). The statement must be formalized with δ universally quantified
  over dividing congruences *of either chain* for the induction to close.
* Two conclusions ((s) and (d)) proved in one induction, with (d) invoking (s)
  and (s) invoking (d) at smaller `k + ℓ`.
* Ten distinct case branches, three of which build a fresh `|A|`-ary or
  `(|A|+1)`-ary relation and then apply Lemma 69 or Lemma 67.
* The `|A|`-ary width is essential (you need `|A|` coordinates to force a
  singleton class), and the relations are defined by set-builder expressions
  whose subalgebra-hood is never checked.

### H-2. Lemma 77 = `LEMSelfIntersectionPC` (141 L, L419–611)

Same machinery as H-1 but with one chain; it is the base on which H-1's subcase
2A3 rests. Extra difficulties: the statement mixes indices `k` (chain length) and
`m` (position of the D-step) and quantifies over σ_ℓ for `ℓ < m` that may be the
*full* congruence `A²` by convention. Subcase 1B contains a visible typo
(`B_{k-1}/σ_{k-1}` for `B_{k-1}/σ_k`, L481). The inductive hypothesis is invoked
in subsubcase 1B3 on a **different m** than the one being proved.

### H-3. Lemma 9 = `LEMPCBridgesAreTrivial` (89 L, L1460–1561)

Pure bridge combinatorics, with three explicitly constructed pp-relations
(ξ, ζ₁, ζ₂), each of which must be checked to be a bridge (four conditions
each). The case split is on the values of `RightLinked(pr₁,₂,₃(ξ))` and
`RightLinked(pr₁,₂,₄(ξ))` — which requires knowing these are congruences
comparable with σ and σ*. Subcases 1A/1B chase "the first two coordinates of δ
determine the last two up to σ" through several instantiations. The step
"`\tilde ζ_1` must be equal to σ" is an unstated appeal to Lemma 7, which is the
source of the dependency cycle.

### H-4. Lemma 8 = `LEMNoBridgeBetweenDifferentTypes` (92 L, L1573–1677)

Five constructed relations (δ′, δ″, ω, ξ₁, ξ₂, ζ), a "without loss of generality
δ̃ is rectangular as otherwise we can compose it with itself many times", and a
sequence of increasingly implicit bridge verifications. The final construction

```
ζ(x₁,x₂,x₃,x₄) = ∃y₁y₂y₃ ω(y₁,y₂,x₁,x₂) ∧ ω(y₁,y₃,x₁,x₃) ∧ ω(y₂,y₃,x₁,x₄)
```

together with "`ζ(x₁,x₂,x₃,x₄) ∧ ζ(x₃,x₄,x₁,x₂)` defines a bridge witnessing that
σ₂ is linear" is asserted with only two witness computations given.

### H-5. Lemma 85 = `LEMBlockOfGoodBridgeDoesNotHaveBAC` (89 L, L1151–1245)

Induction on `|A|` with two nested case splits, a symmetrised bridge whose
defining formula as printed is **wrong** (hazard H3), a "maximal subuniverse E of
D such that `ω ∩ E²` is linked and `a,b ∈ E`" whose existence/uniqueness is not
argued, and a final recursion ("applying the inductive assumption to `σ ∩ C⁴` and
using the fact that `{a} ∘ ω = A`, we get a contradiction") that compresses
several verifications into one sentence. It is also the site of the dependency
cycle (it calls Corollary 22).

*Runners-up*: Lemma 86 (the `Z_p` uniformity argument via pp-defining
`p₁x₁ = p₁x₂`), Lemma 95 (`LEMPreserveLinkdnessOneStepAUX` — a WLOG-heavy
argument with a step, "Since `ξ ⊇ δ₁`, `C₁' ∩ F₁ = C₁' ∩ E₁`", that I could not
reconstruct), and Lemma 91.

---

## 5. Which proofs use the WNU `w` essentially, and which are pure universal algebra

**Direct, essential use of a WNU/Taylor/`V_n` hypothesis — exactly two places:**

1. **Lemma 83 → Lemma 84 → Lemma 86 → Lemma 7** (§5.4). Lemma 83
   (`LEMAbelianEqualAffineForWNU`) is the *only* statement in §5 whose hypothesis
   mentions a WNU term; it converts Abelian into affine, which is what produces
   the `Z_p^{n}` structure in the definition of a linear congruence. Without a
   Taylor/WNU term this chain is false (Abelian ≠ affine in general). Everything
   about linear congruences ultimately rests on it.
2. **Lemma 11 = `LEMLInearOnTheTopIsEasy`** (§5.7). Explicitly assumes
   `A ∈ V_n` (finite algebra whose single basic operation is an idempotent
   *special* WNU of arity `n`) and imports §2.4 Lemma 27 = [zhuk2020proof
   Cor 8.17.1], whose proof in the JACM paper does use `w` concretely. The target
   `Z_p` is itself an algebra of `V_n` (`w = x₁ + … + x_n mod p`), so the
   arity `n` matters: `Z_p ∈ V_n` requires `n ≡ 1 (mod p)` for idempotency, a
   constraint handled in §2 of main.tex, not here.

**Uses `w` only through idempotency / absorption terms** (i.e. needs *some* term
operations but not the WNU identities):

* Lemma 85 Case 2 and Lemma 87 Case 2 apply a **binary or ternary absorbing
  operation** to explicit tuples. Lemma 87 Case 2 needs a *ternary* absorbing
  operation for a singleton central subuniverse, i.e. it silently invokes
  [zhuk2021strong Cor 6.11.1] (central ⟹ ternary absorbing).
* Idempotency (`{a} ≤ A`, `t(a,a) = a`) is used in Lemmas 85, 87, 12.

**Everything else is pure universal algebra over "finite idempotent algebra with
a WNU term operation"**, in the sense that `w` never appears: 5.2 (all), 5.3
(all — Lemmas 75–80 are pure relational combinatorics + the imports), 5.5, 5.6,
and all of 5.7 except Lemma 11. In these proofs the algebraic input enters
*only* through the black boxes 61, 62, 66, 67, 68, 69, 70, 71 — each of which
does need Taylor/WNU in its own (external) proof.

**Consequence for the formalization route**: §5.2's imports are the *entire*
algebraic interface. If Lemmas 61–71 are taken as axioms/interfaces, then §5.3,
§5.5, §5.6 and most of §5.7 become theory-free combinatorics about a lattice of
subsets and congruences — attractive for an early Lean milestone. §5.4 is the
part that cannot be decoupled from real algebra.

---

## 6. Formalization hazards

Ordered by how likely they are to break a Lean development.

### H1 (blocker). `CORPropagationModuloCongruence` (printed **Corollary 15**) is stated in §2.3 and never proved

§5.7 is titled "Proof of the remaining statements from Section 2.3" and restates
Lemmas 11, 12, 13, 14, 20, 21, 23, 24, 25 and Corollaries 16, 17, 18, 22 — but
**not Corollary 15**, which is nevertheless *used* three times inside §5
(L2506 (f), L2514 (t), L2588 (m), L3110 (m)). It is presumably meant to be
Lemma 14 (`LEMPropagation`) applied to the canonical surjection `A ↠ A/δ`
((f)=(f), (t)=(ft), (s)=(fs), (m)=(fm)), but that is never said, and the (m)
item carries the extra hypothesis "`B/δ` is S-free" which must be matched
against (fm)'s "`f(B)` is S-free". A blueprint must add this as an explicit
lemma.

### H2 (blocker). A genuine circular dependency around Lemma 85 / Corollary 22

```
Lemma 9  (PC bridges are trivial, L1508: "Since ζ̃₁ must be equal to σ")
   ⇒ Lemma 7  (linear ⟺ nontrivial reflexive bridge)      [implicit citation]
   ⇒ Lemma 86 (nontrivial reflexive bridge implies …)
   ⇒ Lemma 85 (block of a good bridge is BA-and-center-free)
   ⇒ Corollary 22 (L1214: "If T = C then by Corollary 22 we have …")
   ⇒ Theorem 21
   ⇒ Lemma 8  (no bridge between different types)
   ⇒ Lemma 9.
```

The single edge that closes the cycle is Lemma 85's use of Corollary 22 to
conclude, from three nonempty triple-intersections, that a fourth is nonempty —
i.e. the `n = 3`, all-types-`C` instance of Corollary 22. The intended fix is
almost certainly to replace it by "a central subuniverse is ternary absorbing"
([zhuk2021strong Cor 6.11.1]) plus Lemma 66 with `n = 3`; but Lemma 66 is stated
for a *single* absorbing subuniverse while three *different* central
subuniverses of the same algebra appear here, so a "mixed" essentiality lemma is
needed. **Any blueprint must break this cycle explicitly and prove the mixed
lemma.** Note this is entangled with H3 below.

### H3 (blocker). Theorem 21 case (c) — the claim `n = 2` for type `C` is never proved

The proof of `THMMainStableIntersection` reduces to `n = 2` (via Lemma 89) and
then establishes only **pairwise** conclusions: "Thus, we proved the required
conditions for `T₁(σ₁)` and `T₂(σ₂)`. Similarly, we can prove this for any
`T_i(σ_i)` and `T_j(σ_j)`." That yields `T₁ = … = T_n` and, for PC, the extra
argument `σ₁ = σ₂` which does force `n = 2`. **For type `C` nothing forces
`n = 2`**, yet the statement's case (c) asserts it. The missing ingredient is
again the ternary-absorption essentiality of central subuniverses. Since
Corollary 22's case (c) is what Lemma 85 consumes, H2 and H3 are the same gap
seen from two sides.

### H4. Typo that inverts a definition: the symmetrised bridge in Lemma 85

L1154–1157 prints

```
σ(x₁,x₂,x₃,x₄) = ∃x₅ ∃x₆  δ(x₁,x₂,x₅,x₅) ∧ δ(x₃,x₄,x₅,x₆).
```

With `δ` a bridge from `0_A` to `0_A`, `δ(x₁,x₂,x₅,x₅)` forces `x₁ = x₂`, so
`pr₁,₂(σ) = 0_A` and σ is **not** a bridge — the proof would collapse
immediately. The intended formula is certainly
`∃x₅ ∃x₆ δ(x₁,x₂,x₅,x₆) ∧ δ(x₃,x₄,x₅,x₆)` (which is symmetric, as claimed one
line later). Everything downstream in Lemma 85 and hence Lemma 86 and Lemma 7
depends on getting this right.

### H5. Notational left/right swaps when applying Lemmas 69 and 72

Lemma 69's "center" `C` lives on the **left** (`C ⊆ A`); Lemma 72's `C` lives on
the **right** (`C ⊆ B`). Both are applied to the *opposite* side several times
(Lemma 72's own proof applies Lemma 69 to `R⁻¹`; Lemma 87 Case 3 applies Lemma 72
to `pr₁,₂,₃(δ)⁻¹` with left algebra `A` and right algebra `pr₁,₂(δ) ≤ A²`). Read
naively, Lemma 87 Case 3 appears to require `pr₁,₂(δ) ≤ A²` to be
BA-and-center-free, which is *not* a hypothesis; the swap resolves it, but a
formalization that gets the orientation wrong will chase a phantom gap. Same
issue in Lemma 91 (Case 1 applies Lemma 72 to `S = {(a/σ, b)}`).

### H6. Under-specified "minimal/maximal object" choices

* Lemma 64: "Consider a **minimal** `C''` such that `C ⋘^A C' <_{T(σ)}^A C'' ⋘^A B`
  and `C'' ∩ D ≠ ∅`" — `C'`, `T`, `σ` are free; what is minimised is not said.
  (Intended: walk down a fixed witnessing chain to the first link that misses `D`.)
* Lemma 85 Case 1: "Let `E` be the **maximal** subuniverse of `D` such that
  `ω ∩ E²` is linked and `a,b ∈ E`" — the family is not closed under joins
  (a union of subuniverses is not a subuniverse, and linkedness need not survive
  generation), so maximality does not obviously give a *maximum*; the proof then
  uses `E` as if it were canonical.
* Lemma 90: "Consider a **minimal** `B₂'` such that
  `B₂ ⋘^{A₂} B₂'' <_{T(δ)}^{A₂} B₂' ⋘ A₂` and `c` can be chosen from `B₂'`" —
  same pattern, with `B₂''`, `T`, `δ` existentially bound inside the minimality
  condition.
* Lemma 95: "without loss of generality (we can switch 1 and 2 if it is not
  true) there are `B₁ ⋘ F₁ <_{T(ξ)} E₁ ⋘ A₁` and `B₂ ⋘ E₂ ⋘ A₂` such that …" —
  the existence of the "first failing link" needs an explicit chain-walk lemma.

**Recommendation**: a blueprint should introduce a reusable "first failing link
along a ⋘-chain" lemma once and use it in all four places, rather than repeating
the informal minimality.

### H7. Convention `σ = A²` for types BA/C/S is load-bearing but invisible

Lemmas 77, 78, 89, 92 intersect `σ_1 ∩ … ∩ σ_k` over a chain whose steps may be
of type BA/C/S, and the intended meaning (main.tex L1534) is that those σ_i are
the **full** relation `A²` and therefore contribute nothing. In
`StrongSubalgebras.tex` the paragraph recording this convention inside the proof
of Lemma 77 is **commented out** (L439–442). In Lean this should be a genuine
`Option`/dependent field, not a defaulted congruence, or the definition of ⋘
should carry the congruence only for D-steps.

### H8. Missing properness checks

Repeatedly, `X <_T Y` (strict) is concluded where only `X ≤_T Y` is established:

* Lemma 64: `(C'' ∩ D)/σ <_{BA} C''/σ` needs `(C'' ∩ D)/σ ≠ C''/σ`, which holds
  because `C' ∩ D = ∅` — not stated.
* Lemma 72 step (iii): `W < A^{|A|}` needs `S ∩ (C×C) = ∅` — not stated.
* Theorem 21: `C₂' = C₂ ∩ B₂'` is used as a *strict* subuniverse of `B₂'`;
  strictness follows from `⋂C_i = ∅` — not stated.
* Lemma 93: `(S_i ∩ B²)/σ ⪇ (B/σ)²` follows from `S_i` being stable under
  `δ ⊇ σ` — not stated.

### H9. Omitted routine verifications that are not routine in Lean

* Every set-builder relation (`S₀`, `S_n`, `S_{m,n}`, `R`, `R'`, `W`, `W_n`, `S`,
  `S'`, `S''`, ξ, ζ₁, ζ₂, δ′, δ″) is asserted to be a subalgebra; each needs a
  proof (usually: pp-definable / homomorphic image / intersection).
* Lemma 75 needs `(a,…,a,c), (a,…,a,a) ∈ R` from `pr₁,ₙ(R) = A²`: this requires
  applying the shift-closure `n−2` times *after* a permutation — a small induction.
* Lemma 76's final step ("apply Lemma 75 to `R ∩ (B/σ)ⁿ`") needs
  `pr₁,₂(R ∩ (B/σ)ⁿ) = (B/σ)²`, which again requires the shift-closure induction,
  not just `pr₁,₂(R) ⊇ (B/σ)²`.
* Lemma 72 step (i) needs `LeftLinked(W_n) ⊇ LeftLinked(R)`, asserted in one clause.
* Lemma 82 (⇐) and Lemma 8 both say "compose the relation with itself
  sufficiently many times"; the required number and the invariance of the bridge
  conditions under composition come from §2.4 Lemma 28 [zhuk2020proof Lem 6.3],
  which is only stated for **irreducible** congruences — in Lemma 82 the
  congruence is `0_A`, fine, but in Lemma 8's first move the composition is of
  `δ̃` with itself to force rectangularity, which is a different operation.

### H10. Local typos and notation abuses (each is a trap, none is fatal)

| Where | Issue |
|---|---|
| L481 | `(E ∩ B_{k-1})/σ_k = B_{k-1}/σ_{k-1}` — should be `B_{k-1}/σ_k` |
| L312 | Lemma 73, T=S case: "there exists `D' ≤ C`" — should be `D' ≤ C'` |
| L317 | Lemma 73's proof says "Suppose `T ∈ {PC, L}`" but the statement quantifies `T ∈ {BA,C,S,L,D}`; `D` is never treated (it is the union of the L and PC cases, but that is not said) |
| L335 | Cor 74 writes `<_{T(σ)}^R` with the *same* σ on both sides; the congruence on `R` is really `f₁⁻¹(σ)` |
| L1214–1219 | Lemma 85: the three premises fed to Corollary 22 are asserted without derivation |
| L1297 | Lemma 86: "each Abelian group `G_p`" — should be `G_B` |
| L1415 | Lemma 87 Case 2 says "because `pr₁,₃(δ)` is linked", but hypothesis (3) is `RightLinked(pr₁,₂,₃(δ)) = A²` — a different statement |
| L1443 | Lemma 87 Case 3: `C ≤_{BA} pr₁,₂(δ)` — Lemma 72 gives `≤_{BA,C}`; only BA is used |
| L2224 | Lemma 93: "BA or central subuniverse on `B/δ`" — should be `B/σ` |
| L2823 | Lemma 95: "`B_i ⋘ A₁`" — should be `⋘ A_i` |
| main.tex L2503 | Section 3 cites "Corollary 18**(rm)**" — no such item exists (items are r, r1, b, b1, m, m1) |
| L1953 vs L2018 | Cor 79 is stated for a *binary* subdirect `R`; Lemma 90 applies it where an `n`-ary version would be natural. The commented-out `LEMIntersectionPCLinearIsGoodForRelations` (L1944) was the n-ary version and was deleted; check every use of Cor 79 really is binary |

### H11. Statement-level ambiguities worth resolving before formalizing

* **Lemma 78(d)** "the dividing congruences from the definition of `B ⋘ A` and
  `C ⋘ A`" — depends on the *chosen chains*, which are only pinned down by
  "where `k` and `ℓ` were chosen minimal". Since minimal-length chains need not
  be unique, the conclusion `δ ⊇ δ₁ ∩ … ∩ δ_s` is chain-dependent as written. The
  same issue recurs in Lemma 92 ("ω is the intersection of all the dividing
  congruences coming from `B ⋘ A`") and Lemma 89. Formalizing ⋘ as an inductive
  relation *carrying* its chain (rather than as a `Prop`) is probably necessary.
* **Lemma 97 / Lemma 25** quantify over "**all** congruences of type `T` on
  **A** such that `ω_i* ⊇ B₁²`" — this is a set defined by a property of the
  ambient algebra, and Lemma 25's statement drops the "all" (main.tex L1898
  vs. StrongSubalgebras L3102 both say "congruences", the §5 statement having
  had "all" struck out). The two readings are not equivalent; Lemma 25's proof
  produces a specific finite family, so "some congruences" is the correct
  reading there and "all" the correct reading in Lemma 97.
* **Lemma 12**'s proof asserts `{a_i} <_{PC}^{A/σ} A/σ`, which by the definition
  of `<_D` requires `A/σ` to be **BA-and-center-free**. That is not part of
  "σ is a PC congruence with `σ* = A²`". Either an extra hypothesis is missing
  or an argument (a BA/central subuniverse of `A/σ` contradicts something) is
  omitted. Also "consider a relation `R` of the minimal arity that is not like
  this; then projection of `R` onto any subset of coordinates gives a full
  relation" needs the elimination of coordinates that are forced equal.
* **Lemma 11**'s last step ("`ξ(x,z) = ζ(x,a,z)` is a bijective relation") uses
  more of the perfect-linear-congruence structure than is stated; only
  `(a₁,a₂) ∈ σ ⟺ b = 0` is available, which gives injectivity of `ξ` modulo σ
  but not surjectivity/functionality without extra work.
* **Lemma 14(fm)** silently uses the S-freeness hypothesis to discard the
  `C_i/δ <_S B/δ` alternative of Lemma 94; worth making explicit since (fm) is
  heavily used in §3.

### H12. Dead code in the source

~700 of 3144 lines are commented out, including four lemma statements
(`LEMBACenterSImpliesUniversal`, `LEMLinearIsBACenterFree`,
`LEMReflexiveRestrictedToBForPC`, `LEMIntersectionPCLinearIsGoodForRelations`,
`LEMConOneIsPcOrLinear`, `LEMMultiplyBySmallCongruence`,
`LEMMinimalContainingIsMinimal`) and a long alternative proof of Lemma 96 with a
matrix argument. Several *live* proofs contain commented-out justifications that
were the original reasons for a step (e.g. Lemma 78 subsubcase 2A3's appeal to
`LEMLinearIsBACenterFree`, now deleted). When a step looks unjustified, the
commented-out text is often the missing explanation — but it refers to lemmas
that no longer exist, so it cannot simply be reinstated.

---

## 7. Bottom-line assessment for the blueprint

* §5.2 is a thin wrapper over ~10 external results. Formalizing it means
  formalizing (or axiomatizing) Barto–Kazda, Barto–Kozik, Brady's notes, and
  four lemmas of Zhuk's JMVLSC paper. **This is the real cost centre of the
  route**, and none of it is in Mathlib.
* §5.3 (Lemmas 75–80) is self-contained modulo §5.2 and is where the intellectual
  content of "strong subalgebras" lives. Two proofs (H-1, H-2) will dominate the
  Lean line count of the section; budget them like a mid-size Mathlib file each.
* §5.4 is the only genuinely algebraic part (Abelian/affine/module) and is the
  one place where Mathlib actually helps (modules, abelian groups, `ZMod p`).
* §5.5–§5.7 are assembly; they are short in prose but they are exactly where the
  quantifier structure over chains (H11) bites.
* Three items must be repaired before any faithful formalization: **H1** (a
  missing corollary), **H2/H3** (a circular dependency that coincides with a real
  gap in Theorem 21(c)), and **H4** (a formula typo that would make Lemma 85
  vacuous).
