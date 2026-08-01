# Architecture decision: formalizing the CSP Dichotomy Theorem in Lean 4 / Mathlib

**Status:** decided. Synthesis of survey reports 01–12.
**Date:** 2026-07-31.
**Supersedes:** nothing. This document is the input to the blueprint drafting phase.

---

## 0. The decision in one page

| Question | Decision |
|---|---|
| **Spine** | Zhuk arXiv:2404.01080v2, §§1–3 + §5. Cut §4 (XY-symmetric) entirely. |
| **Proof source for imports** | Brady `csp.tex` for the Absorption Theorem and abelian⟹affine; Zhuk 2005.00593 §6.1–6.2 for the pp-propagation lemmas; Zhuk 1704 §6/§8 for bridge composition; Zhuk 1704 §4 for the algorithm's control flow. |
| **Existing base** | `zhuk-lean` (1,591 lines, sorry-free) lifted verbatim as modules 1–6 of the new repo. It discharges three of 2404's black-box imports outright. |
| **Substrate** | `Mathlib.ModelTheory` (`FirstOrder.Language` / `Structure` / `Substructure`), `L` kept generic, `[L.IsAlgebraic]`, `𝒱ₙ` as a thin `class` on top. |
| **Never build** | P, NP, NP-completeness, Cook–Levin, `TM2ComputableInPolyTime.comp`, cyclic terms, free algebras in a variety, Tame Congruence Theory, pp-interpretability/pp-powers/minions. |
| **Never take from the paper as written** | Corollary 15 (unproved anywhere), Lemma 19 (false as printed), Theorem 21(c) (unproved), the §5 citation cycle, Theorem 44's `S`-free hypothesis, `SolveLinear`'s "remove constraints", 1704's `FindEquationsNonlinked` `I := {1}`. See §7. |
| **Target** | **L0** algebraic core (three theorems + the paper's missing Informal Claim 1); **L1** algorithm correctness as a proposition; **L2** a step-count bound in an explicitly defined unit-cost model plus a seed-relative hardness corollary. `CSP(Γ) ∈ P` is **not** a target. |
| **Best defensible terminal milestone** | **M2 — the Ubiquity theorem** ("every `B ⋘ A` with `\|B\| > 1` has a proper subuniverse of type BA, central, linear, or PC"). ≈ 17–19k Lean lines, no CSP-instance machinery, quotable as a standalone universal-algebra theorem. |
| **Immediate next milestone** | **M1 — the classical prerequisite layer**: Barto–Kozik Absorption Theorem, Loop Lemma, abelian Taylor ⟹ affine. ≈ 9–11k lines. Four named theorems that no proof assistant currently has, each independently citable. |
| **Size, L0+L1+L2** | 33,000–37,000 new Lean lines; 420–470 blueprint pages across five volumes; 33–38 person-months at conventional rates. |

---

## 1. WHICH ROUTE

### 1.1 The spine: Zhuk 2404 §§2–3 + §5

Zhuk 2404 is the spine, for one decisive reason and three supporting ones.

**Decisive.** Zhuk himself rewrote 1704 because of its "very complicated induction"
(`main.tex:450–464`): in 1704 the linear subalgebras exist only *locally* and the proof
oscillates between local and global. 2404's headline change is that the congruence `σ` in a
D/L/PC-type reduction lives on the **top** algebra `A`, not on `B`. That single change deletes
the local↔global oscillation. An induction that the author replaced because it was too
complicated for a human is the worst possible formalization target.

**Supporting.** (i) 2404 is unusually rigorous prose: over 8,998 lines the hedge audit is
`obvious` 3, `clearly` 0, `easy to see` 0, `similarly` 13, `word to word` 1 — roughly one sixth
the hedge density of Brady's notes per line, and half that of 1704. (ii) Its `LEMUbiquity`
derives the existence of a strong subuniverse from the Absorption Theorem rather than from
Zhuk 2021's Rosenberg-style five-types theorem, which removes ~15 printed pages
(2005.00593 §6.3–§6.8: projective subuniverses, PC subuniverses, full-projective relations,
Lemmas 6.26–6.33) from the tractable half. (iii) Its notion of *center* is internal and hence
decidable, whereas 1704's quantifies over all finite algebras `B` with a special WNU.

**But 2404 is not self-contained.** It states 16 numbered results as black boxes and proves 2
more only in some cases. That is the real cost, and it is why the route is a hybrid.

### 1.2 Cut Section 4 (XY-symmetric operations). Decided: out of scope.

Verified mechanically in both directions on the label graph: `XYSymmetric.tex` defines 22–23
labels, **none** referenced from `main.tex` §2/§3, `StrongSubalgebras.tex` or
`necessaryClaims.tex` except in the introduction and `\newtheorem*` boilerplate; conversely §4
issues zero references into §3. `\input{XYSymmetric}` sits at `main.tex:4123`, after everything.
Deleting it leaves the dichotomy proof intact: 1,640 lines and 20 statements removed at zero cost.

Cutting it also **dissolves the worst gap in the whole survey**. Report 06's gap G1 — the
special-WNU lemma's arity `n^{n!}` with `n` unbound in the statement, where the period of
`g_x(y) = w(x,…,x,y)` need not divide `n^{n!}` (take `n = 3` and a 5-cycle) — matters only because
§4 threads `N = n^{n!}` through every construction and needs the arity to be a power of `n`
(`XYSymmetric.tex:411–418`). With §4 cut, we need only *some* arity, and the special-WNU lemma
can be stated and proved in the form we can actually prove:

> There exist `N` and a special idempotent WNU `w' ∈ Clo(w)` of arity `N`.

Report 05's counter-argument (§4's *statement* is trivially Lean-expressible — no algorithms, no
complexity — so it is a better early quotable artifact) is noted and rejected: the milestone
ladder in §6 already contains two better standalone artifacts (the Absorption Theorem at M1, the
Ubiquity theorem at M2), both of which are on the critical path rather than beside it. If the
main line stalls and a showcase is needed, `XYSymmetric.tex:865–1639` (§4.4, which imports
*nothing* from §2 or §5) is the parallel fallback — but budget 2× its page count, since three of
the four worst defects in §4 live in those six pages.

### 1.3 Per-component source table

| Component | Source | Why this source |
|---|---|---|
| Strong subuniverse types, `⋘`, propagation, the intersection theorem | **Zhuk 2404 §2 + §5** | The `σ`-on-the-top formulation; nothing else has it. |
| CSP instances, coverings, crucial instances, the main induction | **Zhuk 2404 §3** | Only complete modern write-up. |
| `zhuk_center` (= 2005.00593 Thm 6.15, 8 uses in 2404) | **`zhuk-lean`** | Already sorry-free. |
| Ternary absorption from centrality (Cor 6.11.1) | **`zhuk-lean`** | Already sorry-free. |
| Relational description of absorption (Barto–Kazda Prop 2.14) | **`zhuk-lean`** | Already sorry-free. |
| **Absorption Theorem** `LEMLinkedImpliesBACenter` (5 uses) | **Brady `csp.tex:10443–10669`** | Brady derives Barto–Kozik's theorem from Zhuk's centre theorem (`csp.tex:10471` literally applies `\ref{zhuk-center}`) in two short lemmas plus a three-line main argument. This is the single most valuable finding in the survey: the hardest classical prerequisite in the area becomes a 600–1,000-line corollary of what is already proved, not a 5,000-line Ramsey argument. |
| **Abelian ⟹ affine for WNU** (cited to Hobby–McKenzie) | **Brady `csp.tex:10670–10854` + `csp.tex:4235–4706`** | Three steps following Barto–Kozik–Stanovský; routes around Tame Congruence Theory entirely. Hobby–McKenzie is not on disk and TCT has no formalization anywhere. |
| `LEMBuildingPerfectCongruence` (JACM Cor 8.17.1) | **Replaced.** Derive from 2404's own `LemBridgeEquivalentToAbelianness` + `LEMNiceBridgeGivesAbelianGroup` + abelian⟹affine | The JACM proof bottoms out in Zhuk's *Key relations* paper (JACM ref [62]), which we do not have. Zhuk's own remark (`1704.01914:2561–2566`) says the commutator route works. This trades an unavailable paper for a large import we need anyway. |
| pp-propagation of BA/central (`LEMBACenterSImplyPPDefinition`, 11 uses) | **Barto–Kazda Lem 2.9 + Zhuk 2005.00593 Lem 6.1 / Thm 6.9**, with `zhuk-lean/Central.lean` covering the hard central half | The BA half is 10 source lines; the central half overlaps what we have. |
| Bridge composition, `LEMAbsorbingEquality` | **Zhuk 1704 Lem 6.3, Lem 7.2** | 12 and 18 source lines; elementary. |
| Tree coverings (5 uses), expanded-covering consistency | **Zhuk 2005.00593 Lem 5.6; Zhuk 1704 Lem 6.1** | No alternative. Note Lem 5.6 is an iterative procedure whose well-founded recursion costs far more than its 26 lines suggest. |
| Special WNU | **Restated and proved locally** (see §1.2) | Maróti–McKenzie Lem 4.7 is not on disk and its published arity is suspect. |
| **Algorithm control flow** | **Zhuk 1704 §4** (with four simplifications and two bug repairs) | 2404's two `algorithm` environments are a self-declared sketch (`main.tex:593`) and contain two defects: `SolveLinear` *removes* constraints where `THMCodimensionOneTheorem`(7) requires *weakening*, and primitive (p2) returns a union of affine subspaces which the next line treats as affine. |
| **Hardness half** | **Zhuk 2005.00593 §4 + §5.2–5.3 + Brady's Inv–Pol** | Separate optional track; see §1.5. |

### 1.4 Routes rejected, with reasons

**Zhuk 1704 / JACM 2020 as spine — rejected.** Superseded by its own author for exactly the
property that matters to us. Hedge density double. *Kept open* as the sole source of the
algorithm, its polynomiality, the auxiliary-function correctness, and five results 2404 imports
from it.

**Bulatov (arXiv:1703.03021) — rejected, ranked last.** Rests on Tame Congruence Theory
(coloured graphs assign TCT types to pairs) plus centraliser theory. Neither has any
formalization in any prover; both are avoidable on the Zhuk route. arXiv:2604.05231 (Apr 2026)
genuinely improves matters by reproving Bulatov's theory for minimal Taylor algebras — revisit in
2–3 years, not now.

**Minimal Taylor algebras (arXiv:2104.11808) — rejected, and Zhuk's own claim
(`main.tex:1055–1057`) evaluated and found to be a bad trade.** The restriction is real: 2-absorption
becomes strong projectivity (Thm 5.7), 3-absorption becomes centrality (Thm 5.10), so the type
`S` plausibly disappears and with it a fair slice of the six-type bookkeeping — perhaps 20–30% of
§2, and **nothing** of §3, which is half the work. The price is the **cyclic term theorem**: every
minimal-Taylor result in 2104.11808 runs through Thm 3.5, and Prop 5.2 ("every Taylor algebra has
a minimal Taylor reduct") is a corollary of it that cannot be had more cheaply. That is
3,000–6,000 Lean lines *plus* free algebras on `m` generators, which Mathlib does not have.
2404 needs none of it: it uses only *special WNU*, a pigeonhole argument. **Net negative.** Mine
2104.11808 §5 for lemma statements; do not adopt the framework.

**Brady's notes as spine — rejected.** Self-described as "maybe half way through the material
needed for the CSP dichotomy"; no Zhuk-algorithm correctness, no Bulatov completion; 54 `TODO`s
and 32 `exercise`s over 17,747 lines. **Use as the proof source, never as the spine.**

**Anything newer — nothing supersedes 2404.** Willard's three-paper series (arXiv:2502.20517,
2503.03551, one unreleased) shows Zhuk's bridges and "similarity bridges" carry the same
information in locally finite Taylor varieties — read it before finalizing the bridge module, a
cleaner definition may be available. Barto–Hadek–Zhuk arXiv:2604.06335 is useful *negative*
evidence: no simple uniform algorithm is imminent. Gaysin arXiv:2403.06704 (bounded arithmetic
`W¹₁`) is the only prior rigorous re-derivation of a Zhuk component and it targets exactly
`THMCSPDReductionsAreSafe` — read it before writing that module.

**Existing formalizations: none.** GitHub searches for CSP dichotomy / Schaefer / Post's lattice
/ clone theory in Lean, Coq, Isabelle, Agda return zero. `agda-algebras` (Birkhoff HSP in MLTT)
is a design reference, not portable. Isabelle/AFP `Cook_Levin` proves that the complexity wrapper
is its own multi-year project. **`zhuk-lean` is the only reusable Lean code in existence for this
area, and it is ours.**

### 1.5 The hardness half: separate, optional, parallel track

The hardness half shares **only** the strong-subalgebra API with the tractability half, and it
does *not* reuse the tractability spine's existence theorem: 2404 assumes a WNU throughout, so
`LEMUbiquity` in its WNU-assumed form does **not** discharge Zhuk 2021 Theorem 3.3, which is
stated for arbitrary finite idempotent algebras and is what Lemma 4.4 (and hence the WNU-blocker
theorem) consumes. Theorem 3.3's proof is all of 2005.00593 §6 — 33 statements, ~20 pages, a
from-scratch re-derivation of the idempotent part of Rosenberg's maximal-clone classification.

Decision: **hardness is a parallel optional track, not on the critical path.** It is worth
stating clearly that it is *cheaper per unit of headline* than finishing the tractability half
(≈ 9k lines for Tier 1 + Tier 2 versus ≈ 29k for L0), and it is the half that makes the
statement a *dichotomy*. If the project's sponsor wants a dichotomy-shaped statement above all
else, reorder. But the tractability half is the mathematics that the whole field regards as the
hard theorem, and it is where `zhuk-lean` gives partial credit.

Two simplifications found for the hardness half if it is taken up: only the arc ¬(1)⟹¬(4) of
Theorem 4.14 is needed, so Lemmas 4.8, 4.9, 4.11, 4.12 and the entire p-WNU-blocker apparatus are
dead weight; and Brady's explicit proof of `Inv(Pol Γ) = ⟨Γ⟩` (`csp.tex:1258`) yields an
*equality-free* pp-definition, eliminating Zhuk's only real hand-wave there.

---

## 2. WHAT EXACTLY WE FORMALIZE

### 2.0 The honest statement of what is out of reach

Mathlib contains **no complexity theory**. Verified file-by-file at commit `905b9581`
(2026-07-28, Lean 4.32.2, 8,264 files): no `P`, no `NP`, no complexity class, no polynomial-time
many-one reduction, no NP-hardness, no NP-completeness, no Cook–Levin, no SAT/3-SAT/NAE-SAT, no
logspace. `Mathlib/Computability/Reduce.lean` has only *computable* many-one reducibility (`≤₀`),
under which every nontrivial decidable problem reduces to every other — using it would make the
dichotomy **vacuous**. The one polytime notion, `Turing.TM2ComputableInPolyTime`
(`Mathlib/Computability/TuringMachine/Computable.lean:179`), applies to total functions rather
than languages, has exactly two theorems in its file (both about the identity function), and is
**not known to be closed under composition** — that is an open `proof_wanted` at line 284 of the
same file. A polytime notion not closed under composition supports no reduction argument at all.

Therefore:

> **`CSP(Γ) ∈ P if Γ has a WNU polymorphism, and NP-complete otherwise` is not a formalizable
> target at any reasonable cost, and will not be attempted.**

This must be said in the blueprint's abstract, in exactly those words, not buried.

A second honesty point that a blueprint must state out loud: **combinatorial correctness of the
algorithm is, by itself, mathematically vacuous as a statement about `CSP(Γ)`** — satisfiability
of a finite-domain CSP instance is trivially decidable by brute force. All the content of the
tractability half lives in the complexity claim. What correctness buys is that it *forces* the
four main theorems to be stated with exactly the right hypotheses. That is the real value, and
saying so is what distinguishes an honest formalization from a misleading one.

### 2.1 Layer L0 — the algebraic core (the primary target)

Four statements. The first is the paper's missing Informal Claim 1, which has **no formal
counterpart anywhere in 2404** and which we must write.

Ambient setting throughout (see §4 D1–D2 for the design decisions behind it):

```lean
variable {L : FirstOrder.Language} [L.IsAlgebraic] {n : ℕ}
variable {A : Type*} [L.Structure A] [Finite A] [VnAlgebra L n A]
```

where `VnAlgebra L n A` bundles `IsIdempotent L A` together with a distinguished
`w : L.Term (Fin n)` and proofs that `w` is a WNU and *special*
(`w(x,…,x,y) = w(x,…,x,w(x,…,x,y))`). Bundling is deliberate: `zhuk-lean`'s `zhuk_main` already
takes eight explicit hypothesis arguments at 1,600 lines; at 30,000 lines unbundled hypotheses
are unmaintainable.

**L0.1 — Ubiquity ("one of four"), `LEMUbiquity`, `main.tex:1653`.**

```lean
theorem exists_strong_subuniverse
    (B : L.Substructure A) (hB : Chain (L := L) B ⊤) (hcard : 1 < Nat.card B) :
    ∃ (σ : Congruence L A) (T : StrongType) (C : L.Substructure A),
      T ∈ ({.BA, .C, .L, .PC} : Set StrongType) ∧ StrongSub σ T C B
```

`Chain B ⊤` is `B ⋘ A` as an **inductive family carrying the chain and its dividing
congruences** (design decision D4), not a `Prop` — §5 of the paper argues about "the congruences
coming from `C ⋘ A`" and about minimal chain length, neither of which is statable otherwise.
`StrongSub σ T C B` is the witness-carrying `C <_{T(σ)}^A B` (design decision D5), with
nonemptiness and properness of `C ⊊ B` built in.

**L0.2 — Informal Claim 1 (`ICExistenceStrong`, `main.tex:518`), not in the paper.**

```lean
theorem exists_strong_or_zp (hcard : 1 < Nat.card A) :
    (∃ (T : StrongType) (C : L.Substructure A),
        T ∈ ({.BA, .C, .PC} : Set StrongType) ∧ StrongSub ⊤ T C ⊤) ∨
    (∃ (σ : Congruence L A) (p : ℕ), p.Prime ∧ p ∣ n - 1 ∧
        Nonempty ((σ.Quotient) ≃[L] ZpAlg n p))
```

Two things the paper never states appear here and are load-bearing. First `p ∣ n - 1`: `Z_p`
belongs to `𝒱ₙ` only if `w(x,…,x) = n·x = x` in `ZMod p`. Zhuk writes only that "every algebra
`Z_p` belongs to `𝒱ₙ` for a fixed `n`, hence `Z_p` is uniquely defined" (`main.tex:1119–1121`);
the divisibility is never written, and *every* conclusion of the form "`A/σ ≅ Z_p`" implicitly
asserts it. Second, the derivation itself: 2404 never assembles `LEMUbiquity` with
`LEMLInearOnTheTopIsEasy` (`main.tex:1454`) to get from "no BA/C/PC subuniverse" to "a linear
congruence with `σ* = A²`, hence `A/σ ≅ Z_p`". Also note the paper is internally inconsistent
here: `main.tex:523` says `D_x/σ ≅ Z_p` (single factor) while `main.tex:610` says
`D_{x_i}/σ_{x_i} ≅ Z_{q_1} × … × Z_{q_{n_i}}` (a product); the reconciliation (take `σ` minimal =
the intersection of all linear congruences with `σ*` full) must be supplied.

**L0.3 — Reductions are safe, `THMCSPDReductionsAreSafe`, `main.tex:3985`.**

```lean
theorem reductions_are_safe
    {V : Type*} [DecidableEq V] (Θ : Instance L V)
    (hcc : Θ.CycleConsistent) (hirr : Θ.Irreducible)
    (x : V) (B : L.Substructure A) (T : StrongType)
    (hT : T ∈ ({.BA, .C, .PC} : Set StrongType))
    (hB : StrongSub ⊤ T B (Θ.dom x)) :
    Θ.HasSolution ↔ (Θ.reduceAt x B).HasSolution
```

Note `T ∈ {BA, C, PC}` — type `L` is **excluded**, and 2404's own `Solve` sketch
(`main.tex:626`) says "strong subset" where it must mean "excluding type L". This is the loop
invariant of the algorithm and the statement Gaysin's bounded-arithmetic work singles out as the
universal-algebra heart.

**L0.4 — The codimension-one theorem, `THMCodimensionOneTheorem`, `main.tex:4004`.**

The paper's conclusion says "an affine subspace of codimension 1 (the solution set of a single
linear equation)" over `Z_{q_1} × … × Z_{q_k}` with **distinct** primes `q_i`. There is no field
over which that is a vector space, and a "linear equation" is meaningful only over a single `Z_p`
and can involve only the coordinates `i` with `q_i = p`. Zhuk states this qualification only in a
footnote to the algorithm (`main.tex:678–680`), not in the theorem. The Lean statement must carry
it:

```lean
theorem codimension_one
    {k : ℕ} {q : Fin k → ℕ} (hq : ∀ i, (q i).Prime)
    (Θ : Instance L V) (hΘ : …conditions (1)–(7), with Θ and I identified…)
    (φ : (∀ i, ZMod (q i)) →+ (∀ i, QuotDom i)) (hφ : Function.Surjective φ) :
    let Δ : Set (∀ i, ZMod (q i)) := {a | (Θ.restrictAlong φ a).HasSolution}
    Δ = ∅ ∨ Δ = Set.univ ∨
      ∃ (p : ℕ) (_hp : p.Prime) (ψ : (∀ i, ZMod (q i)) →+ ZMod p) (b : ZMod p),
        Function.Surjective ψ ∧ Δ = ψ ⁻¹' {b}
```

Two repairs are embedded. (a) The `∃ p, ∃ surjective ψ, Δ = ψ⁻¹{b}` form is what "codimension 1"
must mean; the underlying fact — a codimension-1 subgroup of a finite abelian group of squarefree
exponent is the kernel of a single surjective hom onto some `Z_p` — is used silently at
`main.tex:4109–4114` and is precisely the lemma Mathlib lacks. (b) The theorem as printed mixes
the instance names `I` and `Θ`: conditions (1),(3),(7) are stated about `I` while (3) and the
conclusion mention `Θ`, which is never bound. From the proof, `Θ` is `I` or a designated
subinstance; this must be resolved before formalizing, not during.

Also required at L0 and stated separately because the source never defines it: **dimension** of
`∏ ZMod q_i` and its subgroups. The paper uses "dimension" nine times (`main.tex:564, 668, 689,
708, 723, 741, 748, 750, 4113, 4120`) and never defines it. Adopt composition length:
`dim G := (Nat.card G).primeFactorsList.length`, with additivity
`dim H + dim (G ⧸ H) = dim G` from `Subgroup.card_mul_index`. **Pin this down before anything
downstream is stated.**

### 2.2 Layer L1 — algorithm correctness as a proposition

Formalize the algorithm as a **fuel-indexed** Lean function (structurally recursive on fuel, so
no well-founded-recursion obligations), with 1704's control flow and 2404's vocabulary.

```lean
def solve (Γ : Lang L A k₀) : ℕ → Instance L V → Option Bool   -- none = out of fuel

theorem solve_sound (m : ℕ) (I : Instance L V) (b : Bool) :
    solve Γ m I = some b → (b = true ↔ I.HasSolution)

theorem solve_total (I : Instance L V) : ∃ m, solve Γ m I ≠ none
```

`solve_sound` is by induction on fuel; `solve_total` needs an explicit well-founded measure,
which Zhuk never gives. Adopt

```
μ(Θ) := ( Σ_{x ∈ Var Θ} (|D_x| − 1) ,  Φ(Θ) )      lexicographic,
Φ(Θ) := Σ_{C ∈ Θ} (K+1)^{rank ρ_C},   K := max #{weaker constraints}, rank = height in Zhuk's Γ-order
```

and check it at all six recursion sites. The weighted potential `Φ` is needed because weakening
replaces one constraint by up to `K` constraints, so naive constraint counts grow.

### 2.3 Layer L2 — the complexity wrapper, stated honestly

Two independent pieces, neither of which claims `∈ P`.

**L2a — a step bound in an explicitly defined unit-cost model.** Instrument `solve` to return
its own operation count, so the cost model is a *definition inside the formalization*:

```lean
def solveC (Γ : Lang L A k₀) : ℕ → Instance L V → Option (Bool × ℕ)

theorem solve_poly : ∃ C d : ℕ, ∀ I : Instance L V,
    ∃ b m, solveC Γ (C * I.size ^ d) I = some (b, m) ∧ m ≤ C * I.size ^ d
```

with a `Convention` in the blueprint enumerating exactly what one unit charges for:
membership/union/intersection/projection of `Finset`s of tuples over `A` of arity `≤ k₀`;
Gaussian elimination over `Z_p` per call; graph reachability per call. Then the residual gap to
`CSP(Γ) ∈ P` — a bit-level simulation of those primitives — is visible, small, and honestly
labelled, rather than hidden. State it as a Remark, never as a theorem.

Two things the blueprint must record with the bound. The degree is `O(|A| + |Γ|)` where
`|Γ| ≤ 2^{|A|^{k₀}}`, i.e. "polynomial" only for fixed `Γ`, with a doubly-exponential exponent;
Zhuk flags this himself (§10.1). And the published depth bound `|A| + |Γ|` (1704 Lemma 5.2) is
**not established** for the `CheckTuple → SolveNonlinked → Solve` path: `CheckTuple` bolts unary
constraints onto `Θ` without re-propagating, destroying 1-consistency, and the needed lemma ("in
a 1-consistent, non-fragmented, non-linked instance every linked component meets every domain
properly") has 1-consistency as a hypothesis. Without the repair the depth is `O(n·|A|)` and the
running time `N^{O(n)}` — not polynomial. The repair is cheap (run arc consistency inside
`SolveNonlinked` before splitting into components) and **must be in the blueprint**.

**L2b — the hardness corollary, seed-relative.** If and only if the optional hardness track is
taken up:

```lean
structure GadgetReduction (Γ₁ : Lang L₁ A₁ k₁) (Γ₂ : Lang L₂ A₂ k₂) where
  toFun   : Instance Γ₁ → Instance Γ₂
  sat_iff : ∀ I, (toFun I).HasSolution ↔ I.HasSolution
  c       : ℕ
  size_le : ∀ I, (toFun I).size ≤ c * I.size + c

theorem gadgetReduction_of_no_wnu (h : ¬ HasWNUPolymorphism Γ) :
    Nonempty (GadgetReduction NAE₃ Γ)

theorem csp_npHard_of_no_wnu
    (seed : NPHard NAE3SAT)                 -- Schaefer/Cook–Levin: an explicit hypothesis
    (h : ¬ HasWNUPolymorphism Γ) : NPHard (CSP Γ)
```

`GadgetReduction` is unconditional, honest, composes definitionally, and every `toFun` written on
`List`/`Fin`/`Finset` data is executable by construction — so the only thing missing relative to
"polynomial-time many-one reduction" is the cost model, and `size_le` already certifies the
nontrivial part. The `seed` **hypothesis** rather than an `axiom` is the crux of the honesty:
`#print axioms` stays clean, nothing is `sorry`ed, and the import is visible in the signature.

---

## 3. THE MISSING LAYERS, RANKED

Everything below must be built under Mathlib before any Zhuk-specific mathematics. Estimates
assume Mathlib-quality API (simp lemmas, `SetLike` boilerplate, order instances), calibrated
against `Mathlib/GroupTheory/Congruence/` (~1,000 lines for `Con` on `Mul`) and
`ModelTheory/Substructures.lean` (985 lines).

| # | Layer | Lines | Why it is missing / what Mathlib gives |
|---|---|---:|---|
| 1 | **Congruences, quotients, correspondence.** `Congruence L M` as `SetLike … (M × M)` extending `Setoid`; `CompleteLattice`; `congGen`; `ker` of an `L.Hom`; `map`/`comap`; `Congruence.Quotient` with a **global** `L.Structure` instance; universal property; first iso theorem; correspondence theorem; `Congruence.pi`/`prod`. | 700–1200 | Mathlib has **no congruence for a general structure** — grep over all of `ModelTheory` returns only `Prestructure`, `equivSetoid`, `DirectLimit.setoid`. `Con` is `[Mul M]`-specific but is the exact template to copy, including `Con.submonoid`/`ofSubmonoid`, the congruence ↔ subalgebra-of-`M×M` dictionary Zhuk relies on. **Verified by compilation:** for `[L.IsAlgebraic]` a hand-rolled congruence yields a `Language.Prestructure` and `quotientStructure` gives the quotient algebra for free — **but** the instance must be in scope when the *statement* is elaborated; `letI := c.pre` inside a tactic block fails with `failed to synthesize L.Structure (Quotient c.toSetoid)`. **Copy the construction, not the interface.** |
| 2 | **Relations toolkit.** `Subdirect` at arbitrary index types; `proj_{i₁…i_s}`; `δ₁ ∘ δ₂`, `δ⁻¹`, linked, bijective; `σ^{[n]}`; stability of a coordinate under `σ`; `R/σ`; rectangularity; the parallelogram property; rectangular closure; `Substructure.pi`/`prod`. | 800–1500 | **Zero hits for "subdirect" anywhere in Mathlib.** `Rel.comp`/`Rel.inv` exist but carry no algebra. `zhuk-lean`'s `⊓` / `.map (reindexHom g)` / `.comap (evalHom i)` idioms are the right primitives and cover every relational operation the proof needs. |
| 3 | **Mixed-prime linear algebra.** Coset predicate for `∏ ZMod q_i`; `dim` = composition length with additivity; codimension-1 ⟺ kernel of one surjective hom onto `ZMod p`; `p`-part decomposition justifying "the equation involves only coordinates with `q_i = p`"; subuniverses of `Z_p^k` = affine cosets; `L.Structure (ZMod p)` under `p ∣ n−1`. | 600–1000 | `AddSubgroup.toZModSubmodule : AddSubgroup M ≃o Submodule (ZMod n) M` (`Algebra/Module/ZMod.lean:102`) is the load-bearing decl. **`AffineSubspace` does not apply** — it needs a single base ring, and the ambient object is a mixed-prime product. Use "coset of an `AddSubgroup`". Structure theorem, Goursat, primary decomposition, `isCyclic_of_prime_card`, `zmodAddEquivOfGenerator` all present. |
| 4 | **Irreducible congruences and `σ*`.** The lattice of `σ`-stable binary subalgebras of `A²`; Zhuk's `irreducible`; `σ*` as its minimum; the equivalence "σ irreducible on `A` ⟺ `0` irreducible on `A/σ`"; well-foundedness for finite `A`. | 300–500 | **Mathlib's `InfIrred` is the wrong notion.** Zhuk's meet ranges over `σ`-stable *binary subalgebras of `A²`*, a strictly larger lattice than `[σ,1]` in `Con(A)`, and is finitary-unbounded rather than binary. `σ*` is a **minimal subalgebra, not a priori a congruence** — "σ* is a congruence" is condition (2) in the definition of a *linear* congruence (`main.tex:1370`), so Zhuk is explicit that it can fail. Typing `σ*` as `Congruence` would silently collapse the linear/PC distinction. Finiteness/well-foundedness is free (`SetLike` + `Finite.to_wellFoundedGT`, verified). |
| 5 | **pp-definability, semantic.** pp-formulas as projections of intersections; closure under conjunction, existential quantification, substitution; preimages. | 200–400 | `Set.Definable` is full first-order; `IsExistential` is ∃-prefix only; there is **no positive-primitive fragment**. Model semantically — building a syntactic fragment plus its semantics costs several times more. `LEMBACenterSImplyPPDefinition` has 11 uses and needs an induction over pp-structure; **check this interface early, it is on the critical path.** |
| 6 | **Clones, polynomial clones, PC algebras.** `Clo_m(A)` (have: `zhuk-lean`'s `termOps`); closure under composition/permutation; polynomial clone via `L[[A]]`; PC = `clone(F ∪ constants)` is everything; Sierpiński ⟹ decidability of PC via the binary part only. | 200–400 | `L[[α]]` + `Substructure.withConstants` + `closure_withConstants_eq` make polynomial operations nearly free. `termOps` is already the hard part. |
| 7 | **WNU / special WNU / `𝒱ₙ`.** `IsWNU` as **data** in the `TaylorAt` style; special WNU; the existence lemma; the `VnAlgebra` class. | 150–300 | New but the `TaylorAt` pattern transfers directly: state identities as equations between `t.relabel u` and `t.relabel v`, so substitution arguments become `Term.realize_relabel` rewrites rather than index arithmetic. |
| 8 | **Products / powers extension.** `Substructure.pi`, `Substructure.prod`, subdirect at arbitrary arity, coordinate-subset projections. | 100–200 | `zhuk-lean/Product.lean` (143 lines) is *the entire Mathlib gap* at the previous project's scale and is reusable verbatim; Mathlib's only product-shaped `Structure` instance is `Ultraproducts.«structure»` on the quotient. |
| 9 | **Graph / linkedness glue.** `Linked := Relation.ReflTransGen` on `Σ x, D x`; the bridge `(SimpleGraph.fromRel R).Reachable = Relation.EqvGen R` for symmetric `R`; `DecidableRel (ReflTransGen R)` for finite types. | 40–80 | `Relation.reflTransGen_symmGen` (`Logic/Relation.lean:878`) is exactly the lemma. `fromRel` silently deletes the diagonal, and the nearby `reachable_fromEdgeSet_fromRel_eq_reflTransGen` is about a *different* graph — do not assume it applies. |
| 10 | **Finite-lattice minimization.** A packaged `argmin`-over-a-finite-lattice lemma. | 50–100 | "Consider a minimal/maximal `X` such that …" recurs constantly in Zhuk (at least four places in §5 alone where the minimality condition has free variables or the family has no maximum). `zhuk-lean` used ad-hoc `Nat.find`; that will not scale. |
| 11 | **`Finite (Setoid α)`**, `Finset.strongDownwardInduction` ergonomics. | 10–20 | Missing trivia; `Setoid α ↪ (α → α → Prop)` + `Finite.of_injective`. |
| | **Total new infrastructure** | **3,150–5,700** | before any Zhuk-specific mathematics |

**Do not build, under any circumstances:** `P`, `NP`, `NPComplete`, `≤_p`, Cook–Levin,
`TM2ComputableInPolyTime.comp`, the cyclic term theorem, free algebras in a variety, Tame
Congruence Theory, commutator theory, pp-interpretability / pp-powers / minions, or
`Pol`/`Inv` in general (needed only by the hardness track, where it is ~600 lines).

**Do not extend `Mathlib/Combinatorics/Optimization/ValuedCSP.lean.** It is a false friend: same
words (CSP, polymorphism), entirely different mathematics (valued CSP, fractional polymorphisms,
ordered cost monoid), sharing no definition with the crisp dichotomy.

---

## 4. MODULE ARCHITECTURE

Repository `zhuk-csp`, root `Zhuk.lean`, everything in `namespace Zhuk`, `open FirstOrder Language`.
`lakefile.toml` copies `zhuk-lean`'s: Mathlib pinned by `rev`, `relaxedAutoImplicit = false`
(a typo'd identifier must be an error, not a fresh universe-polymorphic variable),
`weak.linter.mathlibStandardSet = true`.

### 4.0 The eleven design decisions to legislate on day one

These are cheap now and catastrophic to revisit at 20k lines. Each becomes a numbered
`Convention` in the blueprint, cited **at the point of use inside proofs**, not merely declared.

| | Decision |
|---|---|
| **D1** | Build on `Mathlib.ModelTheory`. Keep `L` generic in the foundational layer; assume `[L.IsAlgebraic]`. Do **not** instantiate to a one-symbol language and do **not** define a bespoke algebra type — that throws away 1,591 generic lines including the two hardest theorems, duplicates ~900 lines of `Substructure` API, and loses `mem_closure_iff_exists_term` (whose variable type *is* the generating set) and `L[[A]]`-based PC algebras. `𝒱ₙ` enters as a thin `class VnAlgebra L n A` purely to shorten signatures. |
| **D2** | A subuniverse is `L.Substructure A` (bundled) in constructions and `Set A` in statements, converted by coercion — `zhuk-lean`'s existing split. Absorption stays **relative** (`Witnesses (E D : Set M)`), so `C <_T B ≤ A` never requires forming "the algebra on `B`". Reject the "everything inside one ambient finite set" design: `Z_p` is not a subalgebra of `A`, and `A/σ ≅ Z_p`, `A₁/σ₁ ≅ A₂/σ₂`, `ζ ≤ A × A × Z_p` all need genuinely external algebras. |
| **D3** | Bespoke `Congruence L M` with a **global** `L.Structure` instance on its `Quotient`. Do not route through `Language.Prestructure`: verified failure — the instance is unavailable at statement-elaboration time, so theorems about a *varying* congruence cannot even be stated. |
| **D4** | `⋘` is an **inductive family carrying its chain and the chain's dividing congruences**, not a `Prop`. §5 speaks of "the congruences coming from `C ⋘ A`" and picks minimal chain lengths; as a bare `Prop` those arguments are unstatable. Same for the relative variants `⋘^D`. |
| **D5** | `C <_{T(σ)}^A B` is the **primitive**, with `T : StrongType` an inductive (`BA \| C \| S \| D \| L \| PC`) and `σ : Congruence L A` a genuine argument **constrained to `⊤` when `T ∈ {BA,C,S}`** — not a junk field. `<_D`, `<_L`, `<_PC` are then defined by conditions on `σ`; the paper's "`<_L` is `<_D` where the congruence σ from the definition is linear" is ill-formed as written, because σ is existentially quantified in `<_D`. Theorem 21 and Lemma 25 quantify over the witnesses in both hypotheses and conclusions. |
| **D6** | `σ*` has type `L.Substructure (A × A)`, **never** `Congruence`. It is a tolerance (reflexive, symmetric, not transitive); "σ* is a congruence" is a hypothesis (clause 2 of *linear congruence*). Its existence as a *minimum* is equivalent to irreducibility — a lemma the paper never states and we must. |
| **D7** | Nonemptiness and properness (`∅ ≠ C ⊊ B`) are baked into every `<_T`. The dotted variants (`⋘̇`, `<̇_T`, `≤̇_T`) are separate definitions with explicit bridging lemmas. The paper's clause "`C <_S B` if there exists a BA and central subuniverse `D` in `B` with `D ⊆ C`" is **literally universally true** unless `D` is required nonempty (the empty set is a subuniverse of every idempotent algebra and is vacuously absorbing and vacuously central); repair it explicitly. |
| **D8** | Binary absorption carries its witness term where the mathematics needs it: `Witnesses`/`WitnessesBin` (term as data) is the primitive, `BinAbsorbs`/`Absorbs` the existential wrapper. Zhuk 2021 tracks `≤_{BA(t)}` carefully and 2404 drops the term index throughout; Lemma 19 is **false** without a common term. `zhuk-lean` already made this split — keep it. |
| **D9** | Relations are `L.Substructure (I → A)` for an arbitrary finite index **type** `I`, manipulated only by `⊓`, `.map (reindexHom g)`, `.comap (evalHom i)`. Never encode into `Fin n` unless the numeral is genuinely used; convert once, at the boundary, with a named lemma. Adopt `zhuk-lean`'s live-set + block-function encoding (`IsEssentialOn S (J : Finset I) (block : I → Fin m) R`) for every regrouping argument. |
| **D10** | CSP instances are a `List` of constraints (multiplicity is irrelevant to satisfiability but relevant to `size`, and `List` gives free `length`), variables an arbitrary type with a `Finset`. Weakening and cruciality therefore need **occurrence-level** semantics. |
| **D11** | `leanblueprint` markup (`\lean{}`, `\uses{}`, `\leanok`) from draft 1; all cross-document references by **label**, never by number, machine-checked in CI. Verified defect in the prior art: nine of `zhuk-lean`'s blueprint citations are already stale after two commits inserted statements into a shared counter. At 450 pages that failure mode is fatal. |

### 4.1 File plan, in dependency order

Line counts are central estimates for finished, documented, Mathlib-style code.
**[R]** = reused from `zhuk-lean` essentially verbatim; **[R+]** = reused and extended.

#### Part 0 — algebraic substrate (mostly existing)

| File | Contents | Lines |
|---|---|---:|
| `Zhuk/Algebra/Product.lean` **[R]** | `piStructure`, `prodStructure`, `realize_pi/prod`, `fstHom`, `sndHom`, `reindexHom`, `evalHom`, `snoc_funMap`; **new:** `Substructure.pi`, `Substructure.prod`, subdirect at arbitrary index types, coordinate-subset projections | 250 |
| `Zhuk/Algebra/Absorption.lean` **[R+]** | `IsIdempotent`, `Witnesses`, `Absorbs`, `BinAbsorbs`, **new** `TernAbsorbs`, `TaylorAt`/`IsTaylorOn` as data, `binAbsorbs_of_oneSided` | 250 |
| `Zhuk/Algebra/StarPower.lean` **[R]** | star powers indexed by `Fin ℓ → Fin k` (no Euclidean division) | 55 |
| `Zhuk/Algebra/Essential.lean` **[R+]** | `IsEssential`; **generalized to dependent products** (`piStructure`, mixed families `(C₁,C₂,C₃)`) — required by `LEMBACenterSPossibleIntersections` and `THMMainStableIntersection`, which use distinct `Cᵢ` on distinct algebras | 350 |
| `Zhuk/Algebra/Regrouping.lean` **[R+]** | `IsEssentialOn` with live `Finset`; doubles as the generic reindexing/transport lemma | 200 |
| `Zhuk/Algebra/Relational.lean` **[R+]** | `termOps` = `Clo_m(A)` as a subuniverse of a power; `exists_witnesses_of_not_hasEssential` (**Barto–Kazda = 2404's `LemAbsorptionImpliesEssential`**) | 160 |
| `Zhuk/Center/{Center,Step,Absorbs,Central}.lean` **[R]** | `Subdirect`, `nbhd`, `leftCenter`, `CentrallyAbsorbs` (= 2404's *central subuniverse*, verbatim), `center_step`, `center_central`, **`zhuk_center` (= 2404's `LEMCentralRelationImplies`, 8 uses)** | 520 |
| `Zhuk/Center/{Doubling,Ternary}.lean` **[R+]** | doubling trick **restored to the mixed form** (`(C₁,C₂,C₃)`-essential → `(C₁,C₂,C₁,C₂)` → `(C₁,C₁,C₂)`); `exists_ternary_witnesses` (= `LEMCenterImpliesTernaryAbsorption`) | 620 |
| | *subtotal (≈ 1,600 already exists)* | **2,405** |

#### Part 1 — new infrastructure (§3 above)

| File | Contents | Lines |
|---|---|---:|
| `Zhuk/Algebra/Congruence.lean` | `Congruence L M` as `SetLike … (M × M)`, `CompleteLattice`, `congGen`, `ker`, `map`/`comap`, `pi`/`prod`, `toSubstructure`/`ofSubstructure` | 700 |
| `Zhuk/Algebra/Quotient.lean` | `Congruence.Quotient` + **global** `L.Structure` instance, `mk : M →[L] Quotient`, universal property, `Term.realize_mk` | 400 |
| `Zhuk/Algebra/Correspondence.lean` | first iso theorem; correspondence theorem; third iso; `B/σ` for `B ≤ A` = **image** in `A/σ` (both readings are used interchangeably in §5 — legislate one and prove the bridge) | 250 |
| `Zhuk/Algebra/Relations.lean` | `proj`, `δ₁ ∘ δ₂`, `δ⁻¹`, `Linked`, bijective, rectangular, parallelogram property, rectangular closure | 700 |
| `Zhuk/Algebra/StableUnder.lean` | stability under `σ`, `σ^{[n]}`, `R/σ`, the lattice of `σ`-stable binary subalgebras of `A²` | 350 |
| `Zhuk/Algebra/Irreducible.lean` | Zhuk's `irreducible`; `σ*` as `L.Substructure (A × A)`; existence-as-minimum ⟺ irreducibility; "σ irreducible on `A` ⟺ `0` irreducible on `A/σ`" | 400 |
| `Zhuk/Algebra/PP.lean` | semantic pp-definability + closure properties + preimage | 350 |
| `Zhuk/Algebra/Clone.lean` | clone closure laws, polynomial clone via `L[[A]]`, PC algebras, Sierpiński ⟹ decidability | 250 |
| `Zhuk/Algebra/WNU.lean` | `IsWNU` as data, special WNU + existence lemma, `class VnAlgebra` | 250 |
| `Zhuk/Algebra/Zp.lean` | `ZpAlg n p` with the `p ∣ n − 1` side condition; subuniverses of `Z_p^k` = affine cosets; congruences of `Z_p^k`; `A/σ ≅ Z_p` transport | 350 |
| `Zhuk/Algebra/MixedPrime.lean` | coset predicate for `∏ ZMod q_i`; `dim` + additivity; codim-1 ⟺ one surjective hom onto `ZMod p`; `p`-part decomposition | 600 |
| `Zhuk/Algebra/Linked.lean` | `Linked` on `Σ x, D x`, `fromRel` bridge, decidability | 80 |
| `Zhuk/Algebra/Minimize.lean` | argmin/argmax over a finite lattice, packaged | 100 |
| | *subtotal* | **4,780** |

#### Part 2 — classical prerequisites (Brady) — **milestone M1**

| File | Contents | Lines |
|---|---|---:|
| `Zhuk/Classical/PPAbsorption.lean` | `LEMBACenterSImplyPPDefinition` (11 uses); `LEMBACenterImplies`; `LEMBACenterImplyIntersection`; `LEMBACenterSImplyFactor`; `LEMBACenterSOnPowerImplies`; `LEMReverseHomomorphism`. The `T = S` cases proved **parametrically**, not "word to word" | 700 |
| `Zhuk/Classical/Connectivity.lean` | Jónsson absorption, absorbing directed paths, `LEMBACenterLinkedness` (Barto–Kozik Prop 2.15(i)) | 500 |
| `Zhuk/Classical/BinCentral.lean` | `bin-central-criterion` (`csp.tex:10413`): binary absorption of a central `C` ⟺ `∀ a ∉ C, c ∈ C : Sg{a,c}` has a proper BA subalgebra | 350 |
| `Zhuk/Classical/AbsorptionTheorem.lean` | **Barto–Kozik Absorption Theorem** (`csp.tex:10451`) + **Loop Lemma**, from `zhuk_center` | 500 |
| `Zhuk/Classical/Abelian.lean` | abelian; `LEMAbelianEquivalentDefinition` (diagonal is a block of a congruence on `A²`) | 400 |
| `Zhuk/Classical/Malcev.lean` | Mal'cev algebras; abelian ⟹ hereditarily absorption-free; idempotent Taylor + hereditarily absorption-free ⟹ Mal'cev | 900 |
| `Zhuk/Classical/AbelianAffine.lean` | abelian Mal'cev ⟹ affine (`csp.tex:4235–4706`); **abelian ⟺ affine for WNU** | 1,200 |
| | *subtotal* | **4,550** |

#### Part 3 — Zhuk §2 + §5, strong subalgebras — **milestone M2**

| File | Contents | Lines |
|---|---|---:|
| `Zhuk/Strong/Types.lean` | `StrongType`; `StrongSub σ T C B` (D5); multi-types `ML/MPC/MD`; S-free; dotted variants and their bridges; the empty-set repairs (D7) | 550 |
| `Zhuk/Strong/Chain.lean` | `⋘` as an inductive family carrying the chain (D4); dividing congruences; relative `⋘^D`; the "duplicate the coordinate" transport lemma (`main.tex:1838–1843`) proved rather than gestured at | 450 |
| `Zhuk/Strong/Bridges.lean` | bridges, `δ̃`, reflexive bridges, `LEMBridgeComposition` (1704 Lem 6.3), `LEMBridgeBetweenCongruences`, `LEMAbsorbingEquality` (1704 Lem 7.2) | 700 |
| `Zhuk/Strong/Linear.lean` | linear / perfect linear / PC congruences; `LemBridgeEquivalentToAbelianness`; `LEMNiceBridgeGivesAbelianGroup`; **`LEMBuildingPerfectCongruence` via the abelian route**; `LEMLInearOnTheTopIsEasy`; `LEMPCOnTheTopIsEasy` (with the missing BA/centre-free hypothesis supplied) | 1,000 |
| `Zhuk/Strong/Propagation.lean` | Lemma 13 (Ubiquity prep), **Lemma 14 (Propagation, 7 parts)**, **Corollary 15 — supplied, since the paper never proves it anywhere**, Cor 16, Cor 17, Cor 18, **Lemma 19 restated correctly** (with `pr₁(R) = A₁` and a common BA term) | 950 |
| `Zhuk/Strong/Essentiality.lean` | **New, not in the paper:** the mixed-essentiality lemma for several distinct central (hence ternary absorbing) subuniverses. This breaks the §5 citation cycle *and* supplies the missing `n = 2` step of Theorem 21(c). Highest-risk new mathematics in Part 3 | 550 |
| `Zhuk/Strong/Intersection.lean` | Lemma 20 `IntersectALL`; **Theorem 21 `MainStableIntersection`**; Corollary 22; `LEMSelfIntersectionPC` (141 source lines); `LEMIntersectionPCLinearIsGood` (209 source lines, double induction on `k+ℓ`) | 1,900 |
| `Zhuk/Strong/MultiType.lean` | Lemma 23 (`MultiTypeStillStable`), Lemma 24 (`PreserveLinkedness`, with the hypothesis mismatch against `LEMPreserveLinkdnessOneStepAUX` repaired), Lemma 25 (`MaximalMultExtension`) | 700 |
| `Zhuk/Strong/Ubiquity.lean` | `LEMMainExistenceOfIrreducibleCongruence`; **`LEMUbiquity` (L0.1)**; **`exists_strong_or_zp` (L0.2, Informal Claim 1)** | 750 |
| | *subtotal* | **7,550** |

#### Part 4 — Zhuk §3, CSP instances and the main induction — **milestones M3, M4**

| File | Contents | Lines |
|---|---|---:|
| `Zhuk/Instance/Defs.lean` | `Instance` as a list of constraints; `Var`, `D_x`, subinstance, `Sol`, subdirect solution set; reductions `D^(⊤)`, `I^(⊤)`; the three orders `⋘`, `⋘^D`, `≤_T^D`; conjunction/renaming of instances | 650 |
| `Zhuk/Instance/Consistency.lean` | paths, "connects", 1-consistency, cycle-consistency, linked (**the `main.tex:2089` per-variable definition**, with `¬Fragmented` carried separately — the informal claim's global-connectivity reading is inequivalent), fragmented; hereditary lemmas (consistency passes to subinstances and weakenings) | 550 |
| `Zhuk/Instance/InducedCon.lean` | `Con(R,i)`, `Con(I,x)`, `Con(I)`; PC/Linear type of an instance; adjacency of congruences and constraints; connected instances | 450 |
| `Zhuk/Instance/Weakening.lean` | weaker/weakening at occurrence level, dummy variables, crucial constraint/instance, `GetCrucialInstance` **with the missing termination argument** (Dershowitz–Manna multiset order on cylinder complements) | 550 |
| `Zhuk/Instance/Covering.lean` | expanded coverings, tree coverings, facts (p1)–(p8) with (p4), (p5), (p7) proved rather than asserted; Lemma 30 (= 1704 Lem 6.1); Lemma 35 (= 2005.00593 Lem 5.6, an iterative procedure needing an explicit well-founded recursion) | 900 |
| `Zhuk/Instance/Aux.lean` | §3.2's nine proved lemmas: `LEMBridgeFromRelation`, `LEMConnectedProperties` (**with the missing third hypothesis repaired — see §7.5**), `LEMCrucialMeansIrreducible`, `LEMParalPropertyFromCrucialInMultiType`, `LEMFindOneConsistentForAll` (with the `T = BA` case supplied), `LEMMinimalPCLinearReductionIsConsistent` (with the MT/MD minimality mismatch resolved), `CORSameTypeReductionAndConstraint`, and `LEMMinimalContainingIsMinimal` (**commented out of the source but needed at `main.tex:3527`**) | 2,000 |
| `Zhuk/Instance/Bridge.lean` | `LEMGetABridgeFromSubdirectPCLinearInstance` — 8 hypotheses, two auxiliary instances, two nested minimality choices, five silent imports to be made explicit, the `T = S` case of Case 1 to be supplied. Single biggest cost centre in §3.2 | 1,200 |
| `Zhuk/Main/Inductive.lean` | **`THMMainInductiveCSPClaim` split into two named theorems** (A) crucial ⟹ parallelogram ∧ ((1b) ∨ (1c)), and (B) BA/central reductions preserve solvability; strong induction on `μ(I,D^(1)) = Σ_x |D_x^(1)|`, universally quantified over all instances at a level, with the two-phase step written out; the two genuine gaps (H2, H14) closed | 2,500 |
| `Zhuk/Main/PCSurvival.lean` | `THMPCDoesnotKillAllSolutions`; the four termination arguments (Remark 2, Ω, Υ′, Θ′) on the multiset extension of "is weaker than"; the false-but-unused claim about Θ′ dropped | 800 |
| `Zhuk/Main/Safe.lean` | **`THMCSPDReductionsAreSafe` (L0.3)** | 300 |
| `Zhuk/Main/Codim.lean` | **`THMCodimensionOneTheorem` (L0.4)**, with the `I`/`Θ` identification resolved and hypothesis 2 strengthened from "S-free" to "no nontrivial BA or central subuniverse" | 700 |
| | *subtotal* | **10,600** |

#### Part 5 — L1, the algorithm — **milestone M5**

| File | Contents | Lines |
|---|---|---:|
| `Zhuk/Algorithm/Lang.lean` | `Γ := {ρ : arity ≤ k₀, preserved by w}` as a *definition*; the three closure lemmas (intersection with subuniverse boxes, projections, weaker constraints) | 300 |
| `Zhuk/Algorithm/Decidable.lean` | decidability instances: BA (binary part of the clone as a finite fixpoint), central (internal 2404 definition), PC (Sierpiński ⟹ binary part suffices), congruence/maximal/minimal-linear, irreducible/linear/PC congruences | 500 |
| `Zhuk/Algorithm/Defs.lean` | fuel-indexed `solve` and subroutines, 1704 control flow with four simplifications: drop `FindEquationsNonlinked`/`FindOneEquationNonlinked`/`CheckTuple`/`SolveNonlinked` in favour of 2404's (p2) split-into-linked-components (this also removes the `I := {1}` bug); merge the three consistency checks behind one `ForceConsistency` contract | 900 |
| `Zhuk/Algorithm/Consistency.lean` | `CheckCycleConsistency` + Lemma 5.3 (the one-sentence path induction written out); `CheckIrreducibility` + Lemma 5.4, **including the well-definedness lemma** that the propagated partition does not depend on the choice of constraints or order | 600 |
| `Zhuk/Algorithm/Linear.lean` | `SolveLinearCase`; Lemma 7.20 (a subalgebra of `∏ Z_{p_i}^{n_i}` is a product of affine subspaces) — the hidden workhorse behind every "`k+1` queries suffice"; `FactorizeInstance` | 800 |
| `Zhuk/Algorithm/Sound.lean` | `solve_sound` | 700 |
| `Zhuk/Algorithm/Total.lean` | `solve_total` with the lexicographic measure `μ` | 500 |
| `Zhuk/Algorithm/Cost.lean` | `solve_poly`; depth bound with the **FLAG-DEPTH repair** (arc consistency inside the component split) and the corrected inner-loop potential | 700 |
| | *subtotal* | **5,000** |

#### Part 6 — L2, the wrapper

| File | Contents | Lines |
|---|---|---:|
| `Zhuk/Complexity/Model.lean` | project-local `DecisionProblem`, `InNP`, `PolyManyOneReducible`, `NPHard`, `GadgetReduction` + composition | 350 |
| `Zhuk/Complexity/Wrapper.lean` | seed-relative statements; the explicit Remark on the residual gap | 200 |
| | *subtotal* | **550** |

#### Optional Part H — the hardness track (not on the critical path)

`Zhuk/Hard/{Relation,Clone,PP,Galois,Reduction,WNU,Blocker,Core,Constants,EssentiallyUnary,HSP,Symmetric,Maroti,Main}.lean`.
The starred modules of report 08 (Galois, Blocker, Core, Constants, EssentiallyUnary, HSP,
Reduction) are independent of the strong-subalgebra development and can be finished immediately,
yielding a complete sorry-free hardness theorem *conditional on* Theorem 4.14 — which is then the
single interface to the heavy algebra (2005.00593 §6, ≈ 4–6k lines). Total ≈ 9,000 lines.

### 4.2 Totals

| Layer | New Lean lines | Cumulative |
|---|---:|---:|
| Part 0 (≈1,600 exists) | 800 | 800 |
| Part 1 | 4,780 | 5,580 |
| Part 2 (**M1**) | 4,550 | 10,130 |
| Part 3 (**M2**) | 7,550 | 17,680 |
| Part 4 minus `Codim` (**M3**) | 9,900 | 27,580 |
| Part 4 `Codim` (**M4 = L0 complete**) | 700 | 28,280 |
| Part 5 (**M5 = L1**) | 5,000 | 33,280 |
| Part 6 (**M6 = L2**) | 550 | 33,830 |
| Optional Part H | 9,000 | 42,830 |

Range, honestly: **30,000–45,000 lines for L0+L1+L2.** Four independent estimates (per source
page at ~200 lines/page against Brady-equivalent pages; per source statement at ~134 lines; per
blueprint page at ~65 lines; comparables for "one 50-page paper plus prerequisites") all land in
this band. Read the low end as unreachable: Mathlib has *no* universal algebra, and §3 is
instance-heavy combinatorial bookkeeping that formalizes worse than algebra.

---

## 5. BLUEPRINT PLAN

### 5.1 Structure: five volumes, not one document

The prior art's process — blueprint drafted, reviewed six times end-to-end by two independent
reviewers, then formalized, then revised from what formalizing found — produced a 27-page
document. At 440 pages that loop cannot be run end-to-end. **Split into five volumes, each with
its own theorem counter, each running the full loop independently, cross-referenced by
`leanblueprint` label.** Volume boundaries are chosen at the points where the dependency graph
narrows to a small named interface.

Every volume follows the house style of `zhuk_centers.tex` exactly:

* One shared theorem counter per section (`\newtheorem{theorem}{Theorem}[section]`, everything
  else `[theorem]`), so Definition 1.9 and Lemma 1.10 are adjacent numbers.
* **The volume's main theorem stated before §1, so it is Theorem 0.1**, and proved in one
  paragraph at the end from named corollaries.
* Every environment carries a bracketed title immediately followed by a
  `type:kebab-case-content` label — the regex in the appendix generator *is* the style guide, and
  anything it does not match silently vanishes from the index. Add a `--check` CI mode that
  fails on an untitled environment, a malformed label, a dangling `\ref`, a statement no
  `\uses` mentions, or a `\lean{}` naming a declaration absent from the build.
* Named equation labels for definition clauses (`eq:E1`, `eq:E2`) and manual tags
  `(†) (‡) (∗_ℓ)` for in-proof claims that are later re-instantiated — displayed, universally
  quantified over everything they will ever be instantiated at, and established **before** any of
  those elements is named.
* Standing hypotheses are numbered, labelled, citable `Convention`s with an **audit of where each
  clause is consumed**, plus an explicit instruction to the formalizer. Theorems still restate
  their hypotheses in full; nothing is inherited across a section boundary.
* Every non-trivial proof step names the statement it uses. No "clearly", no "easy to see", no
  unwitnessed "similarly", no ellipsis notation. Long proofs are cut into labelled Steps referred
  to by number.
* Four appendices per volume: **A** statement-level citation index (generated); **B** module
  order; **C** imported background *in the form used*; **D** concordance with the source, whose
  third column admits "weaker" as well as "stronger".
* **Remarks are first-class and carry the formalization content.** In the prior art 16 of 60
  statements are Remarks. Target the same ratio. The six types that earn their place:
  quantifier-form warnings naming the exact corner where two readings part company; degenerate-case
  audits that let main proofs skip case splits; indexing-design justifications; proof-shape
  warnings ("this argument doubles back on itself; prove (‡) before fixing the element"); scope
  limits; and post-formalization findings recorded *next to* the affected statement without
  rewriting correct prose.

### 5.2 Volume plan

| Vol | Title | Chapters | Pages |
|---|---|---|---:|
| **I** | **Foundations: congruences, relations, and the linear layer** | 0. *Theorem 0.1:* the correspondence and quotient package, stated as the volume's deliverable. 1. Signatures, algebras, subuniverses, products (revised from `zhuk_centers` §1). 2. Congruences and quotient algebras. 3. The correspondence theorem and `B/σ` for `B ≤ A`. 4. Relations: projections, composition, inverse, linked, subdirect, rectangularity, the parallelogram property. 5. Stability under σ; σ-stable binary subalgebras; irreducible congruences; `σ*` as a tolerance. 6. pp-definability, semantically. 7. Clones, polynomial clones, PC algebras, Sierpiński. 8. WNU, special WNU, `𝒱ₙ`. 9. `Z_p`, mixed-prime products, dimension, codimension one. | **70** |
| **II** | **Classical prerequisites: absorption, the Absorption Theorem, abelian ⟹ affine** | 0. *Theorem 0.1:* abelian Taylor ⟹ affine, and the Absorption Theorem. 1. Absorption, relative form (revised from `zhuk_centers` §2, unchanged). 2. Essential relations over mixed families — **restoring the mixed doubling lemma the Lean specialized away**. 3. pp-propagation of BA and central subuniverses. 4. Jónsson absorption and connectivity. 5. The binary–central criterion. 6. The Absorption Theorem and the Loop Lemma, from Zhuk's centre theorem. 7. Abelian algebras and the diagonal-block characterisation. 8. Mal'cev algebras; hereditary absorption-freeness. 9. Abelian Mal'cev ⟹ affine; abelian ⟺ affine for WNU. | **80** |
| **III** | **Strong subalgebras (Zhuk §2, §5)** | 0. *Theorem 0.1:* Ubiquity. 1. The six types and the standing type-parameter discipline. 2. `⋘` as data; dividing congruences; coordinate duplication. 3. Bridges, `δ̃`, composition. 4. Linear, perfect linear, and PC congruences; the abelian route to `LEMBuildingPerfectCongruence`. 5. Propagation: Lemma 14 and Corollaries 15–18 (**Cor 15 supplied; Lemma 19 restated**). 6. **Mixed essentiality** — new; breaks the citation cycle. 7. The intersection theorem: Lemma 20, Theorem 21, Corollary 22. 8. Multi-types: Lemmas 23–25. 9. Ubiquity, and Informal Claim 1 assembled. | **120** |
| **IV** | **CSP instances and the main induction (Zhuk §3)** | 0. *Theorem 0.1:* reductions are safe, and the codimension-one theorem. 1. Instances, reductions, and the three orders. 2. Consistency, paths, linkedness, fragmentation. 3. Induced congruences; adjacency; connected instances. 4. Weakening, cruciality, and termination. 5. Expanded and tree coverings; (p1)–(p8). 6. The nine auxiliary lemmas of §3.2. 7. The bridge lemma. 8. **The main inductive claim, split in two, with the measure and the phase order written out.** 9. PC reductions do not kill all solutions. 10. The two target theorems. | **130** |
| **V** | **The algorithm** | 0. *Theorem 0.1:* `solve_sound` ∧ `solve_total` ∧ `solve_poly`. 1. The constraint language `Γ` and its closure properties. 2. Decidability of every test. 3. The algorithm, with the four simplifications and two repairs. 4. Correctness of the consistency checks (Lemmas 5.3, 5.4, incl. well-definedness). 5. The linear case and Lemma 7.20. 6. Termination: the measure `μ`. 7. The cost model, as a definition; the depth bound with the FLAG-DEPTH repair; **the Remark stating precisely what gap remains to `∈ P`**. | **60** |
| | | **total** | **460** |

Volume I chapters 1 and Volume II chapter 1 are **revisions of the existing
`zhuk_centers.tex`**, not new writing — the existing 27 pages fold in almost unchanged, which is
why Volume II is cheaper than its content suggests.

### 5.3 Blueprint-specific obligations that must not be skipped

* Volume I must open with the **`p ∣ n − 1`** convention and the **definition of dimension**,
  both of which the source lacks and both of which are consumed everywhere downstream.
* Volume III must open with a `Convention` resolving the type parameter `T ∈ {BA,C,S,PC,L,D}`
  (`main.tex:1644`), which makes dozens of the paper's lemmas implicitly polymorphic over `T`
  with clauses that are **not uniformly true** — `LEMBACenterSImplyFactor`'s proof literally reads
  "for `T=C` see Lemma 6.8 in [zhuk2021strong], for `T=S` it is just a combination". This is the
  single largest quantifier-discipline hazard in the project.
* Volume III chapter 6 (mixed essentiality) is **new mathematics not in any source**. It must be
  drafted first, reviewed hardest, and formalized before anything in chapters 7–9 is written,
  because the entire §5 dependency structure is circular without it.
* Volume IV chapter 8 must state the induction hypothesis as a single explicitly quantified
  conjunction, with the measure named and the (A)-uses-(B)-at-the-same-level phase order spelled
  out, **before anyone opens an editor** — the discipline `zhuk_centers` Remark 7.2 applied to
  the doubling lemma's Step 1, where the Lean confirmed that "written in the source's order it
  does not typecheck".
* Every volume's Appendix D (concordance) gets one row per source statement of *every* paper in
  the transitive closure, with the difference column admitting weakenings.
* Appendix A must be replaced by a **real, acyclic dependency graph** (via `leanblueprint`),
  not the prior art's syntactic cross-reference index. That means forward references must be
  *eliminated*, not merely disclosed — a stricter drafting discipline than the prior art used,
  and the thing that makes parallel module assignment possible.

---

## 6. HONEST SCOPE

### 6.1 The milestone ladder

| | Milestone | Deliverable | New lines | Cum. | P-M (conv.) |
|---|---|---|---:|---:|---:|
| **M1** | Classical prerequisite layer (Parts 0–2) | **Barto–Kozik Absorption Theorem**, **Loop Lemma**, **Siggers terms**, **finite abelian Taylor ⟹ affine**, plus the congruence/quotient/relations infrastructure | 10,130 | 10,130 | 7 |
| **M2** | **The Ubiquity theorem** (+ Part 3) | *Every `B ⋘ A` with `\|B\| > 1` has a proper subuniverse of type BA, central, linear, or PC*, plus Informal Claim 1 | 7,550 | 17,680 | 12 |
| **M3** | Reductions are safe (+ Part 4 minus Codim) | `THMCSPDReductionsAreSafe` — the loop invariant of Zhuk's algorithm | 9,900 | 27,580 | 19 |
| **M4** | **L0 complete** (+ Codim) | `THMCodimensionOneTheorem` | 700 | 28,280 | 19.5 |
| **M5** | **L1** (+ Part 5) | `solve_sound`, `solve_total` | 5,000 | 33,280 | 23 |
| **M6** | **L2** (+ Part 6) | `solve_poly` in a stated cost model; seed-relative hardness wrapper | 550 | 33,830 | 23.5 |
| **H** | Hardness track (optional, parallel) | `gadgetReduction_of_no_wnu`; `csp_npHard_of_no_wnu` given the seed | 9,000 | 42,830 | 30 |

Add **8–12 person-months** for the blueprint (~460 pages at ~1.1× the Lean line count in LaTeX,
plus the review loop). **Total for L0+L1+L2: 33–38 person-months at conventional rates
(~1,500 finished Lean lines / P-M for research-level material with no library support).**

**Calibration caveat, stated both ways.** The one measured data point in this project — 1,603
sorry-free Lean lines plus a 1,830-line eight-draft blueprint in ~24 hours wall clock, agent-assisted —
implies a throughput perhaps 20–40× the conventional rate. If that holds at scale, L0 is
6–18 months rather than three years. It almost certainly does not hold at scale: the centre
theorem's proofs average ~25 source lines, whereas Parts 3–4 contain proofs of 141, 175, 205, 209
and 427 source lines whose case analyses do not decompose the same way, and the prior art's rate
was measured on a *leaf* theorem with maximal Mathlib support, no congruences, no quotients,
after eight drafts, six review rounds and **two independent formalizations**. **Plan for the
conventional estimate; treat the agent multiplier as upside, not as the plan.**

### 6.2 What is realistically finishable, and what is not

**Realistically finishable:** M1 and M2. Together they deliver, in Lean, four named classical
theorems that no proof assistant currently has plus Zhuk's fundamental structural theorem, in
17–18k lines of pure universal algebra with no CSP-instance combinatorics, no algorithm, no
complexity, and no executable content. Every one of these is independently citable and
Mathlib-adjacent.

**A multi-year project:** M3–M6. Part 4 alone is 10,600 lines dominated by three proofs (the
bridge lemma, the main inductive claim, and PC survival) that together carry two genuine gaps the
formalizer must close, four separate termination arguments the paper does not give, and an
induction whose measure and phase structure are nowhere written down. This is where a
formalization stalls if it stalls.

**Never:** `CSP(Γ) ∈ P`, NP-completeness in the standard sense, Cook–Levin. Building `P` and `NP`
honestly means a machine model, a time measure, closure of polytime under composition (an open
`proof_wanted` in Mathlib itself), and Cook–Levin — the last of which exists only in Isabelle,
at a scale comparable to this entire project. **If the project's stated goal contains the phrase
"NP-complete", renegotiate it to the seed-relative form of §2.3 before the blueprint is written,
or the goal is unreachable.**

### 6.3 The best defensible milestone

**M2 — the Ubiquity theorem.** Reasons, in order:

1. It is a **clean, quotable, self-contained universal-algebra theorem** — Zhuk's "one of four
   cases" — that a reader can evaluate without knowing anything about CSP.
2. It requires **no CSP-instance machinery at all**: no instances, no coverings, no crucial
   instances, no expanded coverings, no algorithm, no complexity.
3. Getting there **discharges 2404's two hardest external imports** (the Absorption Theorem and
   abelian ⟹ affine) as named theorems that stand on their own.
4. It **fails gracefully**: if the project stops after Part 2, M1 is already four citable
   theorems; if it stops inside Part 3, the bridge and linear-congruence chapters are still
   independently meaningful.
5. It is the honest boundary between "universal algebra Mathlib should have" and "a
   research-scale formalization of one paper".

**Immediate next action: write the Volume II blueprint (M1) first**, as `brady_absorption.tex`
alongside `zhuk_centers.tex`, in the same style, covering Brady `csp.tex` §8540–8859,
§9822–10127, §10443–10669, §10670–10854 and §4235–4706. It extends the finished work, it
discharges the two hardest imports, every theorem in it is independently citable, and — decisively —
**it is the only way to find out whether the observed throughput survives contact with harder
material before committing to Zhuk §2/§3.** Volume I's congruence chapters can be drafted in
parallel, since Volume II needs congruences only in its last three chapters.

### 6.4 Critical path

```
Congruence ──► Quotient ──► Correspondence ──┐
                                             ├──► StableUnder ──► Irreducible/σ* ──┐
Relations ───────────────────────────────────┘                                     │
                                                                                   ▼
zhuk_center [DONE] ──► PPAbsorption ──► BinCentral ──► AbsorptionTheorem ──┐   Bridges
                                                                          │       │
Abelian ──► Malcev ──► AbelianAffine ═════════════ (long pole 1) ═════════─┼──► Linear
                                                                          │       │
                                                                          ▼       ▼
                                              Types/Chain ──► Propagation ──► Essentiality (new)
                                                                                  │
                                                                                  ▼
                                                             Intersection (Thm 21 / Cor 22)
                                                                                  │
                                                                                  ▼
                                                    MultiType ──────────────► Ubiquity  ◄── M2
                                                                                  │
Instance/Defs, Consistency, InducedCon, Weakening, Covering ──────────────────────┤
   (parallelizable early against a sorry-ed §2 interface)                         │
                                                                                  ▼
                                                              Instance/Aux ──► Instance/Bridge
                                                                                  │
                                                                                  ▼
                                          Main/Inductive ═══ (long pole 2) ═══════┤
                                                                                  ▼
                                                          Main/Safe ◄── M3 ──► Main/Codim ◄── M4
                                                                                  │
                                                                                  ▼
                                                        Algorithm/* ◄── M5 ──► Complexity/* ◄── M6
```

**Two long poles.** (1) `AbelianAffine` — the largest genuinely new prerequisite, the only one
with zero partial credit from `zhuk-lean`, and it drags in Mal'cev algebras via 472 lines of
Brady. If it slips, everything downstream of `LEMLInearOnTheTopIsEasy` slips.
(2) `Main/Inductive` — 427 source lines, a simultaneous induction whose proof of part (2) invokes
the IH for part (1) and vice versa, with two genuine gaps.

**What parallelizes.** Part 1's thirteen files are mostly independent of one another after
`Congruence`/`Quotient`. Part 2's `AbsorptionTheorem` chain and its `AbelianAffine` chain are
independent. All of `Zhuk/Instance/{Defs,Consistency,InducedCon,Weakening,Covering}` can be built
against a `sorry`-ed Part 3 interface from day one — writing `Algorithm/Sound` early, even fully
`sorry`-ed, is worth doing precisely because it *forces* the four main theorems to be stated with
exactly the right hypotheses. The optional hardness track shares only the strong-subalgebra API
and can run entirely in parallel by a second person.

---

## 7. PRE-FLIGHT: defects that must be resolved before drafting

These are not risks to monitor; they are **decisions to make**, and several determine the data
layout. Every one was verified against the source by the survey.

### 7.1 Blockers — the paper is wrong or incomplete

1. **Corollary 15 (`CORPropagationModuloCongruence`, `main.tex:1682`) is stated, used six times
   (four inside §5, one in §3), and never proved or restated anywhere.** It is Lemma 14 specialized
   to the canonical surjection `A ↠ A/δ`, but the paper never says so. Supply the derivation,
   taking care that item (m)'s "`B/δ` is S-free" matches (fm)'s "`f(B)` is S-free".
2. **The §5 citation cycle.** Lemma 9 ⇒ Lemma 7 ⇒ Lemma 86 ⇒ Lemma 85 ⇒ Corollary 22 ⇒
   Theorem 21 ⇒ Lemma 8 ⇒ Lemma 9, closed at `StrongSubalgebras.tex:1214` where Lemma 85's `T=C`
   case invokes Corollary 22. Nothing in §5.4 or §5.7 can be formalized until this is broken. The
   break is the **mixed essentiality lemma** for three distinct central (hence ternary absorbing)
   subuniverses — not in the paper.
3. **Theorem 21(c) / Corollary 22(c) assert `n = 2` for type C with no supporting argument.** The
   proof reduces to pairs and shows all types agree, and `σ₁ = σ₂` forces `n = 2` for PC, but
   nothing rules out `n ≥ 3` with all types C. A Lean statement copying the paper is unprovable.
   Same fix as (2).
4. **Lemma 19 (`LEMBACenterImplies`) is false as printed.** The cited sources (Zhuk 2021
   Cor 6.1.2 / 6.9.2) both require `pr₁(R) = A₁` and, for the BA case, a single common absorbing
   term shared by all `Cᵢ`. Counterexample to the printed form: `R = {(0,0)} ≤ Z_p × Z_p` with
   `Cᵢ = Aᵢ` gives `pr₁ = {0}`, not a BA subuniverse of `Z_p`, contradicting the paper's own
   Lemma 29. Restate with both hypotheses.
5. **`LEMConnectedProperties`(a) applies `LEMBridgeFromRelation` without its third hypothesis**,
   which can fail — explicit witness `R = {(x,z,y) ∈ Z₄ × Z₂ × Z₄ : x ≡ z ≡ y (mod 2)}`. Zhuk's
   original supplied the tuples from *criticality*, a notion 2404 deleted. Fix: add "every
   constraint relation is critical" to the definition of *connected* (available, since crucial ⟹
   critical), at the cost of re-importing roughly one page of the original's machinery.
6. **Theorem 44's hypothesis 2 says "`D_{x_i}` is `S`-free" but the proof needs "no nontrivial BA
   or central subuniverse on `D_{x_i}`"** — the commented-out gloss, and what Informal Claim 3
   says. `S`-free is strictly weaker. Strengthen the hypothesis.
7. **`LEMMinimalContainingIsMinimal` is commented out of the source** (`main.tex:1864–1870`, and
   its citation at `:2527`) yet is genuinely needed at `main.tex:3527`. True, but must be
   re-proved.
8. **Two genuine gaps in Theorem 41.** (H2) In Case 1 the IH gives (1c) relative to `D^(2)` but
   the goal is (1c) relative to `D^(1)`; the paper writes only "we derive the required
   conditions". (H14) Both endgames conclude "(1b) if the solution set is subdirect, (1c)
   otherwise", but (1c) demands a **linked** connected subinstance and only "connected" was
   proved; linkedness must be extracted from irreducibility, with a fragmentation descent and the
   empty-solution-set case.
9. **`FindEquationsNonlinked` (1704:711) initialises `I := {1}` instead of `∅`,** losing
   equations — explicit two-variable counterexample. Moot under the recommended simplification
   (drop that subroutine in favour of 2404's (p2)), but must be recorded.
10. **The depth bound `|A| + |Γ|` is not established** for the `CheckTuple → SolveNonlinked`
    path. Without the repair the algorithm is not polynomial. See §2.3.

### 7.2 Conventions the paper leaves implicit and we must legislate

11. **`Z_p ∈ 𝒱ₙ` silently requires `p ∣ n − 1`** (`main.tex:1119–1121`). Every "`A/σ ≅ Z_p`"
    carries it as part of its conclusion.
12. **"Dimension" of `∏ Z_{q_i}` with distinct primes is never defined** and there is no field
    over which it is a vector space. Adopt composition length; prove additivity.
13. **`σ*` is a tolerance, not a congruence** (D6). Typing it as `Congruence` collapses the
    linear/PC distinction silently.
14. **The empty-subuniverse discipline** (D7). The empty set is a subuniverse of every idempotent
    algebra and is vacuously absorbing and vacuously central; the `<_S` clause is literally
    universally true as written.
15. **`⋘` is data** (D4).
16. **Two inequivalent definitions of "linked instance"** coexist: `main.tex:551–554` (global
    connectivity, in the informal claim) and `main.tex:2089–2091` (per-variable). The second does
    not imply the first. Use the formal definition and carry `¬Fragmented` separately.
17. **Whether `σ = A²` counts as irreducible** is genuinely ambiguous (the `k = 0`
    empty-intersection reading), and `σ*` does not exist in that case. 2404 drops the word
    "proper" that the original has. Legislate.
18. **The type parameter `T`** (`main.tex:1644`) — see §5.3.
19. **`B/σ` for `B ≤ A` is the image in `A/σ`**, not the quotient of `B`; §5 uses both readings
    interchangeably. Relatedly, `(C₁ ∩ … ∩ C_t)/δ = ⋂ (Cᵢ/δ)` is **false in general** and is
    proved on the fly inside Lemma 14(fm).
20. **`LEMCentralRelationImplies` silently drops a third case** (a nontrivial *projective*
    subuniverse) present in Zhuk 2021 Thm 6.15. The elimination is legitimate under 2404's
    standing Taylor hypothesis via Zhuk 2021 Lemma 3.4, but 2404 never says so. State it as an
    explicit hidden import — and check it against what `zhuk-lean` actually proved.

### 7.3 Known typos that change meaning if transcribed

`main.tex:2100` `Var(C) ⊆ X₁ or Var(C) ⊆ X₁` in the definition of *fragmented* (second must be
`X₂`); `main.tex:2135` undefined macro `\R`; Lemma 14(b) `f⁻¹(B)` should be `f⁻¹(B')`; 14(bt)
superscript `A'` should be `A`; Theorem 21(l) and Cor 22(l) say "a bridge from σ_k **and** σ_l"
(should be "to"); `StrongSubalgebras.tex:1154–1157` prints the symmetrised bridge as
`δ(x₁,x₂,x₅,x₅) ∧ δ(x₃,x₄,x₅,x₆)`, which forces `x₁ = x₂` and makes Lemma 85 vacuous (intended:
`δ(x₁,x₂,x₅,x₆) ∧ δ(x₃,x₄,x₅,x₆)`); `main.tex:2503` cites a nonexistent item "Corollary 18(rm)".
Assume more: the source has not been proof-read at formalization granularity.

### 7.4 Process risks carried over from the prior art

* **Stale cross-references** (verified: nine already stale in a 1,600-line project after two
  commits). Fixed by D11.
* **Hypothesis bundles spelled out verbatim at every use site** (the "no nonempty proper binary
  absorbing subuniverse" hypothesis appears six times in full in `zhuk-lean`). At 2404 scale
  "BA-and-centre-free", the `<_T` family and "in `𝒱ₙ`" must be named predicates from day one.
* **The mixed doubling lemma.** `zhuk-lean` proved only the all-equal specialization; Zhuk's
  Lemma 6.11 is genuinely mixed and downstream consumers need distinct `Cᵢ` on distinct algebras.
  Restoring it means `IsEssential` over a dependent product. Budget 200–300 lines propagating
  into `Essential.lean` — already priced into Part 0.
* **`piStructure`/`prodStructure` are aggressive global instances.** Harmless at 1,600 lines
  (2.6 s build); with towers of quotients, powers, subalgebras and function types at 30k lines,
  instance-search cost needs monitoring and priority tuning.
* **The 2.5× source→blueprint page expansion** was measured against Brady's readable prose;
  against Zhuk's terser prose 3–4× is likelier, which is why the volume estimate is 460 pages and
  why the review loop runs per volume rather than per document.
* **A second independent formalization** found all three of the prior art's simplifications, and
  neither formalization found them alone. At this scale a second full formalization is
  unaffordable; ration it to the two or three riskiest lemmas per volume — `Essentiality`,
  `Intersection`, and `Main/Inductive` are the obvious candidates.
