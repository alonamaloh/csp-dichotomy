# Route selection for a Lean 4 formalization of the CSP Dichotomy Theorem

**Question asked.** Is Zhuk arXiv:2404.01080 really the best route to "the cleanest proof possible"
of the CSP Dichotomy Conjecture, judged by *easiest to formalize in Lean 4 with least prerequisite
theory*? Compared against: Zhuk's original JACM 2020 proof, Bulatov's proof, the minimal-Taylor-algebra
framework, Brady's notes, and anything newer.

**Answer in one line.** Yes for the *skeleton*, but 2404 is not self-contained: it imports 16 numbered
results as black boxes, and the recommended route is a **hybrid — Zhuk 2404 §2–§3 as the spine,
Brady's notes as the proof source for every imported prerequisite, on top of the already-completed
`zhuk-lean`**, which turns out to discharge three of the imports outright and to be the base case of
the two hardest remaining ones.

---

## 0. Calibration data (what we can actually measure)

Everything below is anchored on the one completed data point in this project.

| Artifact | Size | Content |
| --- | --- | --- |
| `/home/alvaro/claude/zeb/zhuk_centers.tex` | 1,830 LaTeX lines | 44 numbered statements (15 def, 16 lem, 5 thm, 4 cor, 2 prop, 2 conventions) + 16 remarks |
| `/home/alvaro/claude/zhuk-lean/` | 1,603 Lean lines, 96 declarations, **sorry-free** | 13 modules on `Mathlib.ModelTheory` (`FirstOrder.Language.Structure` / `Substructure`) |
| Source material | ≈ Brady `csp.tex` §3.8 (partial) + §3.10 (315 lines) | Zhuk's centre theorem + relational description of absorption |
| Elapsed | blueprint 2026-07-30 19:35 → Lean done 2026-07-31 08:45 | 8 blueprint drafts, 2 independent reviewers, ~24 h wall clock, agent-assisted |

Derived ratios, used throughout:

- **≈ 36 Lean lines per blueprint statement**; ≈ 2.2 Lean declarations per blueprint statement.
- **≈ 3 Lean lines per line of Brady's LaTeX** (Brady is verbose; Zhuk is ~2–3× denser per line).
- Blueprint LaTeX ≈ 1.1× the Lean line count.

Two caveats that inflate the numbers when scaling to the dichotomy:
the centre-theorem statements are *small* (typical proof 10–30 source lines), whereas Zhuk 2404's
main inductive claim has a **427-line proof** in a single `\begin{proof}` block; and the centre
theorem needed no CSP-instance combinatorics, no congruence lattice theory, and no `Z_p` layer.

### What Mathlib actually provides (checked on disk, v4.32.2)

Verified at `/home/alvaro/claude/zhuk-lean/.lake/packages/mathlib/Mathlib`:

- **Present and reusable.** `ModelTheory/Basic.lean`, `Substructures.lean`, `Quotients.lean`
  (prestructures → quotient structures, i.e. congruences), `Semantics.lean`, `LanguageMap.lean`,
  `Definability.lean`, `FinitelyGenerated.lean`. This is exactly the "algebra of a signature" layer
  and `zhuk-lean` already runs on it.
- **Absent.** No clone theory, no polymorphisms, no `Pol`/`Inv` Galois connection, no absorption,
  no Taylor/WNU/cyclic terms, no congruence lattice for general algebras, no Tame Congruence Theory,
  no universal-algebra `Con(A)` lattice.
- **Absent — and this is decisive for scoping.** *No computational complexity theory whatsoever.*
  `grep` for `PolyTime|NP-complete|polynomial time` across all of Mathlib returns exactly one
  substantive hit: `Computability/TuringMachine/Computable.lean`, which defines
  `TM2ComputableInPolyTime` (a Turing machine + a polynomial time bound computing a *function*).
  There is **no `P`, no `NP`, no NP-completeness, no polynomial-time many-one reduction, no SAT,
  no Cook–Levin**. (A web search claimed otherwise; the claim is false — I checked the source tree.)

**Consequence.** "CSP(Γ) is in P or NP-complete" is *not* a formalizable target at any reasonable
cost. The formalizable target is the **algebraic core**: the three theorems that make Zhuk's
algorithm correct, plus (optionally) the pp-interpretability side of hardness. See §7.

---

## 1. Option (a): Zhuk arXiv:2404.01080 — "A simplified proof … and XY-symmetric operations"

### Structure and size

Source at `/tmp/.../scratchpad/papers/src2404/`. Totals:

| File | Lines | `lem` + `thm` + `cor` |
| --- | --- | --- |
| `main.tex` | 4,132 | 52 |
| `StrongSubalgebras.tex` (§5, proofs of §2) | 3,144 | 50 |
| `XYSymmetric.tex` (§4) | 1,640 | 20 |
| `necessaryClaims.tex` (§2.4) | 82 | 4 |
| **total** | **8,998** | **126** (96 lem, 16 thm, 15 cor − overlap) |

Plus ~50 definitions, of which ~35 are introduced in §2 alone (I extracted the `\emph{}`-defined
terms: *special* WNU, subdirect, linked, bijective, stable under σ, irreducible congruence, σ*,
bridge, δ̃, perfect linear congruence, parallelogram property, rectangular, rectangular closure,
polynomially complete, absorbing / binary absorbing / ternary absorbing subuniverse, central
subuniverse, BA-and-centre-free, linear congruence, PC congruence, the six types
`<_BA, <_C, <_S, <_D, <_L, <_PC`, the multi-types `MT ∈ {ML, MPC, MD}`, `⋘`, `⋘̇`, S-free,
dividing congruence, adjacent, reflexive bridge).

### §4 (XY-symmetric) is fully separable — cut it

I checked the reference graph mechanically. `XYSymmetric.tex` defines 23 labels; **none** is
referenced from `main.tex` §2/§3, `StrongSubalgebras.tex`, or `necessaryClaims.tex` except from the
introduction, where the theorems are merely *announced*. Conversely `XYSymmetric.tex` consumes 12
labels from §2. So the dependency is one-way: **§4 depends on §2, nothing depends on §4.**

Cutting §4 removes 1,640 lines and 20 statements at zero cost to the dichotomy. **Do this.**

### The decisive finding: 2404 is *not* self-contained

Zhuk 2404 states 16 results as `\begin{lem}[\cite{...}, Lemma N]` — imported, not proved. Ranked
by number of uses inside 2404:

| Uses | Label | Statement | Source |
| --- | --- | --- | --- |
| 11 | `LEMBACenterSImplyPPDefinition` | R defined by pp-formula Φ containing S; Φ' replaces each occurrence of S by S' <_T S (T∈{BA,C}); then Φ' defines R' with R' ≤_T R | Barto–Kazda *Deciding Absorption* Lem 2.9; Zhuk 2005.00593 Lem 6.1, Thm 6.9 |
| 8 | `LEMCentralRelationImplies` | R ≤_sd A×B, C = left centre. Then C is central in A, **or** B has a nontrivial binary absorbing subuniverse | Zhuk 2005.00593 **Thm 6.15** |
| 8 | `LEMBACenterImplies` | R ≤ A₁×…×Aₙ, Cᵢ ≤_T Aᵢ, T∈{BA,C} ⟹ proj₁(R ∩ ∏Cᵢ) ≤̇_T A₁ | Zhuk 2005.00593 Cor 6.1.2, 6.9.2 |
| 5 | `LEMLinkedImpliesBACenter` | R ⪇_sd A×B linked ⟹ a BA or central subuniverse exists on A or on B (**the Absorption Theorem**) | Brady `csp.tex` **Thm 3.11.1** |
| 5 | `LEMExistenceOfTreeCoverings` | existence of tree-coverings realising the maximal 1-consistent reduction | Zhuk 2005.00593 Lem 5.6 |
| 4 | `LEMBridgeComposition` | composition of bridges is a bridge; δ̃ = δ̃₁∘δ̃₂ | Zhuk 1704 **Lem 6.3** |
| 4 | `LEMBACenterSPossibleIntersections` | B <_{T₁} A, C <_{T₂} A, B∩C=∅, Tᵢ∈{BA,C,S} ⟹ T₁=T₂∈{BA,C} | Zhuk 2005.00593 Lem 6.25 |
| 3 | `LEMBuildingPerfectCongruence` | σ irreducible on A∈𝒱ₙ, δ a bridge σ→σ with δ̃ = A² ⟹ σ is perfect linear | Zhuk 1704 **Cor 8.17.1** |
| 2 | `LEMExistenceOfSpesialWNULemma` | idempotent WNU w ⟹ ∃ special idempotent WNU w' ∈ Clo(w) of arity n^{n!} | Maróti–McKenzie Lem 4.7 |
| 2 | `LEMBridgeBetweenCongruences` | ω∩σ₁=ω∩σ₂, ω∖σ₁≠∅ ⟹ ∃ bridge σ₁→σ₂ with δ̃ = σ₁∘σ₂ | Zhuk 1704 Lem 8.19 |
| 1 | `LEMExpandedConsistencyLemma` | expanded covering of a cycle-consistent irreducible instance is cycle-consistent and irreducible | Zhuk 1704 Lem 6.1 |
| 1 | `LemAbsorptionImpliesEssential` | B absorbs A with an n-ary op ⟺ no S ≤ Aⁿ with S∩Bⁿ=∅ and S∩(B^{i−1}×A×B^{n−i})≠∅ ∀i | Barto–Kazda Prop 2.14; Zhuk 2005.00593 Lem 3.2 |
| 1 | `LEMBACenterLinkedness` | R linked, B₁,B₂ absorbing, R∩(B₁×B₂) subdirect ⟹ R∩(B₁×B₂) linked | Barto–Kozik 2012 Prop 2.15(i) |
| 1 | `LEMAbsorbingEquality` | 0_A ⊆ σ ≤ A², ω <_BA σ ⟹ ω ∩ 0_A ≠ ∅ | Zhuk 1704 Lem 7.2 |
| 1 | `LEMAbelianEquivalentDefinition` | A abelian ⟺ ∃ congruence δ on A² with the diagonal as a block | **Hobby–McKenzie**, *Structure of Finite Algebras* (TCT) |
| 1 | `LEMAbelianEqualAffineForWNU` | finite A with a WNU term operation: **abelian ⟺ affine** | **Hobby–McKenzie** (TCT) |

Two more are proved only by "see the cited paper": `LEMBACenterSImplyFactor` ("for T=C see Lemma 6.8
in [zhuk2021strong]") and `LEMBACenterSOnPowerImplies` ("for T∈{BA,C} see Lemma 6.24 in
[zhuk2021strong]; for T=S just repeat the same proof **word to word** replacing BA by S").

> **Formalization hazard, flagged.** `StrongSubalgebras.tex:186–189`: *"For T = S just repeat the
> same proof word to word replacing BA by S."* A word-to-word repetition claim is exactly what a
> proof assistant will not accept. Either the proof genuinely parametrises over T ∈ {BA, C, S}
> (in which case the blueprint should say so and prove it once), or it does not. This must be
> resolved before the module is written.

**So 2404's "simplified proof" is simplified *relative to a large imported base*.** Counting honestly,
the reachable-from-2404 dependency closure is 2404 §1–§3 + §5 (≈ 7,300 lines) **plus** the cited
parts of Zhuk 2005.00593 §5–§6, Zhuk 1704 §6–§8, Barto–Kazda, Barto–Kozik 2012, and two
Hobby–McKenzie results.

### But three of the imports are **already formalized**

This is the pivotal observation.

- `LEMCentralRelationImplies` (2005.00593 **Thm 6.15**, 8 uses) **is exactly the theorem
  `zhuk-lean` proves.** `README.md`: "let `R ≤ A × B` be subdirect, `C = {a ∈ A : {a}×B ⊆ R}`; if
  `B` has a Taylor term and no nonempty proper binary absorbing subuniverse, then `C` centrally
  absorbs `A`". Same statement. Done, sorry-free.
- `LEMCenterImpliesTernaryAbsorption` (2005.00593 Cor 6.11.1) — the ternary-witness half.
  Done (`ZhukLean/Ternary.lean`, `Doubling.lean`).
- `LemAbsorptionImpliesEssential` (Barto–Kazda Prop 2.14) — the relational description of
  absorption. Done (`ZhukLean/Relational.lean`, `Essential.lean`, `Regrouping.lean`).

### And the two *hardest* remaining imports reduce to that same theorem

**(i) The Absorption Theorem.** `LEMLinkedImpliesBACenter` = Brady `csp.tex` Thm 3.11.1, in
§"Absorption Theorem and Loop Lemma" (`csp.tex:10443–10669`, 227 lines, 18 statements). I read the
proof. Brady derives it from **Zhuk's centre theorem plus two short lemmas**:

> `csp.tex:10471`: "…and then we will apply Zhuk's result (Corollary `\ref{zhuk-center}`) to the
> binary relation R ∩ (A × D_n)."

and `zhuk-center` (`csp.tex:10257`) is:

> "Suppose A, B are finite and idempotent. If R ≤_sd A × B has left center C and B is Taylor and
> binary absorption free, then C ⊲_Z A." — proved from `thm-center-implies-absorbing` +
> `thm-center-implies-central`, i.e. **exactly the two halves of `zhuk-lean`.**

The full proof of the Absorption Theorem is then: two bootstrap lemmas (≈ 15 lines each) plus a
three-line main argument (S = R∘R⁻; if S = A², apply the lemmas; else take minimal k with S^{∘k} = A²
and apply to S^{∘(k−1)}). The only other input is `bin-central-criterion` (`csp.tex:10413`), a local
criterion equating binary absorption of a central C with "∀a∉C, ∀c∈C: Sg{a,c} has a proper binary
absorbing subalgebra", proved by induction on |Sg{a,c}| using partial semilattice terms.

**This is the single most valuable finding in this report.** The Barto–Kozik Absorption Theorem —
usually regarded as the hardest classical prerequisite in the whole area, and normally proved by a
long Ramsey-flavoured argument — is, in Brady's presentation, **a short corollary of the theorem this
project has already formalized.** Estimated cost: 600–1,000 Lean lines, not 5,000.

**(ii) Abelian ⟹ affine.** `LEMAbelianEqualAffineForWNU`, cited to Hobby–McKenzie, is proved in
Brady §"Finite abelian Taylor algebras are affine, and Zhuk's four cases" (`csp.tex:10670–10854`,
185 lines, 12 statements), following Barto–Kozik–Stanovský rather than TCT, in three steps:

1. every finite abelian algebra is (hereditarily) absorption free;
2. every finite idempotent Taylor hereditarily-absorption-free algebra is Mal'cev;
3. every abelian Mal'cev algebra is affine — **already done in Brady §`s-abelian-malcev`
   (`csp.tex:4235–4706`, 472 lines).**

So the TCT citation is avoidable; **you never need Hobby–McKenzie, tame congruence theory, or
commutator theory.** Cost: step 3 is the expensive one (it needs Mal'cev algebras and a chunk of
Brady §4235); steps 1–2 are moderate.

### Where 2404 will hurt

Longest proofs, measured by `\begin{proof}`…`\end{proof}` span:

| Lines | Location | Statement |
| --- | --- | --- |
| **427** | `main.tex:3431` | **`THMMainInductiveCSPClaim`** |
| 292 | `StrongSubalgebras.tex:644` | `LEMIntersectionPCLinearIsGood` |
| 205 + 159 | `main.tex:3041`, `2879` | `LEMGetABridgeFromSubdirectPCLinearInstance` (one lemma, two proof blocks) |
| 175 | `StrongSubalgebras.tex:436` | `LEMSelfIntersectionPC` |
| 126 | `main.tex:2605` | `LEMParalPropertyFromCrucialInMultiType` |
| 104 + 101 | `StrongSubalgebras.tex:1573`, `1460` | `LEMPCCongruencePropertyInductiveStep` |

`THMMainInductiveCSPClaim` (`main.tex:3408–3429`) is the monster. It is a **simultaneous induction on
|D^(1)| proving three conclusions at once** — (1a) every constraint has the parallelogram property;
(1b) *or* (1c) a dichotomy about connected linear-type instances vs. expanded coverings with a linked
connected non-subdirect subinstance; and (2) reductions to BA/central types preserve solvability —
where the proof of (2) invokes the inductive hypothesis for (1), and the proof of (1) invokes the
inductive hypothesis for (2). In Lean this must become a single `theorem` with a conjunctive
conclusion and strong induction on a `Finset` cardinality, and the mutual invocation pattern has to
be laid out explicitly in the blueprint before anyone writes tactic code.

Hedge-word audit (whole 2404, 8,998 lines): `obvious` 3, `clearly` 0, `easy to see` 0,
`easy to check` 0, `straightforward` 1, `similarly` 13, `the same way` 2, `word to word` 1,
`can be easily` 2, `It remains to` 20. **Zhuk 2404 is unusually rigorous prose** — far cleaner than
either Zhuk 1704 or Brady (see §5). The 13 `similarly`s and the one `word to word` are the audit list.

Other flagged items:

- `main.tex:1534–1536`: "Sometimes, we also put a congruence there even if T∈{BA,C,S}, which means
  that σ is a full congruence." — a notational convention that silently overloads `<_{T(σ)}`.
  A formalization must decide whether the type carries a σ field that is sometimes junk.
- `main.tex:1628–1637`: empty subuniverses are *excluded* from `⋘` but readmitted via a dotted
  `⊍⋘`. Three parallel dotted notations (`⋘̇`, `<̇_T`, `≤̇_T`). This is precisely the empty-set
  convention that bit the previous project (see `zhuk_centers` README: "Two theorems quantified over
  an unused center element … makes the statement vacuous when C = ∅"). Budget for it explicitly.
- `main.tex:1838–1843` (Remark after `CORMainStableIntersection`): "we can always duplicate the
  coordinate of the relation and apply restrictions separately on different coordinates." — an
  informal transport step used to justify a weaker statement covering a stronger use. Needs a lemma.
- `main.tex:2100`: `Var(C) ⊆ X₁ or Var(C) ⊆ X₁` in the definition of *fragmented* — an obvious
  **typo for `X₂`**. Harmless but shows the source has not been proof-read at formalization
  granularity.
- `main.tex:2135`: `$\R$ does not depend on its i-th variable` — undefined macro `\R`; means `R`.

---

## 2. Option (b): Zhuk's original — arXiv:1704.01914 / JACM 2020

4,563 lines (pdftotext), ~144 numbered statements (73 distinct `Lemma n.m`, 26 `Theorem n.m`, plus
corollaries and definitions). Sections: 1–2 outline, 3 definitions, 4 the algorithm (pseudocode),
5 correctness + Rosenberg completeness + polynomiality, 6 remaining definitions, 7 absorption /
centre / PC / linear congruence, 8 one-of-four reductions / bridges / strategies, 9 existence of next
reduction + linked connected component + the §5 theorems, 10 extensions.

**Advantages over 2404.** It is the only source that contains the *algorithm itself*, its
polynomial-time analysis (Lem 5.2: recursion depth < |A|+|Γ|), the correctness of the auxiliary
functions, and the reduction to the idempotent core. It is also more self-contained: 2404 cites *it*
five times, never the reverse.

**Disadvantages, and they are decisive.** Zhuk himself explains why he rewrote it
(`main.tex:450–464`):

> "The crucial disadvantage of this approach is that the linear subalgebras we obtain only exist
> locally, whereas the properties we want to prove are global. … As a result, we are forced to go
> forward and backward from global {0,…,99} to local {0,1}, and use a **very complicated induction**
> to prove most of the claims."

A "very complicated induction" that the author replaced is the worst possible formalization target.
Hedge density is also worse: `obvious` 6, `easy to see` 4, `clearly` 1, `similarly` 16,
`the same way` 10 — in half the line count of 2404.

**Verdict.** Not the spine. But **do not discard it**: §4 (the algorithm), §5.2 (polynomiality),
§5.3 (auxiliary function correctness), and §10 are the only place several things are written down,
and 2404 cites 1704 Lem 6.1, Lem 6.3, Lem 7.2, Cor 8.17.1, Lem 8.19 as black boxes that a complete
formalization must eventually reach into.

---

## 3. Option (c): Bulatov, arXiv:1703.03021 (coloured graphs / centralisers)

Assessed from the literature (not fetched in full; the local corpus does not contain it).

**Against, strongly:**

1. **It rests on Tame Congruence Theory.** Bulatov's coloured graph assigns to each pair of elements
   a TCT type (semilattice / majority / affine), which presupposes Hobby–McKenzie's classification of
   minimal algebras and the whole localisation apparatus. Formalizing TCT is a multi-year project in
   its own right and there is no partial Lean/Coq/Isabelle work on it. By contrast, the Zhuk route
   **can avoid TCT entirely** (see §1(ii)).
2. **Centralisers and congruence separation** add a second layer of commutator-theoretic machinery
   on top of TCT.
3. **No comparably rigorous rewrite exists.** 2104.11808 §3 recovers Bulatov's *starting point* as a
   corollary of an elementary pp-definability theorem, but does not reprove his main development.
4. **Reception.** Bulatov's proof has been independently checked less thoroughly than Zhuk's; the
   literature I surveyed records no *identified* gap, but also no equivalent to Zhuk's own simplified
   rewrite. Zhuk's is the one that has been re-derived from scratch by its author and partially
   re-verified in bounded arithmetic (§6).

**Newest development, and it is real.** **arXiv:2604.05231**, *"The colored edge theory of A. Bulatov
and binary absorption in minimal Taylor algebras"*, Brady, Đapić, Marković, Prokić, Uljarević,
submitted **6 April 2026**:

> "We find a new definition of colored edge graphs of finite algebras in the case of minimal Taylor
> algebras, a definition which includes the graphs invented by A. Bulatov. Next we proceed to reprove
> the main results of A. Bulatov's theory in the case of minimal Taylor algebras and in our setting,
> finding several simplifications compared to the more general case of smooth algebras Bulatov
> considered."

This makes Bulatov's *theory* substantially cleaner — but (i) it reproves the *algebraic* theory, not
the dichotomy; (ii) it buys the simplification by restricting to minimal Taylor algebras, which
imports the cyclic term theorem (§4); (iii) it is four months old with no independent verification.

**Verdict: rank last.** Revisit in 2–3 years if the minimal-Taylor reconstruction of Bulatov matures.

---

## 4. Option (d): the minimal-Taylor-algebra framework (2104.11808) — evaluating Zhuk's own claim

Zhuk's claim, `main.tex:1055–1057`:

> "Moreover, many definitions and statements could be simplified if we consider only Taylor minimal
> algebras (see [minimaltayloralgebras]), which would be sufficient to prove two main results of this
> paper."

He mentions minimal Taylor algebras exactly **three times** in 8,998 lines (`main.tex:839`, `1056`,
`1361`), which already tells you the claim is an aside, not a worked plan.

### What the restriction genuinely buys

From Barto–Brady–Bulatov–Kozik–Zhuk (TheoretiCS 3 (2024) art. 14, 76 pp.), §5:

- **Thm 5.5.** Every absorbing set of a minimal Taylor algebra is a *subuniverse*. (False in general.)
- **Thm 5.7.** For minimal Taylor A: `B` 2-absorbs A ⟺ `R(x,y,z) = B(x)∨B(y)∨B(z)` is a subuniverse
  of A³ ⟺ `B` projective ⟺ `B` **strongly** projective. So binary absorption acquires an arity-3
  relational description and the strongest possible closure form.
- **Thm 5.10.** For minimal Taylor A: `B` 3-absorbs A ⟺ `R(x,y) = B(x)∨B(y)` is a subuniverse of A²
  ⟺ `B` is a **centre**. *This is exactly the collapse Zhuk points at in `main.tex:1360–1361`:*
  "In general ternary absorption does not imply central subuniverse, but they are equivalent for
  minimal Taylor algebras."
- **Prop 5.9.** B ⊴₂ A, C ≤ A ⟹ B∪C ≤ A; B ⊴₂ A, C ⊴ A by f ⟹ B∪C ⊴ A by f and B∩C ≠ ∅ and
  B∩C ⊴ A by f; ⊴₂ is transitive; A has a *unique* minimal 2-absorbing subalgebra.
- **Prop 5.4.** Subalgebras, finite powers and quotients of minimal Taylor algebras are minimal Taylor
  — so the class is closed under everything the proof does.
- **Thm 5.23 / 5.24.** A single ternary term witnesses every edge and every 2- and 3-absorption, and
  generates the whole clone.

These would hit `StrongSubalgebras.tex` §"Subuniverses of types BA, C, S" (18 lemmas, 276 lines)
hardest, and would simplify `LEMBACenterSPossibleIntersections`, `LEMBACenterImplyIntersection`,
`LEMBACenterSImplyFactor`, `LEMBACenterSOnPowerImplies` and the whole S-type bookkeeping. Zhuk's `S`
type ("simultaneously BA and central") plausibly **disappears** in the minimal Taylor world, and with
it a fair fraction of the six-type case analysis.

Realistic saving: **perhaps 20–30 % of the §2 machinery.** Not more, because §3 (CSP instances,
coverings, crucial instances, the main induction) is untouched by the restriction, and §3 is roughly
half the work.

### What it costs — and this is the killer

Every minimal-Taylor result in 2104.11808 runs through **Theorem 3.5**, the **cyclic term theorem**
of Barto–Kozik:

> "The following are equivalent for any algebra. A is Taylor. There exists n > 1 such that A has an
> n-ary cyclic term operation. For every prime p > |A|, A has a p-ary cyclic term operation."

Proposition 5.2 ("every Taylor algebra has a minimal Taylor reduct") is proved
(2104.11808 line 2147) by: take a p-ary cyclic term; consider the finite family of clones generated
by such cyclic operations; choose a minimal one; if its algebra had a proper Taylor reduct it would
have a p-ary cyclic term by Theorem 3.5, contradiction. **The reduction to minimal Taylor algebras is
a corollary of the cyclic term theorem and cannot be obtained more cheaply.** Propositions 5.3, 5.4,
Theorems 5.5, 5.7, 5.10, 5.23, 5.24 all invoke it again directly.

The cyclic term theorem is proved in Brady §"Cyclic terms" (`csp.tex:14873–15083`, 211 lines) — but
that section sits at line 14,873 of the notes and depends on the whole preceding absorption and
bounded-width development, including the Absorption Theorem itself. Formalizing it means: the
multiplicative property of cyclic terms; the "semantic meaning" characterisation (V has no m-ary
cyclic term ⟺ ∃ A, σ with σ^m = 1 fixed-point-free, via the free algebra F_V(x₁,…,x_m) and the
cyclic-shift automorphism — **note this constructs a free algebra on m generators, an infinitary
object Mathlib's `ModelTheory` does not currently hand you**); then the main Barto–Kozik argument.

Estimated cost of the cyclic term theorem alone: **3,000–6,000 Lean lines**, on top of the Absorption
Theorem.

**Contrast with what 2404 actually needs.** 2404 does **not** use cyclic terms. It uses **special
WNU** (`main.tex:1079–1082`, `necessaryClaims.tex:5–8`):

> `w(x,…,x,y) = w(x,…,x,w(x,…,x,y))`, existing in `Clo(w)` at arity n^{n!} for any idempotent WNU w
> (Maróti–McKenzie Lem 4.7).

That is an iteration/pigeonhole argument on a finite set — **an order of magnitude cheaper** than the
cyclic term theorem.

### Verdict on (d)

**The claim is true but the trade is bad.** Restricting to minimal Taylor algebras would save
maybe 20–30 % of Zhuk §2 and buy nothing in §3, at the price of importing the cyclic term theorem,
free algebras on m generators, and a 76-page paper whose §5 proofs are themselves stated at survey
granularity ("(link to proof)" pointing into §9). Net: **it makes the formalization bigger, not
smaller.**

**Use it as a source of *lemma statements*, not as the framework.** Specifically, Thm 5.10
(3-absorption ⟺ centre) is worth knowing about because it tells you which of Zhuk's two notions is
the "right" one; and if a later phase of the project needs Bulatov's theory, 2604.05231 + minimal
Taylor is the way in.

---

## 5. Option (e): Brady's notes, `/home/alvaro/claude/zeb/csp.tex`

17,747 LaTeX lines, 61 sections. Self-described status (`csp.tex:9`):

> "Currently these notes are in an unfinished state - maybe half way through the material needed for
> the CSP dichotomy for finite structures, with much more planned if that is ever finished."

The notes stop at conservative CSPs and Maróti's reduction. There is **no Zhuk-algorithm correctness
proof, no Bulatov completion** (§"Bulatov's colored graph" is 167 lines, an introduction only).
So Brady cannot be the spine.

**But Brady is by far the best proof source for the prerequisite layer**, and the section-size table
makes the case:

| `csp.tex` lines | Section | Role for us |
| --- | --- | --- |
| 8540–8859 (320) | Absorption, Jónsson absorption, and connectivity | prerequisite |
| 8860–9821 (962) | Absorption and B-essential relations | **partly formalized** (`Relational.lean`, `Essential.lean`, `Regrouping.lean`) |
| 9822–10127 (306) | Finding an arc-consistent absorbing subinstance | prerequisite |
| **10128–10442 (315)** | **Zhuk's centers and ternary absorption** | **FORMALIZED — `zhuk-lean`** |
| **10443–10669 (227)** | **Absorption Theorem and Loop Lemma** | = 2404's `LEMLinkedImpliesBACenter`; derived from the line above |
| **10670–10854 (185)** | **Finite abelian Taylor algebras are affine** | = 2404's Hobby–McKenzie import |
| 4235–4706 (472) | Abelian Mal'cev algebras are affine | step 3 of the line above |
| 14873–15083 (211) | Cyclic terms | only if you take route (d) |
| 15084–15720 (637) | Minimal Taylor clones | only if you take route (d) |

**Where Brady is cleaner than Zhuk.** (1) The Absorption Theorem — Brady's derivation from Zhuk's
centre theorem is dramatically shorter than Barto–Kozik's original. (2) Abelian ⟹ affine —
Brady routes around Tame Congruence Theory. (3) The relational description of absorption — already
proven better in practice, since it is what the completed Lean project used. (4) Motivation and
worked examples throughout, which matter for writing a blueprint.

**Where Brady is worse.** Hedge audit over 17,747 lines: `similarly` 102, `TODO` **54**,
`exercise` 32, `obvious` 25, `easy to check` 22, `clearly` 18, `easy to see` 12, `left to the reader` 1.
That is roughly **6× Zhuk 2404's hedge density per line**. Brady's notes are readable *because* they
are informal. Every section pulled from Brady needs the same blueprint treatment `zhuk_centers.tex`
gave §3.10 — and recall that treatment took **eight drafts and two reviewers** and found real defects
(missing term substitution, two vacuous quantifications, an ordered-product/indexed-product mismatch).

**Verdict.** Not the spine; **the proof source for every import**. This is half of the recommended
hybrid.

---

## 6. Option (f): anything newer (2024–2026), and existing formalizations

### Newer mathematics

| Ref | Date | What | Relevance |
| --- | --- | --- | --- |
| **arXiv:2604.05231** | Apr 2026 | Brady, Đapić, Marković, Prokić, Uljarević — *The colored edge theory of A. Bulatov and binary absorption in minimal Taylor algebras*. Reproves Bulatov's main results for minimal Taylor algebras, "finding several simplifications" | Best hope for route (c), but 4 months old, unverified, and needs cyclic terms |
| **arXiv:2503.03551** | Mar 2025, rev. Jan 2026 | Ross Willard — *Zhuk's bridges, centralizers, and similarity*. Second of a **three-paper series**; first is arXiv:2502.20517 (*Abelian congruences and similarity in varieties with a weak difference term*, "similarity bridges") | Extends Zhuk's bridges to arbitrary meet-irreducible congruences; proves Zhuk's bridges and similarity bridges "convey the same information in locally finite Taylor varieties". **Explanatory, not a shortcut** — makes no claim that any component of Zhuk's proof is redundant. Worth reading before writing the bridge module; may suggest a cleaner definition |
| **arXiv:2604.06335** | Apr 2026 | Barto, Hadek, Zhuk — *Toward a Uniform Algorithm and Uniform Reduction for Constraint Problems* (present in the local corpus, unmentioned in the task) | **Not a dichotomy proof.** Minion-theoretic characterisation of k-consistency / Sherali–Adams / affine IP hierarchies; a new Z_p vector relaxation solving the D₄ CSP. Confirms Singl(BLP+AIP) is *not* a uniform algorithm (Kompatscher's D₄ example fools it; correct only for domains ≤ 7). **Read as evidence that no simple uniform algorithm is about to replace Zhuk's** — i.e. no cheaper route is imminent |
| arXiv:2104.11808 | v6, May 2024 | Minimal Taylor framework | See §4 |
| arXiv:2310.00514 | rev. Oct 2024 | Kátay, Tóth, Vidnyánszky — *The CSP Dichotomy, the Axiom of Choice, and Cyclic Polymorphisms* | About the **infinite** compactness statement K_𝒟 (equivalent to BPI when no cyclic polymorphism, strictly weaker otherwise). **Does not** affect the finite-domain dichotomy or its formalization. Noted so it is not over-read |
| notzeb.com/csp.html | last updated **2019** | "Royal road to the CSP" — a reading guide, not a proof | Not useful |

**No 2024–2026 source supersedes Zhuk 2404 as a route to the dichotomy.** 2404 (v2, Oct 2024) remains
the most recent complete, self-described-as-simplified proof.

### Existing formalizations — exhaustive search result

| Target | Status |
| --- | --- |
| CSP dichotomy, any prover | **Nothing.** GitHub repository searches for CSP + dichotomy + Lean/Coq/Isabelle return zero results |
| Schaefer's theorem | **Nothing** in any prover |
| Post's lattice / clone lattice | **Nothing** |
| Polymorphism clones, Pol/Inv Galois connection | **Nothing** |
| Absorption theory, Taylor terms | **Nothing** except `zhuk-lean` (this project) |
| **Universal algebra generally** | **`agda-algebras`** (ualib.org, DeMeo & Carette): a complete machine-checked constructive proof of **Birkhoff's HSP / variety theorem** in Martin-Löf type theory (`Demos/HSP.lagda`, `Setoid/Varieties/HSP.lagda`), TYPES 2021 / arXiv:2101.10166. Also Birkhoff completeness for multi-sorted algebras in Agda (arXiv:2111.07936) |
| Bounded-arithmetic formalization of *Zhuk specifically* | **Azza Gaysin**, arXiv:2201.00913 (*Proof complexity of CSP*, 2022) and **arXiv:2403.06704** (*Proof complexity of universal algebra in a CSP dichotomy proof*, Mar 2024, + Charles Univ. PhD thesis). Shows the **soundness of Zhuk's algorithm** is provable in bounded arithmetic V¹ + three universal-algebra axiom schemes, and in W¹₁; specifically formalizes "after reducing some domain of an instance to its strong subuniverses, a satisfiable instance maintains a solution" — i.e. **Informal Claim 2 / `THMCSPDReductionsAreSafe`** |
| Complexity-theory substrate | **Isabelle/AFP `Cook_Levin`** (Frank J. Balbach, current version dated Apr 2026): multi-tape TMs, P, NP, poly-time many-one reduction, SAT, and the Cook–Levin theorem. **Not portable to Lean.** Mathlib has none of this |

**Reusability assessment.**

- `agda-algebras` is **not reusable as code** (different prover, different foundations: setoid-based
  MLTT vs. Lean's `Prop`/quotients). It *is* reusable as a **design reference** for the signature /
  term / free-algebra layer, and as evidence that the foundations layer is genuinely tractable
  (Birkhoff HSP was done by two people).
- Gaysin's work is **not reusable as code** (bounded arithmetic, not a proof assistant) but is
  **directly reusable as a blueprint**: it is the only existing rigorous, gap-hunting re-derivation of
  a component of Zhuk's proof, and it targets exactly `THMCSPDReductionsAreSafe`. **Read arXiv:2403.06704
  before writing that module.**
- `Cook_Levin` proves the point that the complexity wrapper is a separate, enormous project.
- **`zhuk-lean` is the only reusable Lean code in existence for this area, and it is ours.**

---

## 7. What "the CSP Dichotomy Theorem" can actually mean as a Lean target

This must be settled before the module architecture is drawn. Three candidate targets:

**T1 — full statement.** "CSP(Γ) ∈ P if Γ has a WNU polymorphism; NP-complete otherwise."
Requires P, NP, NP-completeness, poly-time many-one reductions, and NP-hardness of NAE-3SAT
(Zhuk 2005.00593 §5.3 proves hardness by pp-reducing NAE3 to Γ′, citing NAE-3SAT NP-hardness as
"known [27]" — a black box needing Cook–Levin). **Mathlib supplies none of this.** Balbach's Isabelle
Cook–Levin is a multi-year effort. **T1 is out of reach; do not attempt.**

**T2 — algorithmic core (recommended).** The three theorems that make Zhuk's algorithm correct,
stated purely algebraically, with no complexity vocabulary:

- `THMCSPDReductionsAreSafe` (`main.tex:3985`): *Θ cycle-consistent irreducible, B <_T^{D_x} D_x with
  T ∈ {BA, C, PC}. Then Θ has a solution iff Θ has a solution with x ∈ B.*
- `LEMUbiquity` (`main.tex:1653`): *B ⋘ A, |B| > 1 ⟹ ∃ C <_T^A B with T ∈ {BA, C, L, PC}.*
  (Its proof, `StrongSubalgebras.tex:2301`, is 8 lines given `LEMMainExistenceOfIrreducibleCongruence`
  at `StrongSubalgebras.tex:2185` — that lemma is where the real content lives.)
- `THMCodimensionOneTheorem` (`main.tex:4004`): the codimension-one theorem — the solution set,
  pulled back along φ: ∏Z_{q_i} → ∏D_{x_i}/σ_{x_i}, is empty, full, or an affine subspace of
  codimension 1.

Anyone can then read off that the algorithm is correct; the *"is in P"* half is a separate,
uncontroversial, unformalized statement. **This is the honest, defensible target.**

**T3 — T2 plus the algorithm as a Lean function** with a termination proof and a `Nat`-valued step
bound, without claiming polynomiality in a machine model. A nice extra; low priority.

---

## 8. Recommended route, and size estimate

### The recommendation

> **Zhuk 2404 §1–§3 + §5 as the spine (cut §4 entirely); Brady `csp.tex` as the proof source for
> every prerequisite 2404 imports; `zhuk-lean` as the existing base; target T2.**

Concretely, the imports resolve as follows:

| 2404 import | Where it comes from | Status |
| --- | --- | --- |
| `LEMCentralRelationImplies` (8 uses) | `zhuk-lean` | **done** |
| `LEMCenterImpliesTernaryAbsorption` | `zhuk-lean` | **done** |
| `LemAbsorptionImpliesEssential` | `zhuk-lean` | **done** |
| `LEMLinkedImpliesBACenter` (Absorption Thm) | Brady §10443, from the above | short |
| `LEMAbelianEqualAffineForWNU` | Brady §10670 + §4235 | medium-large |
| `LEMAbelianEquivalentDefinition` | Brady §10670 (definitional) | short |
| `LEMBACenterSImplyPPDefinition` (11 uses) | Barto–Kazda / Brady §8860 | medium |
| `LEMBACenterLinkedness` | Barto–Kozik Prop 2.15(i) / Brady §8540 | short |
| `LEMExistenceOfSpesialWNULemma` | Maróti–McKenzie Lem 4.7 (elementary) | short |
| `LEMBridgeComposition`, `LEMBuildingPerfectCongruence`, `LEMBridgeBetweenCongruences` | Zhuk 1704 §6, §8; cross-check against Willard arXiv:2503.03551 | medium |
| `LEMExistenceOfTreeCoverings` (5 uses), `LEMExpandedConsistencyLemma`, `LEMAbsorbingEquality`, `LEMBACenterSPossibleIntersections` | Zhuk 2005.00593 §5–§6, Zhuk 1704 §6–§7 | medium |

**Cyclic terms are never needed.** **Tame Congruence Theory is never needed.**

### Size estimate

Component breakdown. Lean lines are the central estimate; person-months use ~1,500 finished Lean
lines / person-month, the conventional rate for research-level material with no library support.
(See the caveat after the table.)

| # | Component | Source | Lean lines | P-M |
| --- | --- | --- | ---: | ---: |
| L0 | **Foundations.** Signatures, term operations, `Clo`, `Sg` with generation-by-terms, finite-index products, congruence lattice `Con(A)`, quotients, projections, pp-formulas, subdirect, linked, WNU / Taylor / special WNU. Extends Mathlib `ModelTheory`; ~600 lines reusable from `zhuk-lean` (`Product.lean`, `Absorbs.lean`, `StarPower.lean`) | Brady §s-definitions, Zhuk §2.1 | 3,000 | 2.0 |
| L1 | **Absorption core (already done).** absorption, binary/central absorption, essential relations, relational description, Zhuk's centre theorem, ternary collapse | `zhuk-lean` | *1,603 done* | *0* |
| L2 | **Absorption core (remaining).** pp-propagation of BA/central (`LEMBACenterSImplyPPDefinition`, 11 uses), `bin-central-criterion`, absorption on powers, Jónsson absorption, `LEMBACenterLinkedness` | Brady §8540, §8860, §9822; Barto–Kazda | 2,000 | 1.4 |
| L3 | **Absorption Theorem + Loop Lemma** | Brady §10443 (227 ln) | 800 | 0.6 |
| L4 | **Abelian ⟹ affine for Taylor.** 3 steps; incl. Mal'cev algebras and abelian Mal'cev ⟹ affine | Brady §10670 (185 ln) + §4235 (472 ln) | 2,800 | 1.9 |
| L5 | **Special WNU** (Maróti–McKenzie Lem 4.7) | `necessaryClaims.tex:5` | 450 | 0.3 |
| L6 | **Polynomially complete algebras.** PC definition, Lem 7.11–7.14 of Zhuk 1704 | Zhuk 1704 §7.3 | 1,200 | 0.8 |
| L7 | **Z_p / linear layer.** A/σ ≅ Z_p^n, affine subspaces, dimension, linear maps. Mathlib `ZMod` + `Module` help | Zhuk §2, §3 | 700 | 0.5 |
| L8 | **Zhuk §2: irreducible congruences, σ*, bridges, perfect linear congruences, linear vs PC** | `main.tex:1227–1470`, `StrongSubalgebras.tex:1022–1927` | 4,500 | 3.0 |
| L9 | **Zhuk §2: the six subuniverse types, ⋘, MT types, propagation lemmas, `LEMUbiquity`** | `main.tex:1504–1931`, `StrongSubalgebras.tex:71–347`, `2297–3144` | 4,500 | 3.0 |
| L10 | **Zhuk §2: the intersection property.** `THMMainStableIntersection` + `CORMainStableIntersection` + `LEMIntersectionPCLinearIsGood` (292-line proof) + `LEMSelfIntersectionPC` (175 ln) | `StrongSubalgebras.tex:347–1022` (675 ln) | 4,000 | 2.7 |
| L11 | **Zhuk §3: CSP vocabulary.** instances, reductions, induced congruences `Con₁`, consistency, linkedness, irreducibility, weakening, crucial instances, expanded coverings (p1)–(p8), connectedness | `main.tex:1969–2229` | 2,000 | 1.4 |
| L12 | **Zhuk §3: auxiliary statements** (17 lemmas incl. `LEMParalPropertyFromCrucialInMultiType` 126 ln, `LEMGetABridgeFromSubdirectPCLinearInstance` 205+159 ln, `LEMConnectedProperties`, `LEMFindOneConsistentForAll`, `LEMMinimalPCLinearReductionIsConsistent`) | `main.tex:2230–3406` | 5,000 | 3.3 |
| L13 | **`THMMainInductiveCSPClaim`** — the 427-line simultaneous induction | `main.tex:3408–3977` | 3,500 | 2.5 |
| L14 | **The two target theorems** (`THMCSPDReductionsAreSafe`, `THMCodimensionOneTheorem`) | `main.tex:3978–4122` | 900 | 0.6 |
| | **TOTAL (T2, new work)** | | **≈ 35,000** | **≈ 24** |
| | plus blueprint writing at ~1.1× Lean lines | | ≈ 38,000 LaTeX ln | **+8–12** |
| | **TOTAL with blueprint** | | | **≈ 32–36 P-M** |

**Range, honestly: 25,000–50,000 Lean lines and 25–50 person-months** at conventional rates.

**Calibration caveat, stated both ways.** The one measured data point in this project — 1,603
sorry-free Lean lines plus a 1,830-line 8-draft blueprint, in **~24 hours wall clock** — implies an
agent-assisted throughput perhaps 20–40× the conventional rate. If that throughput holds at scale,
the project is **6–18 months of sustained agent-driven work with human review**, not 3 years. But it
almost certainly does *not* hold at scale: the centre theorem's proofs average ~25 source lines,
whereas L10, L12 and L13 contain proofs of 175, 205, 292 and 427 lines whose case analyses do not
decompose the same way. Plan for the conventional estimate; treat the agent multiplier as upside.

### What to cut for a defensible partial result

Ranked by defensibility per unit of work.

**Cut 1 — "Zhuk's reductions are safe" (L0–L5, L8, L9, L11, L12, L13, L14 minus the codimension-one
theorem). ≈ 24,000 lines, ≈ 17 P-M.** Delivers `THMCSPDReductionsAreSafe`: *for a cycle-consistent
irreducible instance and B <_T D_x with T ∈ {BA, C, PC}, the instance has a solution iff it has one
with x ∈ B.* This is the statement Gaysin (arXiv:2403.06704) singles out as the universal-algebra
heart, and it is the loop invariant of `Solve`. Cutting `THMCodimensionOneTheorem` drops `SolveLinear`
and with it much of L7 and L10.

**Cut 2 — "One of four" / the ubiquity theorem (L0–L5, L8, L9). ≈ 16,000 lines, ≈ 11 P-M.**
Delivers `LEMUbiquity`: *every B ⋘ A with |B| > 1 has a proper subuniverse of type BA, central,
linear, or PC.* This is Zhuk's "one of four cases", the fundamental structural theorem of the whole
approach, and it needs **no CSP-instance machinery at all** (no instances, no coverings, no crucial
instances, no expanded coverings). It is a clean, quotable, self-contained universal-algebra theorem.
**This is the best stopping point if you need one.**

**Cut 3 — the classical prerequisite layer (L0–L5). ≈ 9,000 lines, ≈ 6 P-M.** Delivers, on top of
what exists: the **Barto–Kozik Absorption Theorem**, the **Loop Lemma**, **Siggers terms**, and
**finite abelian Taylor ⟹ affine**. Every one of these is a named, citable theorem that no proof
assistant currently has, and each is independently publishable as a Mathlib-adjacent contribution.
**This is the best next milestone** — it is a natural continuation of `zhuk-lean` (L3 is a short
corollary of what is already proved), it derisks the foundations before committing to Zhuk §2/§3,
and it fails gracefully.

**Never attempt:** T1 (P/NP, NP-completeness, Cook–Levin, NAE-3SAT hardness) — add ≥ 30,000 lines and
years, with no Mathlib substrate. **Always cut:** Zhuk 2404 §4 (XY-symmetric operations) — 1,640
lines, 20 statements, provably not on the dependency path.

---

## 9. Risks specific to this route

1. **`StrongSubalgebras.tex:186–189`, "repeat the same proof word to word replacing BA by S".**
   Must be replaced by a proof parametric in T ∈ {BA, C, S}, or by two proofs. Resolve in the blueprint.
2. **`THMMainInductiveCSPClaim` is a mutually-invoking simultaneous induction** (proof of (2) uses IH
   for (1); proof of (1) uses IH for (2)). The blueprint must state the induction hypothesis as a
   single explicitly-quantified conjunction *before* anyone opens an editor — the same discipline
   `zhuk_centers` Remark 7.2 applied to the doubling lemma's Step 1.
3. **The empty-subuniverse convention** (`⋘` excludes ∅; three dotted variants readmit it). This
   already caused two vacuous-quantification defects in the previous, much smaller project.
4. **Type-with-attached-congruence overloading** (`<_{T(σ)}` where σ is "a full congruence" and
   irrelevant when T ∈ {BA, C, S}). Decide the data layout once.
5. **L4 (abelian ⟹ affine) is the largest genuinely new prerequisite** and the only one with no
   partial credit from `zhuk-lean`. It drags in Mal'cev algebras. If it slips, everything downstream
   of `LEMLInearOnTheTopIsEasy` slips.
6. **`LEMBACenterSImplyPPDefinition` has 11 uses** and needs an induction over pp-formula structure.
   Mathlib's `ModelTheory.Syntax` / `Definability` may or may not give the right induction principle
   for *positive existential conjunctive* formulas; check early.
7. **`main.tex:2100` typo** (`X₁` twice in the definition of *fragmented*) and the undefined `\R`
   macro at `main.tex:2135` — evidence the source has not been read at formalization granularity.
   Assume more of these.
8. **Free algebras.** Not needed on the recommended route, but needed the moment anyone reaches for
   cyclic terms. Mathlib does not have free algebras over an arbitrary `FirstOrder.Language`.
9. **Bridges may be re-founded.** Willard's three-paper series (arXiv:2502.20517, 2503.03551, +1
   forthcoming) shows Zhuk's bridges and "similarity bridges" carry the same information in locally
   finite Taylor varieties. Read it before finalising the bridge module; a better definition may be
   available, and the third paper is not out yet.
10. **Statement-level drift between 2404 and its sources.** 2404 cites 2005.00593 Thm 6.15 as
    `LEMCentralRelationImplies`; `zhuk-lean` proves it via Brady's §3.10, and the `zhuk_centers`
    concordance already records places where the version proved is *weaker* than the source. Every
    import must be re-checked against the exact form 2404 uses, not the form Brady states.

---

## 10. Ranked recommendation

**1. (a)+(e) hybrid — Zhuk 2404 spine, Brady prerequisites, on `zhuk-lean`. RECOMMENDED.**
2404 §2–§3 is the only complete, recent, rigorously-written proof of the dichotomy, and its own
author rewrote it to eliminate the local-to-global induction that made 1704 unformalizable. Its 16
black-box imports are its weakness, but three are already discharged by this project, and the two
hardest — the Absorption Theorem and abelian ⟹ affine — are proved in Brady's notes *from the theorem
this project has already formalized* and *without Tame Congruence Theory*. Cut §4. Target T2.
≈ 35,000 Lean lines, ≈ 32–36 person-months with blueprint; stage it as Cut 3 → Cut 2 → Cut 1 → T2.

**2. (a) alone — Zhuk 2404, importing prerequisites as axioms.** Viable as a *staging* strategy: state
the 16 imports as Lean `axiom`s, build §2–§3 on top, discharge the axioms later. Halves time to a
working skeleton and makes the dependency structure explicit. **Only acceptable if the axiom list is
published as such** and Cut 3 is scheduled; an axiom-laden "proof of the CSP dichotomy" is not a
result.

**3. (e) alone — Brady's notes.** Cleanest prose, best-motivated, and the source of the two key
prerequisite proofs — but explicitly "maybe half way" to the dichotomy, with 54 TODOs and 32
"exercise"s. Cannot reach the dichotomy. **Use as the proof source, never as the spine.**

**4. (d) minimal Taylor algebras.** Zhuk's own claim at `main.tex:1055–1057` is *true but a bad
trade*: it would simplify perhaps 20–30 % of §2 (S-type bookkeeping collapses; 2-absorption becomes
strong projectivity; 3-absorption becomes centrality) and **nothing** of §3, at the cost of the
**cyclic term theorem** (3,000–6,000 lines, plus free algebras on m generators) which 2404 does not
otherwise need — it uses only *special WNU*, an elementary pigeonhole argument. **Net negative.**
Mine 2104.11808 §5 for lemma statements and intuition; do not adopt the framework.

**5. (b) Zhuk 1704 / JACM 2020.** Superseded by the author. Its "very complicated induction" is the
worst possible formalization target. **But keep it open**: it is the sole source for the algorithm,
its polynomiality, the auxiliary functions, and five results 2404 imports from it.

**6. (f) newer work.** Nothing supersedes 2404. Willard arXiv:2503.03551 is worth reading before the
bridge module. Barto–Hadek–Zhuk arXiv:2604.06335 is useful negative evidence — no simple uniform
algorithm is imminent. Gaysin arXiv:2403.06704 is the only prior rigorous re-derivation of a Zhuk
component and should be read before writing `THMCSPDReductionsAreSafe`.

**7. (c) Bulatov.** Rank last. Requires Tame Congruence Theory and centraliser theory, neither of
which has any formalization anywhere, and both of which the Zhuk route avoids entirely.
arXiv:2604.05231 (Apr 2026) genuinely improves the situation by reproving Bulatov's theory for
minimal Taylor algebras — revisit in 2–3 years, not now.

### Immediate next action

Write the blueprint for **Cut 3** — the classical prerequisite layer — as
`brady_absorption.tex` alongside `zhuk_centers.tex`, in the same style, covering Brady `csp.tex`
§8540–§8859, §9822–§10127, §10443–§10669, §10670–§10854 and §4235–§4706. It extends the finished
work, it discharges 2404's two hardest imports, every theorem in it is independently citable, and it
is the only way to find out whether the observed throughput survives contact with harder material
before committing to Zhuk §2/§3.
