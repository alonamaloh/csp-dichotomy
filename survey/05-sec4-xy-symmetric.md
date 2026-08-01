# Section 4 of Zhuk, arXiv:2404.01080v2 — "XY-symmetric operations"

Deep read for the formalization blueprint. Companion to `01-sec2-strong-subuniverses.md`.

**Sources read (all local, no web):**

| file | role |
|---|---|
| `.../src2404/XYSymmetric.tex` (1640 lines, complete) | Section 4 proper, `\input` at main.tex:4123 |
| `.../src2404/main.tex` L760–975 | §1.2 "Existence of XY-symmetric operations" (the introduction to Section 4) |
| `.../src2404/main.tex` L1064–1931 | Section 2 — everything Section 4 imports |
| `.../src2404/necessaryClaims.tex` | §2.4, three of Section 4's imports live here |
| `.../src2404/main.tex` L1932–4122 | Section 3 — checked exhaustively for back-dependencies |
| `.../src2404/StrongSubalgebras.tex` | Section 5 — checked for back-dependencies |
| `.../papers/zhuk2404.txt` pp. 5–7, 26–36 | rendered text, used to recover printed numbering |

**Page budget (from the printed TOC).** §1 pp. 2–8, §2 pp. 8–15, §3 pp. 15–26, **§4 pp. 26–36**, §5 pp. 36–53.
Section 4 is ~10 of the ~45 pages of technical content (22%), and 1640 of the 8998 LaTeX lines (18%).

---

# 0. THE HEADLINE ANSWER

> **Section 4 is NOT needed for the CSP Dichotomy Theorem. It is a strictly independent
> second result, sitting downstream of Sections 2 and 5 and completely disjoint from Section 3.**

This is not a judgement call; it is mechanically verifiable from the LaTeX cross-reference graph, and
I checked it in both directions.

### 0.1 Nothing outside Section 4 depends on Section 4

Extracting every `\label{…}` in `XYSymmetric.tex` (22 labels) and grepping `\ref{…}` for each of them
across `main.tex`, `StrongSubalgebras.tex` and `necessaryClaims.tex` yields **exactly four hits, all
non-mathematical**:

* `main.tex:1042`, `:1054`, `:1127` — prose: "In Section 4 we show that…", "in Sections 3 and 4 we
  usually consider algebras from 𝒱ₙ".
* `main.tex:308`, `:349`, `:353` — `\newtheorem*{…}{Theorem~\ref{…}}` preamble declarations, i.e. the
  boilerplate that lets Section 4 restate its own theorems. Not uses.

The two theorems that Section 3 exists to prove — `THMCSPDReductionsAreSafe` (Theorem 43, main.tex:3985)
and `THMCodimensionOneTheorem` (Theorem 44, main.tex:4004), the two statements that make Zhuk's
algorithm correct — have proofs that cite only Section 2 / Section 3 material.
Section 5 (`StrongSubalgebras.tex`) never mentions Section 4.

Note also the ordering: `\input{XYSymmetric}` is at main.tex:4123, i.e. **after** all of Section 3, and
`\input{StrongSubalgebras}` is at 4125. So Section 4 could be deleted from the paper and Theorem 1
(the dichotomy) would be unaffected.

### 0.2 Section 4 does not depend on Section 3 either

Every `\ref` issued from inside `XYSymmetric.tex` resolves to one of: (i) a Section-4 label, (ii) a
Section-2 label, (iii) a §2.4 (`necessaryClaims.tex`) label. **Zero references into Section 3.**
Complete import list:

| imported | printed | where stated | also used by §3? |
|---|---|---|---|
| `LEMUbiquity` | Lemma 13 | main.tex:1653 | yes |
| `LEMPropagation` (b, bt, ft) | Lemma 14 | main.tex:1659 | yes |
| `CORPropagateFromFactor` (t) | Corollary 16 | main.tex:1699 | yes |
| `CORPropagateMultiplyByCongruence` (t) | Corollary 17 | main.tex:1713 | yes |
| `CORPropagateToRelations` (r, r1) | Corollary 18 | main.tex:1726 | yes |
| `LEMBACenterImplies` | Lemma 19 | main.tex:1753 | yes |
| `LEMIntersectALL` (t) | Lemma 20 | main.tex:1762 | yes |
| `CORMainStableIntersection` | Corollary 22 | main.tex:1803 | yes |
| `LEMMakePerfectCongruenceFromLinked` | Lemma 5 | main.tex:1310, proved necessaryClaims.tex:36 | **NO — §4 only** |
| `LEMNoAbsCenterPCInLinearAlgebra` | Lemma 29 | necessaryClaims.tex:69 | yes (main.tex:3485) |
| `LEMExistenceOfSpesialWNULemma` | Lemma 26 | necessaryClaims.tex:5 | **NO — §4 only** (§3 only name-drops it at main.tex:1082) |

So Section 4's Section-2 surface is a **proper subset** of Section 3's, with exactly two exceptions:

* **Lemma 5** (`LEMMakePerfectCongruenceFromLinked`): "σ irreducible on **A** ∈ 𝒱ₙ, δ a bridge from σ
  to σ with δ̃ linked ⟹ σ is a perfect linear congruence." Its proof (necessaryClaims.tex:43–57) is
  10 lines and uses only Lemma 27 (`LEMBuildingPerfectCongruence`) and Lemma 28
  (`LEMBridgeComposition`), *both of which Section 3 already needs* (main.tex:2421 and :2384). So the
  marginal cost of this import is ~nil.
* **Lemma 26** (Maróti–McKenzie, `\cite{miklos}` Lemma 4.7, stated without proof): "w an idempotent WNU
  on A ⟹ ∃ special idempotent WNU w′ ∈ Clo(w) of arity n^{n!}." This is an *external* import that the
  paper never proves. A complete formalization of the dichotomy will need it anyway, to get from
  "Γ has a WNU polymorphism" to "all domains lie in 𝒱ₙ" — Section 3 simply assumes 𝒱ₙ and never
  discharges that reduction.

**Consequence for the module architecture:** Section 4 is a *leaf*. It can be added, deferred,
or dropped at any time without touching the main line. It cannot block anything.

### 0.3 The one place Section 4 touches the dichotomy narrative

Corollary 3 (`corTaylorEquivalentConditions`, main.tex:797) lists six equivalent characterisations of
finite Taylor algebras; Section 4 supplies item 6 ("**A** has an XY-symmetric term operation of any
prime arity p > |A|"). Items 1–5 are all pre-existing literature (Bulatov; Maróti–McKenzie; Barto–Kozik;
Siggers/Kearnes–Marković–McKenzie). The dichotomy theorem never uses item 6.

Zhuk's own explanation of why the two results are in one paper (main.tex:962–974) is *methodological*,
not logical: "their proofs have the same flavour… the proofs of Informal Claims 1 and 2 are similar to
the proof of Theorem 2, only sufficient level of consistency is replaced by symmetries of the relation R."

### 0.4 A second, sharper independence: §4.4 needs *nothing* from Sections 2 or 5

Splitting Section 4 at line 865:

* **§4.1–4.3** (lines 1–864, printed pp. 26–31) — imports all 11 Section-2 lemmas above.
* **§4.4** "Proof of Theorem 47 (Fixing an operation)" (lines 865–1639, printed pp. 31–36) — imports
  **zero** external lemmas. Its only prerequisites are: the definition of *perfect linear congruence*
  (main.tex:1295–1301), the class 𝒱ₙ (special idempotent WNU, main.tex:1079/1110), the algebra **Z**ₚ,
  and generic clone/term machinery.

This is a real architectural finding: **§4.4 is a self-contained ~6-page piece of 𝐙ₚ-linear algebra over
term trees that could be formalized on day 1, in parallel, by someone who has not read Section 2 at all.**

---

# 1. Printed numbering map

| printed | label | XYSymmetric.tex line | kind |
|---|---|---|---|
| Theorem 2 | `THMMainTheoremOnXYSymmetric` | stated main.tex:789, restated+proved 396–418 | main result |
| Corollary 3 | `corTaylorEquivalentConditions` | main.tex:797 | corollary of Thm 2 |
| Lemma 4 (unnumbered in src) | — | main.tex:845 | the XYZ counterexample |
| Theorem 45 | `THMExistenceOfReduction` | 214 (proved 604–662) | reduction step |
| Theorem 46 | `THMBuildAReductionFromXYSymmetric` | 234 (proved 664–863) | reduction step |
| Theorem 47 | `THMpropagateXYSymmetric` | 254 (proved 1615–1639) | operation-fixing |
| Theorem 48 | `THMMainInductive` | 262 (proved 270–393) | **the induction** |
| Theorem 49 | `ExistenceOfStrongReductionTHM` | 422 | workhorse of 45/46 |
| Lemma 50 | `LEMExistenceOfReduction` | 579 | workhorse of 45 |
| Lemma 51 | `ZetaPropertiesLEM` | 869 | ζ-calculus |
| Theorem 52 | `ExistenceOfInjectiveHomomorphismTHM` | 951 | **A** ↪ **B** ⊠ **Z**ₚ |
| Lemma 53 | `kWNUImplieskWNU` | 1213 | tᶠ₀ preserves k-WNU |
| Lemma 54 | `SpecialWNUPreservingDeltaLEM` | 1285 | f⁽²'²⁾ = Σxᵢ, p ∣ n−1 |
| Lemma 55 | `DifferenceTwoTwoReplacementLEM` | 1320 | leaf-replacement calculus (**no proof given**) |
| Lemma 56 | `TwoTwoPartLEM` | 1334 | (tᶠ₀)⁽²'²⁾ = Σxᵢ |
| Lemma 57 | `GeneralizedMaltsev` | 1353 | alternating sums from Σ |
| Lemma 58 | `MainIncreasingSymmetricity` | 1409 | k ↦ k+1 (the engine of §4.4) |
| Corollary 59 | `MainIncreasingSymmetricityCor` | 1516 | iterate 58 to full weak symmetry |
| Theorem 60 | `PropagateXYSYmmetricityToBoxtimesTHM` | 1554 | XY-symmetry propagates across ⊠ |

Dead labels present in the file but never used: `ExistenceOfNextStrongReductionTHM` (commented out),
`RelationDefinesBoxtimesLEM` (commented out — **see §5, gap G1**), `bigTransformation`.

---

# 2. Definitions (verbatim-faithful)

## 2.1 Symmetry vocabulary (main.tex:766–780)

* An n-ary operation f is **symmetric on a tuple of variables** (x_{i₁},…,x_{i_n}) if it satisfies the
  identity f(x_{i₁},…,x_{i_n}) = f(x_{i_{σ(1)}},…,x_{i_{σ(n)}}) for every permutation σ of [n].
* f is **XY-symmetric** if it is symmetric on (x,…,x,y,…,y) — i copies of x — **for every i**.
  Unfolded: for all a,b ∈ A and all α,β ∈ {a,b}ⁿ with N_b(α) = N_b(β), f(α) = f(β).
* f is a **k-WNU** (XYSymmetric.tex:106) if it is symmetric on (x,…,x,y,…,y) with k copies of x.
  1-WNU = ordinary WNU. XY-symmetric = k-WNU for all k ∈ [n].
* f is **idempotent** if f(x,…,x) = x.

**⚠ Overloading.** XYSymmetric.tex:1382–1391 *redefines* "symmetric on a tuple" for a tuple of
**elements** (a₁,…,a_n) rather than variables, and adds **weakly symmetric on a tuple**: invariance
under permutations σ with σ(1) = 1. Two different notions share one phrase. In Lean these must be
three separate predicates:
`SymmOnVars f (i₁…i_n)`, `SymmAt f (a₁…a_n)`, `WeakSymmAt f (a₁…a_n)`.

Auxiliary: for a tuple α and element b, **N_b(α)** = number of coordinates equal to b (line 1254).
**T^{n,k}_{a,b}** = { γ ∈ {a,b}ⁿ : N_b(γ) = k and γ(1) = a } (line 1256).

## 2.2 The free generated relation R_{**A**₁,…,**A**_s} (lines 40–79)

Fix n and algebras **A**₁,…,**A**_s ∈ 𝒱ₙ.

* `TwoTuples(S)` = the set of tuples in S having **exactly** 2 distinct elements.
* Index set **I** = { (**A**ᵢ, α) : i ∈ [s], α ∈ TwoTuples(Aᵢⁿ) }.
  Arity N = |I| = (2^{n−1} − 1) · Σᵢ |Aᵢ|·(|Aᵢ| − 1).  *(Check: per unordered pair {a,b} there are
  2ⁿ − 2 tuples; |Aᵢ|(|Aᵢ|−1)/2 pairs; product = (2^{n−1}−1)|Aᵢ|(|Aᵢ|−1). ✓)*
* For i ∈ [n], **γ_i** ∈ ∏ is the tuple whose (**A**_j, α) entry is α(i).
* **R_{A₁,…,A_s}** := Sg(γ₁,…,γ_n) ≤ ∏_{i∈[s]} **A**ᵢ^{(2^{n−1}−1)|Aᵢ|(|Aᵢ|−1)} — the subalgebra
  generated by the n tuples γ₁,…,γ_n. The γ's are called **the generators**.
* **D⁽⁰⁾_{(**A**ᵢ,α)}** := Sg_{**A**ᵢ}(elements of α) = Sg({a,b}). Then pr_{(**A**ᵢ,α)}(R) = D⁽⁰⁾_{(**A**ᵢ,α)}.
* **𝓡_{A₁,…,A_s}** := all relations R of arity N, coordinates indexed by I, whose i-th domain is D⁽⁰⁾ᵢ.

*Formalization note.* The coordinate type is a Σ-type `(i : Fin s) × {α : Fin n → Aᵢ // exactly two values}`
whose second component's type **depends on i**. That dependency is the single most annoying feature of
this section for Lean. An alternative is to index by `(i, a, b, S)` with `S ⊆ Fin n` nonempty proper,
i.e. the b-positions — at the cost of a 2-to-1 redundancy (ordered pair (a,b) with set S ≡ (b,a) with Sᶜ).

## 2.3 Reductions (lines 83–104)

* **A reduction D⁽ᵀᵒᵖ⁾ for R ∈ 𝓡** assigns a subuniverse D⁽ᵀᵒᵖ⁾ᵢ ≤ D⁽⁰⁾ᵢ to every i ∈ I.
* D⁽⊥⁾ ⋘ D⁽ᵀᵒᵖ⁾ / D⁽⊥⁾ ≤_T D⁽ᵀᵒᵖ⁾ means the relation holds **coordinatewise for every i ∈ I**.
* Any reduction is itself a member of 𝓡, and R⁽⊥⁾ := R ∩ D⁽⊥⁾.
* D⁽⊥⁾ is **1-consistent** for R if pr_i(R⁽⊥⁾) = D⁽⊥⁾ᵢ for every i ∈ I.

This is deliberately parallel to the CSP-instance reductions of Section 3 (main.tex:1993–2001) but is a
**separate definition**; there is no shared abstraction in the paper. A formalization *could* factor
"reduction over an index set with a family of algebras" once and instantiate twice — probably worth it.

## 2.4 Permutation action (lines 131–161)

* Perm(α) = all tuples obtainable from α by permuting entries. Perm((**A**_j,α)) = {(**A**_j,β) : β ∈ Perm(α)}.
* For σ ∈ S_n and α ∈ Aⁿ: σ(α) is α′ with α′(j) = α(σ(j)).
* For γ of arity N: **γ^σ** is γ′ with γ′((**A**ᵢ,α)) = γ((**A**ᵢ, σ(α))).
* R^σ = {γ^σ : γ ∈ R}; R is **σ-symmetric** if R^σ = R; **symmetric** if σ-symmetric for all σ ∈ S_n.
* A reduction D⁽ᵀᵒᵖ⁾ is **symmetric** if D⁽ᵀᵒᵖ⁾ᵢ = D⁽ᵀᵒᵖ⁾_j for all j ∈ Perm(i).

**⚠ Never stated, silently used:** *R_{A₁,…,A_s} is symmetric.* Proof: γ_i^σ((**A**_j,α)) =
γ_i((**A**_j,σ(α))) = σ(α)(i) = α(σ(i)) = γ_{σ(i)}((**A**_j,α)), so σ permutes the generators, hence
fixes the generated subalgebra. Used at line 654 ("Since D⁽ᵀᵒᵖ⁾ and R are symmetric, D⁽²⁾ is also
symmetric") and implicitly whenever Theorem 49 is applied to R (its hypothesis 2 says "a symmetric
relation R"). **This must be an explicit lemma in the blueprint.**

## 2.5 The ⊠-product (lines 164–181)

For x = (a,b) write x⁽¹⁾ = a, x⁽²⁾ = b. For **B** = (B; w^**B**), **B** ⊠ **Z**ₚ denotes the **set of
algebras** **A** with A = B × Z_p such that

* (w^**A**(x₁,…,x_n))⁽¹⁾ = w^**B**(x₁⁽¹⁾,…,x_n⁽¹⁾),
* (w^**A**(x₁,…,x_n))⁽²⁾ = f(x₁⁽¹⁾,…,x_n⁽¹⁾) + a₁x₁⁽²⁾ + … + a_n x_n⁽²⁾

for some f : Bⁿ → **Z**ₚ and a₁,…,a_n ∈ **Z**ₚ. (Note: ⊠ yields a *class*, and the paper writes both
"**A** ∈ **B** ⊠ **Z**ₚ" and "**C** ∈ (**A**/0* ⊠ **Z**ₚ) ∩ 𝒱ₙ".)

Generalised to arbitrary arities at line 1183: **𝓒_{B ⊠ **Z**ₚ}** = all operations f on B × Z_p with
f⁽¹⁾ depending only on the first components and f⁽²⁾ = f⁽²'¹⁾(x⁽¹⁾) + Σ aᵢ xᵢ⁽²⁾. The linear part
Σ aᵢ xᵢ⁽²⁾ is written **f⁽²'²⁾**. 𝓒 is a clone (needed, never stated).

## 2.6 The term tower tᶠ_ℓ (lines 1203–1241)

For an n-ary f define, for ℓ = n, n−1, …, 0:

    tᶠ_n(x₁,…,x_n, y₁,…,y_n)      = f(x₁,…,x_n)
    tᶠ_ℓ(x₁,…,x_ℓ, y₁,…,y_n)      = f( t_{ℓ+1}(x₁,…,x_ℓ, y₁, y₁,…,y_n),
                                        t_{ℓ+1}(x₁,…,x_ℓ, y₂, y₁,…,y_n), …,
                                        t_{ℓ+1}(x₁,…,x_ℓ, y_n, y₁,…,y_n) )

so tᶠ₀ is n-ary. **Key structural fact** (line 1232, asserted): in the term defining tᶠ₀, for every
(i₁,…,i_n) ∈ [n]ⁿ there is **exactly one** internal occurrence f(y_{i₁},…,y_{i_n}) — i.e. tᶠ₀ is a
depth-n tree with nⁿ leaves in bijection with [n]ⁿ. Notation
**t^{f,(j₁,…,j_n)}_{0,(i₁,…,i_n)}** = the same term with the single leaf f(y_{i₁},…,y_{i_n}) replaced
by f(y_{j₁},…,y_{j_n}).

**ξ(α,β)** for α,β ∈ T^{n,k}_{a,b} (lines 1260–1279): let j₁<…<j_k and s₁<…<s_k be the b-positions of
α and β. Put i_ℓ = 1 if β(ℓ) = a, and i_{s_m} = j_m. Worked example given at 1275. Noted property:
ξ(α,β) is a permutation of ξ(α,γ) for any α,β,γ ∈ T^{n,k}_{a,b}.

## 2.7 (P,a,b,k)-symmetric (lines 1393–1407)

For P ⊆ {(c,d) : c,d ∈ B, c ≠ d} and a,b ∈ B, an n-ary f ∈ 𝓒_{B⊠**Z**ₚ} is **(P,a,b,k)-symmetric** if

1. p divides n − 1;
2. f⁽¹⁾ is XY-symmetric;
3. f⁽²'²⁾(x₁⁽²⁾,…,x_n⁽²⁾) = x₁⁽²⁾ + … + x_n⁽²⁾;
4. f⁽²'¹⁾ is weakly symmetric on all α ∈ {c,d}ⁿ with α(1) = c and (c,d) ∈ P;
5. f⁽²'¹⁾ is weakly symmetric on all α ∈ {a,b}ⁿ with α(1) = a and N_b(α) ≤ k.

f is **P-symmetric** if it satisfies only (1)–(4). Note P is a set of **ordered** pairs; full weak
symmetry on all 2-valued tuples needs both (a,b) and (b,a) in P.

---

# 3. The main theorems (faithful statements)

**Theorem 2** (main.tex:789 / XYSymmetric.tex:396). *Suppose f is a WNU operation of an odd arity n on
a finite set. Then there exists an XY-symmetric operation f′ ∈ Clo({f}) of arity n.*
⚠ **Idempotency is missing from this statement** — see gap G6.

**Theorem 45** `THMExistenceOfReduction` (line 214). *Suppose **A**₁,…,**A**_s ∈ 𝒱ₙ, n odd, D⁽¹⁾ is a
1-consistent symmetric reduction of R_{A₁,…,A_s}, D⁽¹⁾ ⋘ D⁽⁰⁾. Then one of:*
1. *|D⁽¹⁾_{(**A**ᵢ,α)}| = 1 for all (**A**ᵢ,α);*
2. *there is a 1-consistent symmetric reduction D⁽²⁾ for R with D⁽²⁾ ⋘ D⁽¹⁾ and D⁽²⁾ ≠ D⁽¹⁾;*
3. *there is a perfect linear congruence σ on some D⁽⁰⁾_{(**A**ᵢ,α)} with
   (a) D⁽¹⁾_{(**A**ᵢ,α)} × D⁽¹⁾_{(**A**ᵢ,α)} ⊄ σ, and (b) D⁽¹⁾_{(**A**ᵢ,α)} × D⁽¹⁾_{(**A**ᵢ,α)} ⊆ σ\*.*

**Theorem 46** `THMBuildAReductionFromXYSymmetric` (line 234). *Suppose **A**₁,…,**A**_s ∈ 𝒱ₙ, n odd,
and there is an n-ary term τ₀ such that τ₀^{**A**ᵢ} is XY-symmetric for every i. Then there exist a
1-consistent symmetric reduction D⁽△⁾ ⋘ D⁽⁰⁾ of R_{A₁,…,A_s} and an n-ary term τ such that τ^{**A**ᵢ}
is XY-symmetric and D⁽△⁾_{(**A**ᵢ,α)} = {τ(α)} for every i and α ∈ TwoTuples(Aᵢⁿ).*

**Theorem 47** `THMpropagateXYSymmetric` (line 254). *Suppose **A**, **B** ∈ 𝒱ₙ, 0_**A** is a perfect
linear congruence, and **A**/0_**A**\* × **B** has an XY-symmetric term operation of arity n. Then
**A** × **B** has an XY-symmetric term operation.*

**Theorem 48** `THMMainInductive` (line 262). *Suppose **A**₁,…,**A**_s ∈ 𝒱ₙ, n odd. Then there exists
a term τ such that τ^{**A**ᵢ} is an XY-symmetric operation for every i.*

**Theorem 49** `ExistenceOfStrongReductionTHM` (line 422). *Suppose (1) **A**₁,…,**A**_s ∈ 𝒱ₙ, n odd;
(2) D⁽¹⁾ is a 1-consistent symmetric reduction of a **symmetric** relation R ∈ 𝓡; (3) D⁽¹⁾ ⋘ D⁽⁰⁾;
(4) B <_𝓣^{D⁽⁰⁾_{(A_j,β)}} D⁽¹⁾_{(A_j,β)} with 𝓣 ∈ {𝓑𝓐, 𝓒, 𝓟𝓒}. Then there is a 1-consistent symmetric
reduction D⁽²⁾ for R with D⁽²⁾ ⋘ D⁽¹⁾ and D⁽²⁾ ≠ D⁽¹⁾; moreover D⁽²⁾ ≤_𝓣 D⁽¹⁾ if 𝓣 ≠ 𝓟𝓒.*

**Lemma 50** `LEMExistenceOfReduction` (line 579). *Suppose **A**₁,…,**A**_s ∈ 𝒱ₙ, n odd, D⁽¹⁾ a
1-consistent symmetric reduction of R, D⁽¹⁾ ⋘ D⁽⁰⁾, B <_{𝓓(σ)}^{D⁽⁰⁾_{(Aᵢ,α)}} D⁽¹⁾_{(Aᵢ,α)}, and
R⁽¹⁾ has no tuple γ with γ(**A**ᵢ,β) ∈ B for every β ∈ Perm(α). Then σ is a perfect linear congruence
on D⁽⁰⁾_{(**A**ᵢ,α)}.*

**Lemma 51** `ZetaPropertiesLEM` (line 869). *Suppose **A** = (A; w^**A**) with w^**A** n-ary idempotent,
0_**A** a perfect linear congruence witnessed by ζ ≤ **A**×**A**×**Z**ₚ. Then:*
(1) *for every (a,b) ∈ 0_**A**\* there is a **unique** c with (a,b,c) ∈ ζ;*
(2) *p ∣ n − 1;*
(3) *w^**A**(a,…,a,b,a,…,a) = b for every (a,b) ∈ 0_**A**\* and any position of b;*
(4) *for every a, c there is at most one b with (a,b,c) ∈ ζ;* (5) *dually in a;*
(6) *(a,b,d),(b,c,e) ∈ ζ ⟹ (a,c,d+e) ∈ ζ.*
By (1), ζ becomes a partial binary function ζ(x₁,x₂) = z ⟺ (x₁,x₂,z) ∈ ζ, additive by (6).

**Theorem 52** `ExistenceOfInjectiveHomomorphismTHM` (line 951). *Suppose **A** ∈ 𝒱ₙ and 0_**A** is a
perfect linear congruence. Then there exists **C** ∈ (**A**/0_**A**\* ⊠ **Z**ₚ) ∩ 𝒱ₙ and an injective
homomorphism h : **A** → **C**.*

**Lemma 53–57** — see §1 table; all are 𝐙ₚ-calculus lemmas about tᶠ₀.

**Lemma 58** `MainIncreasingSymmetricity` (line 1409). *Suppose P ⊆ {(c,d) : c ≠ d ∈ B}, 0 ≤ k < n−1,
a,b ∈ B, and f ∈ 𝓒_{B⊠**Z**ₚ} is (P,a,b,k)-symmetric. Then there is a (P,a,b,k+1)-symmetric
g ∈ Clo(f) of arity n.*

**Corollary 59** (line 1516). *Suppose g ∈ 𝓒_{B⊠**Z**ₚ}, g⁽¹⁾ is n-ary XY-symmetric, p ∣ n−1,
g⁽²'²⁾ = Σxᵢ⁽²⁾. Then Clo(g) contains an n-ary h with h⁽¹⁾ XY-symmetric, h⁽²'²⁾ = Σxᵢ⁽²⁾, and h
[**read: h⁽²'¹⁾**] weakly symmetric on all tuples having two different elements.*

**Theorem 60** (line 1554). *Suppose **A** ∈ (**B** ⊠ **Z**ₚ) ∩ 𝒱ₙ and w^**B** is XY-symmetric. Then
there is an n-ary term t with t^**A** XY-symmetric.*

---

# 4. Digest of the argument

## 4.1 The CSP-shaped reformulation (main.tex:966–972)

Take the matrix whose rows are all n-tuples with exactly two distinct elements; close the columns under
the WNU; the result is a relation R of huge arity N. An XY-symmetric term exists **iff** R contains a
tuple that is constant on each Perm-block. That is a CSP instance: one R-constraint plus many equality
constraints. Section 4 solves it by the Section-2 reduction technique, with "sufficient consistency"
replaced by "symmetry of R".

## 4.2 Theorem 48 (the induction), lines 270–393

Sort so |A₁| ≥ … ≥ |A_s|; attach the infinite tuple (|A₁|,…,|A_s|,0,0,…); induct on the **lexicographic**
order of these tuples. Base: all |Aᵢ| = 1.

Inductive step: first WLOG **add all nontrivial subalgebras of A₁ to the list**. Then:

* **Case 1** — **A**₁ has two nontrivial congruences σ, δ with σ ∩ δ = 0. Apply IH to
  **A**₁/σ, **A**₁/δ, **A**₂,…,**A**_s to get t; since **A**₁ ↪ **A**₁/σ × **A**₁/δ, t^{**A**₁} is
  XY-symmetric. Done.
* **Case 2** — **A**₁ has a unique minimal nontrivial congruence δ. IH gives τ₀ XY-symmetric on
  **A**₁/δ and on all **A**ᵢ (i ≥ 2). Theorem 46 gives a singleton reduction D⁽⊤⁾ for
  R_{**A**₁/δ, **A**₂,…,**A**_s} witnessed by a term τ₁. Lift: D⁽¹⁾_{(A_i,α)} = D⁽⊤⁾_{(A_i,α)} for
  i ≥ 2, and D⁽¹⁾_{(A₁,α)} = E where D⁽⊤⁾_{(**A**₁/δ, α/δ)} = {E} (E is a δ-block, i.e. an element of
  A₁/δ). Applying τ₁ to the generators lands in R⁽¹⁾. Make it 1-consistent by projecting:
  D⁽²⁾ᵢ := pr_i(R⁽¹⁾). Then |D⁽²⁾_{(**A**ᵢ,α)}| = 1 for i ≥ 2. Iterate Theorem 45 (its case 2 strictly
  shrinks, so it terminates) to land in:
  * **Subcase 1** — a symmetric 1-consistent D⁽³⁾ ⋘ D⁽²⁾ with all singletons. Any γ ∈ R⁽³⁾ is
    Perm-block-constant; write γ = τ(γ₁,…,γ_n); then τ^{**A**ᵢ}(α) = γ(**A**ᵢ,α), hence τ^{**A**ᵢ}
    is XY-symmetric. ∎
  * **Subcase 2** — a perfect linear congruence σ on some D⁽⁰⁾_{(**A**₁,α)} with
    D⁽²⁾×D⁽²⁾ ⊄ σ. Argue D⁽⁰⁾_{(**A**₁,α)} = A₁ (else that subalgebra is in the list, and the
    diagonal identification γ(**A**_k,α) = γ(**A**₁,α) forces |D⁽²⁾_{(**A**₁,α)}| = 1). Then δ ⊄ σ,
    and minimality of δ forces σ = 0_{**A**₁}. Apply Theorem 47 to
    **A**₁/0\* × **A**₂ × … × **A**_s. ∎

Theorem 2 then follows: Maróti–McKenzie (Lemma 26) gives a special WNU w ∈ Clo(f) of arity N = n^{n!};
Theorem 48 gives w′ ∈ Clo(w) XY-symmetric of arity N; identify variables in blocks of n^{n!−1} to get
the n-ary f′.

## 4.3 Theorem 49, lines 445–575 (the "shrink a symmetric reduction" workhorse)

Notation S ↓^{(**A**_j,β)}_B := S with coordinate (**A**_j,β) restricted to B. Choose (**A**_j,β) and
B of type 𝓣 such that R ↓^{(A_j,β)}_B is **inclusion-maximal**. Section-2 propagation gives
R⁽¹⁾ ↓_B ≤_𝓣^R R⁽¹⁾ and, for C := pr_{(A_j,α)}(R⁽¹⁾↓_B), C ≤_𝓣 D⁽¹⁾_{(A_j,α)}. Maximality ⟹ if
C ≠ D⁽¹⁾ then R⁽¹⁾↓^β_B = R⁽¹⁾↓^α_C.

* **Case 1** — some α ∈ Perm(β), α ≠ β, with pr_{(A_j,α)}(R⁽¹⁾↓^β_B) ≠ pr_{(A_j,α)}(R⁽¹⁾). Then
  R⁽¹⁾↓^β_B is invariant under Stab(α) and under Stab(β); "since we can compose such permutations,
  α ≠ β, and n is odd" it is fully symmetric. Set D⁽²⁾ := its projections.
* **Case 2** — otherwise. Put S = ⋂_{α ∈ Perm(β)} R⁽¹⁾↓^α_B; S is symmetric. If S ≠ ∅, use it. If
  S = ∅, "by Corollary 22 there must be α₁, α₂ ∈ Perm(β) with R⁽¹⁾↓^{α₁}_B ∩ R⁽¹⁾↓^{α₂}_B = ∅";
  applying the σ with β = σ(α₁) contradicts this via the Case-2 hypothesis.

## 4.4 Theorem 46, lines 684–863 (the hardest proof in the section)

Build a chain of symmetric reductions D⁽ˢ⁾ ⋘ … ⋘ D⁽¹⁾ ⋘ D⁽⁰⁾ together with congruences δ^j_i on D⁽⁰⁾ᵢ
maintaining, for every level j:

1. δ^j_{(A_i,α)} = δ^j_{(A_i,β)} for β ∈ Perm(α);
2. ∃ γ ∈ R^{(j)} with (γ(**A**ᵢ,α), γ(**A**ᵢ,β)) ∈ δ^j_{(A_i,α)} for every index and every β ∈ Perm(α);
3. δ^{j+1}_i ⊇ δ^j_i;
4. the δ^j are chosen **minimal** subject to (2) and (3);
5. either δ^j = δ^{j+1} componentwise, or D^{(j+1)} ≤_𝓣 D^{(j)} for some 𝓣 ∈ {𝓑𝓐, 𝓒}.

Start with δ⁰ = equality. At each step, by Lemma 13 (Ubiquity):

* **Case 1** — a 𝓑𝓐/𝓒 subuniverse exists in some D^{(s)}ᵢ ⟹ Theorem 49 shrinks; re-choose δ freely.
* **Case 2** — all singletons ⟹ **done**, output D⁽△⁾ and the term τ.
* **Case 3** — take the **maximal** ℓ ≤ s with |D^{(s)}ᵢ / δ^ℓ_i| > 1 for some i. Ubiquity on the
  quotient gives B′ <_{𝓣(σ′)} D^{(s)}ᵢ/δ^ℓ_i; if 𝓣 ∈ {𝓑𝓐,𝓒} we are back in Case 1 (via Cor 16 + Lem 20),
  so 𝓣 = 𝓓. Lift σ′ to an irreducible σ ⊇ δ^ℓ_i on D⁽⁰⁾ᵢ.
  * **3.1, ℓ = s** — restrict all of Perm(i) to the σ-block containing γ(i); project; recurse.
  * **3.2, ℓ < s** — then σ ⊉ δ^{ℓ+1}_i, and minimality of δ^{ℓ+1} means R^{(s)} has no tuple lying in
    a single σ-block across Perm(i); Lemma 50 makes σ **perfect linear**, giving ζ. Build the
    conjunctive formula Θ over variables {x_j : j ∈ I} ∪ {z_{i′} : i′ ∈ Perm(i)} with constraints
    δ^{ℓ+1}_j(x_j, x_{j′}), ζ(x_i, x_{i′}, z_{i′}), and one copy of R. Then Θ^{(ℓ+1)} is unsatisfiable
    with all z = 0 but satisfiable for some z; Θ^{(ℓ)} is satisfiable with all z = 0. By condition (5),
    D^{(ℓ+1)} ≤_𝓣 D^{(ℓ)} with 𝓣 ∈ {𝓑𝓐,𝓒}, so the z-projections satisfy L₀ <_𝓣 L₁ ≤ **Z**ₚ^{|Perm(i)|}
    (Lemma 19) — contradicting Lemma 29. **Case 3.2 is impossible.**

## 4.5 §4.4 — "fixing an operation" (Theorem 47), lines 869–1639

1. **Lemma 51** establishes the ζ-calculus (uniqueness, p ∣ n−1, the "reflection" identity
   w(a,…,b,…,a) = b on 0\*-related pairs, cancellation, additivity).
2. **Theorem 52** builds **C** = (A/0\* × **Z**ₚ; w^**C**) by picking a transversal φ of the 0\*-classes
   and setting the **Z**ₚ-component to the *defect cocycle*
   ζ(w^**A**(φ(x⁽¹⁾)), φ(w^{**A**/0\*}(x⁽¹⁾))) + Σ xᵢ⁽²⁾. The map h(a) = (a/0\*, ζ(a, φ(a/0\*))) is an
   injective homomorphism, and w^**C** is verified to be idempotent, WNU and special, i.e. **C** ∈ 𝒱ₙ.
3. **Lemmas 53–57** develop the calculus of tᶠ₀: replacing one leaf changes the first component not at
   all and shifts the second component by exactly the leaf's second-component difference (Lemma 55);
   (tᶠ₀)⁽²'²⁾ stays Σxᵢ (Lemma 56); alternating sums are available (Lemma 57, notation ⊕/⊖).
4. **Lemma 58** is the engine: given two bad tuples α, β with f⁽²'¹⁾(α) ≠ f⁽²'¹⁾(β), set

   g(y₁,…,y_n) := ⊕_{γ ∈ T^{n,k+1}_{a,b}} [ (f⁽²'¹⁾(α) − f⁽²'¹⁾(γ)) / (f⁽²'¹⁾(β) − f⁽²'¹⁾(α)) ] ·
                    ( t^{f, ξ(γ,β)}_{0, ξ(γ,α)}(y) ⊖ tᶠ₀(y) ) ⊕ f(y₁,…,y_n)

   a **Z**ₚ-affine correction that leaves the first component and all previously-achieved symmetries
   untouched (each ξ-substitution is inert on tuples other than γ) while forcing weak symmetry at level
   k+1. The verification is a three-line cancellation of the displayed quotient.
5. **Corollary 59** iterates: increase k up to n−1, then add the pair (a,b) to P, then repeat until P is
   everything.
6. **Theorem 60** finally symmetrizes the first coordinate by a cyclic composition
   t = w(τ(x₁,…,x_n), τ(x₂,…,x_n,x₁), …, τ(x_n,x₁,…,x_{n−1})), which turns *weak* symmetry into full
   symmetry because the n cyclic shifts of a 2-valued α contain each starting letter N_a(α)/N_b(α) times.
7. **Theorem 47** = Theorem 52 + Theorem 60 applied to **D** = **C** × **B**.

---

# 5. Gaps, abuses, and quantifier hazards

Ordered roughly by how much they would hurt a formalization.

### G1 — `\Pol(σ_{B×ℤ})` is an undefined symbol (lines 1322, 1336)
Lemmas 55 and 56 are stated for "f ∈ Pol(σ_{B×ℤ})". The symbol σ_{B×ℤ} **appears nowhere else in the
paper**. It is a fossil of the commented-out Lemma `RelationDefinesBoxtimesLEM` (lines 1097–1180), which
defined Δ_{B×**Z**ₚ} = (x₁⁽¹⁾ = x₂⁽¹⁾ ∧ x₃⁽¹⁾ = x₄⁽¹⁾ ∧ x₁⁽²⁾ − x₂⁽²⁾ = x₃⁽²⁾ − x₄⁽²⁾) and proved
Pol(Δ) = 𝓒_{B⊠**Z**ₚ}. **Intended reading: f ∈ 𝓒_{B⊠**Z**ₚ}.** A formalizer must either adopt that
reading or resurrect the commented lemma (it is fully written out and correct-looking).

### G2 — Theorem 47's invocation of Theorem 60 has a hypothesis mismatch (line 1633)
Theorem 60 requires the **basic operation** w^**B** of the quotient to be XY-symmetric. Theorem 47's
hypothesis only gives that **A**/0\* × **B** has an XY-symmetric **term** operation, and the proof simply
says "By Theorem 60 there exists a term τ such that τ^**D** is XY-symmetric". Replacing the basic
operation by the term is *not* legitimate here: 𝒱ₙ demands a **special idempotent WNU** basic operation,
which a general XY-symmetric term need not be.
*Repair (not in the paper, but it works):* run the argument with g := the cyclic composition
w^**D**(τ(x₁,…,x_n), τ(x₂,…,x_n,x₁), …). One checks g ∈ 𝓒, g⁽¹⁾ XY-symmetric, and
g⁽²'²⁾ = (Σcᵢ)·Σxᵢ = Σxᵢ since Σcᵢ = 1 by idempotence. That is exactly the hypothesis package Corollary 59
consumes. **This is the most serious defect I found and it must be fixed in the blueprint.**

### G3 — "(w^**C**)⁽²⁾(x′,…,x′,y′) = 0" is false as stated (line 1071)
In Theorem 52's speciality verification, comparing second components of the special identity on h(A)
yields only

    F(x⁽¹⁾,…,x⁽¹⁾, w^**B**(x⁽¹⁾,…,x⁽¹⁾,y⁽¹⁾)) = 0    (†)

where F = (w^**C**)⁽²'¹⁾ — i.e. vanishing on the *image* of x ∘ (−), not for arbitrary y′. The general
claim "(w^**C**)⁽²⁾(x′,…,x′,y′) = 0" would say F(x⁽¹⁾,…,x⁽¹⁾,y⁽¹⁾) = 0, which is the defect cocycle and
is generally nonzero. The displayed chain that follows ("= 2·(w^**C**)⁽²⁾(x′,…,y′) + 2(n−1)x⁽²⁾ + y⁽²⁾")
conflates the two terms. **The conclusion is still correct**: expanding honestly gives
F(x⁽¹⁾,…,w^**B**(…)) + (n−1)x⁽²⁾ + F(x⁽¹⁾,…,y⁽¹⁾) + (n−1)x⁽²⁾ + y⁽²⁾, and (†) kills the first term while
p ∣ n−1 (Lemma 51(2)) kills 2(n−1)x⁽²⁾ ↦ (n−1)x⁽²⁾. A blueprint must rewrite this proof.

### G4 — Two "we derive that" steps are real group theory
* **Line 517** (Theorem 49, Case 1): "Since we can compose such permutations, α ≠ β, and n is odd, we
  derive that R⁽¹⁾↓_B is σ-symmetric for any σ." The content is: *for α ≠ β ∈ {a,b}ⁿ with the same
  number of b's and n odd, Stab(α) and Stab(β) generate S_n.* Non-trivial, and the oddness is
  load-bearing: for n = 4, α = aabb, β = bbaa the two Young subgroups coincide (S₂ × S₂ ≠ S₄). Proof
  sketch: with K, K′ the b-position sets, |K| = |K′| = k, K ≠ K′; n odd forces K′ ≠ Kᶜ; the generated
  group is transitive and contains a transposition, hence (primitivity) equals S_n. **State and prove
  this as a standalone combinatorial lemma.**
* **Line 599** (Lemma 50): "Since pr_{(Aᵢ,α₁),(Aᵢ,α₂)}(R) is **linked**…" — never justified. It is true
  and again uses **n odd**: the projection contains the pairs (α₁(k), α₂(k)) for k ∈ [n]; α₁ ≠ α₂ are
  permutations of each other so both (a,b) and (b,a) occur, and — because n is odd, α₂ cannot be the
  pointwise complement of α₁ — they must **agree somewhere**, contributing (a,a) or (b,b), which
  connects the bipartite graph on {a,b} and hence (by generation) all of Sg({a,b}). **Also a standalone
  lemma.**

### G5 — Corollary 22 (`CORMainStableIntersection`) is applied past its statement, twice
* **Line 550** (Theorem 49, Case 2): "S = ∅ ⟹ by Corollary 22 there must be α₁, α₂ with pairwise empty
  intersection." Corollary 22's conclusions are (ba) all types 𝓑𝓐 (**no bound on n**), (l) all 𝓛 plus
  bridges, (c) n = 2 and 𝓒, (pc) n = 2 and 𝓟𝓒. Branches (c)/(pc) give the desired n = 2 after passing to
  an inclusion-minimal empty subfamily (which the text does not do), but branch **(ba) does not**. The
  missing ingredient is the classical fact that binary absorbing subuniverses of a common finite algebra
  always intersect (Zhuk, *Strong subalgebras and the CSP*), so (ba) cannot occur with an empty
  intersection. **Neither the minimal-subfamily reduction nor the (ba) exclusion is written down.**
* **Line 593** (Lemma 50): same shape. Here all types are 𝓓 = 𝓛 or 𝓟𝓒, so branch (l) gives the bridge
  and branches (ba)/(c) are excluded by type, but branch **(pc)** must be excluded by hand: it asserts
  n = 2 with {(a/σ₁, b/σ₂)} bijective, which is incompatible with the projection being linked (unless
  the quotient is trivial). Not written down.
* Also relevant: Corollary 22 is stated for **distinct** coordinates; here several restrictions land on
  coordinates of the same relation. The paper's Remark 1 (main.tex:1838) says "duplicate the coordinate
  and apply restrictions separately", which a formalization must actually implement.

### G6 — Theorem 2 is missing the idempotency hypothesis
"Suppose f is a WNU operation of an odd arity n on a finite set." The proof immediately invokes Lemma 26,
which requires an **idempotent** WNU, and then works in 𝒱_N (idempotent special WNU). main.tex:408
defines WNU without idempotency; main.tex:1123 declares a *global* standing assumption
("every algebra is a finite idempotent algebra having a WNU term operation") which presumably covers it.
**The Lean statement must carry `Idempotent f`.** (Corollary 3 is about idempotent algebras, so no harm
there.)

### G7 — Well-foundedness of Theorem 48's induction is asserted, not proved
Three separate issues:
1. The measure is "the infinite tuple (|A₁|,…,|A_s|,0,0,…) in lexicographic order" after sorting
   descending — this is really the Dershowitz–Manna multiset order on the multiset of sizes.
   Well-foundedness on finite multisets of naturals is fine (Mathlib has `Multiset.IsWellFounded`/
   `Finsupp.Lex`), but the paper's "infinite tuple + lex" phrasing is not literally well-founded on
   arbitrary sequences; you must restrict to eventually-0 sequences (Finsupp) or use the multiset order.
2. "**We add all nontrivial subalgebras of A₁ to the list and prove even stronger claim**" — the
   augmented list has a **larger** measure, so this is not an application of the IH; it is a
   strengthening of the goal. The proof only works because in both cases the recursive calls drop the
   top element |A₁| and replace it with strictly smaller ones. That decrease is never verified. Case 2
   is the delicate one: if |A₂| = |A₁| the first coordinate does not drop, and one must argue at the
   first position where the sorted tuples differ.
3. "nontrivial subalgebra" is undefined here. For the measure argument it must mean **proper**
   subalgebra with ≥ 2 elements; if it included **A**₁ itself the induction would not terminate.
   *(main.tex:1096 defines "nontrivial" only for congruences: "not the equality relation and not A²".)*

### G8 — The δ-block lifting in Theorem 48 Case 2 is under-specified (lines 317–337)
"Put D⁽¹⁾_{(**A**₁,α)} = E whenever D⁽⊤⁾_{(**A**₁/δ, α/δ)} = {E}."
* If the two distinct entries of α are δ-equivalent then **α/δ is a constant tuple**, so
  (**A**₁/δ, α/δ) is **not an index** of R_{**A**₁/δ,…} — D⁽⊤⁾ is undefined there. The natural uniform
  fix: define D⁽¹⁾_{(**A**₁,α)} := the δ-block containing τ₁^{**A**₁}(α) (which coincides with E in the
  non-degenerate case, by idempotency in the degenerate one). Not stated.
* A reduction must satisfy D⁽¹⁾ᵢ ≤ D⁽⁰⁾ᵢ = Sg(α); a δ-block E need not be contained in Sg(α). One must
  intersect. Not stated.
* The citation "By Corollary 17(t) and Corollary 18(r1) we have D⁽²⁾ ⋘ D⁽⁰⁾" looks wrong: the step
  "singleton in the quotient ⟹ ⋘ upstairs" is exactly **Corollary 16** (`CORPropagateFromFactor`),
  not Corollary 17. Worth re-deriving from scratch.

### G9 — Lemma 55 is stated with no proof at all
"The next lemma follows immediately from the definition of tᶠ₀ and t^{f,(j)}_{0,(i)}" (line 1305).
The content is a structural induction over an nⁿ-leaf term tree: (a) if the substituted leaf's *first*
component is unchanged, all downstream first components are unchanged; (b) the *second* component of the
root is affine in each leaf's second component with coefficient exactly 1 (because f⁽²'²⁾ = Σ and the
tree has depth n). Both are easy but neither is a one-liner in Lean. Same for the "exactly one internal
occurrence f(y_{i₁},…,y_{i_n}) for every (i₁,…,i_n) ∈ [n]ⁿ" claim at line 1232.

### G10 — The ⊕/⊖ notation controls only the ⁽²'²⁾ part, but Lemma 58 reasons about ⁽¹⁾ and ⁽²'¹⁾
Line 1379: "Notice that we use this notation if the only important part of the obtained operation f is
f⁽²'²⁾." Yet Lemma 58 defines g with that notation and then proves statements about g⁽¹⁾ (property 2) and
g⁽²'¹⁾ (properties 4, 5), and the displayed computation of g⁽²'¹⁾(δ) − g⁽²'¹⁾(δ′) treats g⁽²'¹⁾ as
literally the **Z**ₚ-linear combination of the arguments' ⁽²'¹⁾ parts. That is only correct up to an extra
term — the outer Malcev-like operation's own ⁽²'¹⁾ evaluated at the (common) first components of its
arguments. It cancels in the difference **because** all the arguments' first components agree on δ and δ′
(XY-symmetry of f⁽¹⁾ and of (tᶠ₀)⁽¹⁾). **Not stated.** This is exactly the sort of silent step that
breaks a formalization.

### G11 — Lemma 57 ("Generalized Malcev") is asserted in one sentence
"Consider a term defining x₁ − x₂ + x₃ − … + x_{2m+1} from x₁ + x₂ + … + x_n in **Z**ₚ. The same term
defines the required g from f." The real statement is a small clone-theoretic fact:
*for n ≡ 1 (mod p), the clone generated by (x₁,…,x_n) ↦ Σxᵢ on **Z**ₚ contains every Σaᵢxᵢ with Σaᵢ = 1.*
Also, when the ⊕/⊖ notation writes "a_i copies" for a_i ∈ **Z**ₚ, an integer representative in
{0,…,p−1} is silently chosen.

### G12 — Notational collisions and typos that will bite a transcriber
* **`s` is overloaded** in Theorem 46's proof: it is both the number of algebras **A**₁,…,**A**_s and the
  index of the reduction chain D⁽⁰⁾,…,D⁽ˢ⁾ ("We start with s = 0", line 727). Rename before writing
  anything.
* Line 60/64: "R_{**A**₁,…,**A**_n}" should be "R_{**A**₁,…,**A**_s}" (three occurrences).
* Line 62: "|A_i − 1|" should be "(|Aᵢ| − 1)".
* Line 55: "α ∈ TwoTuples(Aⁿ)" should be "TwoTuples(Aᵢⁿ)".
* Line 449–450: "denote S whose coordinate (**A**_j,β) is restricted to **S**" — should be **B**.
* Line 491: "C = pr_{(**A**_i,α)}(…)" — the algebra index should be **j**, matching β.
* Line 486: "Lemma 20(**it**)" — Lemma 20 has items (i) and (t); "(it)" is not an item.
* Line 804: "Put δ^s_{i′} = δ^{s+1}_{i′}" — assignment direction reversed.
* Line 1222: `t_{e\\}^{f}` — garbled LaTeX; should be tᶠ_ℓ.
* Line 1349: "Σ_{i₁,…,i_n∈[n]}(x_{i₁}⁽²⁾+…+x_{i_n}⁽²⁾) = n^{n−1}(x_{i₁}⁽²⁾+…)" — the summation indices
  are bound and then reused free; should be n^{n−1}(x₁⁽²⁾+…+x_n⁽²⁾), and n^{n−1} ≡ 1 because n ≡ 1 (mod p).
* Corollary 59's conclusion says "**h** is weakly symmetric on all tuples having two different elements";
  it must be **h⁽²'¹⁾**.
* Theorem 47's conclusion omits "of arity n" although its hypothesis and every use require it.

### G13 — Implicit facts used without statement
* **R_{A₁,…,A_s} is symmetric** (§2.4 above). Used at least at lines 502, 654, and every application of
  Theorem 49 to R.
* **Sg(γ₁,…,γ_n) = {τ(γ₁,…,γ_n) : τ an n-ary term}** — the "term ↔ generated element" bridge, used to
  extract τ in Theorem 48 Subcase 1 and Theorem 46 Case 2.
* **γ(**A**_k,α) = γ(**A**₁,α) for all γ ∈ R when **A**_k = Sg(α) ≤ **A**₁** (line 365) — true because
  the generators agree there and **A**_k is a subalgebra so the operations agree; a one-line lemma but
  needed.
* **σ perfect linear ⟹ σ\* is a congruence** — required to form **A**/0_**A**\* (Theorem 47, Theorem 52).
  The definition of *perfect linear congruence* (main.tex:1295) only says "irreducible + ∃ζ"; the fact
  that it is then *linear* in the sense of main.tex:1368 (and hence σ\* is a congruence) goes through
  Lemma 7 (`LEMLinearEquivalentConditions`) with the bridge δ(x₁,x₂,y₁,y₂) := ∃z (ζ(x₁,x₂,z) ∧ ζ(y₁,y₂,z)).
  Never spelled out.
* **𝒱ₙ is closed under subalgebras, quotients and finite products** — used constantly.
* **𝓒_{B⊠**Z**ₚ} is a clone** — used when composing in Lemmas 57/58 and Theorem 60.
* In Theorem 46's Subcase 3.2, "Θ^{(ℓ+1)} is satisfied for some z" needs a witness; the honest witness is
  *any* γ ∈ R^{(s)} (which is δ^{ℓ+1}-block-constant because ℓ was chosen maximal, and lies inside σ\*
  because D^{(s)}ᵢ × D^{(s)}ᵢ ⊆ σ\* from the 𝓓-type definition). The chain is short but entirely implicit.
* Θ^{(j)} for a *conjunctive formula* Θ (restrict the domain of each x-variable by D^{(j)}, leave the
  **Z**ₚ-valued z-variables alone) is never defined in Section 4; it is borrowed by analogy from
  Section 3's instance notation.
* Lemma 19 (`LEMBACenterImplies`) is stated for the projection onto **coordinate 1**; Theorem 46's
  Subcase 3.2 projects onto the **whole block of z-variables**. A grouped-coordinate version is needed
  (routine, but must be stated).

### G14 — Dead branch: Theorem 49's 𝓟𝓒 case is never used
Theorem 49 admits 𝓣 ∈ {𝓑𝓐, 𝓒, 𝓟𝓒}, and its proof contains the caveat "below we assume that D⁽¹⁾ is
S-free whenever 𝓣 = 𝓟𝓒" plus the weaker conclusion for 𝓟𝓒. Both call sites (lines 633 and 748) invoke it
only with 𝓣 ∈ {𝓑𝓐, 𝓒}. **A formalization can state Theorem 49 for 𝓣 ∈ {𝓑𝓐, 𝓒} only**, dropping the
S-free caveat and the "Moreover" clause. Genuine saving.

### G15 — Theorem 45's conclusion 3(a)/(b) are not re-derived in its proof
The proof ends "Then by Lemma 50 condition 3 is satisfied", but Lemma 50 only produces "σ is a perfect
linear congruence". Items (a) and (b) come from unfolding the definition of
B <_{𝓓(σ)}^{D⁽⁰⁾} D⁽¹⁾: (b) is clause 1 of the 𝓓 definition (B² ⊆ σ\*), and (a) follows from clause 2
(B = D⁽¹⁾ ∩ E for a σ-block E) together with B ⊊ D⁽¹⁾. Easy, but must be written.

---

# 6. Formalization cost, and is it worth it?

## 6.1 What Section 4 adds on top of an already-formalized Sections 2 + 5

**Zero new Section-2 theory.** Its imports are a subset of Section 3's plus Lemma 5 (a 10-line corollary
of two lemmas Section 3 already needs) and Lemma 26 (an external cite the dichotomy needs anyway).

**New definitional surface** (≈ 12 definitions): TwoTuples / the dependent index type I; R_{A₁,…,A_s};
reductions over I + 1-consistency; the S_n action on tuples/relations/reductions; symmetric reduction;
k-WNU; XY-symmetric; weakly-symmetric-at-a-tuple; ⊠-product and the clone 𝓒_{B⊠**Z**ₚ}; the tᶠ_ℓ tower
and the leaf-replacement notation; ξ(α,β) and T^{n,k}_{a,b}; (P,a,b,k)-symmetric.

**New statements:** 8 theorems + 8 lemmas + 1 corollary, plus (from §5 above) roughly **10 auxiliary
lemmas that the paper does not state at all** — the symmetry of R, the term/generation bridge, the two
group-theory lemmas of G4, the BA-intersection fact of G5, the grouped-coordinate Lemma 19, the
𝒱ₙ-closure facts, the clone-hood of 𝓒, the σ\*-is-a-congruence fact, the **Z**ₚ-clone fact of G11.

**New infrastructure that Section 3 does not need:**
* A `Equiv.Perm (Fin n)` action on a *dependent* index type, with the "symmetric reduction / symmetric
  relation" API. Mathlib has the group theory; the plumbing is on you.
* A well-founded multiset order on tuples of algebra sizes (G7). Mathlib: `Multiset` DM order or
  `Finsupp.Lex`. Non-trivial to set up but standard.
* A term-tree induction package for tᶠ₀ (G9) — nⁿ leaves indexed by `Fin n → Fin n`, with a
  single-leaf-replacement operation. This is the least Mathlib-shaped part.
* **Z**ₚ-affine calculus on operations (f⁽²'¹⁾ / f⁽²'²⁾ decomposition). Mathlib's `ZMod p` and module
  API cover the algebra; the decomposition lemmas are bespoke.

## 6.2 Sizing

| | pages | LaTeX lines | new defs | numbered stmts | new infra |
|---|---|---|---|---|---|
| §2 + §5 (theory) | 7 + 17 = 24 | ~4000 | ~25 | ~60 | congruence/bridge theory |
| §3 (dichotomy) | 11 | ~2190 | ~20 | ~45 | CSP instances, cycle-consistency, expanded coverings |
| **§4.1–4.3** | **5** | **864** | **~7** | **5** | S_n action, multiset induction, term↔generation |
| **§4.4** | **5** | **775** | **~5** | **11** | term trees, **Z**ₚ-affine calculus |

My estimate: **Section 4 costs roughly 30–45% of what Section 3 costs**, and roughly **12–18% of the
whole project (§2 + §3 + §5)**. §4.4 will cost *more* than its page count suggests (dense computation,
three of the four worst defects, essentially no reusable Mathlib), while §4.1–4.3 will cost *less*
(it is the same reduction-chasing idiom as Section 3, on a smaller and cleaner index structure).

The critical caveat: **§4 is cheap only if §2 + §5 are already done.** On its own it is not cheap at all —
§4.1–4.3 sits directly on Corollary 22 (`CORMainStableIntersection`), the deepest theorem in the paper.
§4.4, by contrast, is genuinely cheap standalone (see §0.4).

## 6.3 Recommendation

**Yes, include it — as a clearly-labelled stretch goal, sequenced last, and split in two.**

Reasons for:
1. **Zero risk to the main line.** It is a leaf in the dependency graph. It cannot block, delay, or
   destabilise the dichotomy formalization, and it can be dropped at any point without rework.
2. **Its statement is trivially Lean-able**, unlike the dichotomy. Theorem 2 is
   `∀ (A : Type) [Finite A] (f : (Fin n → A) → A), Odd n → IdempotentWNU f → ∃ f' ∈ Clo f, XYSymmetric f'`.
   No algorithms, no complexity classes, no Turing machines, no P-vs-NP interface. The dichotomy's
   *statement* alone is a substantial modelling problem; this one is not. That makes it a far better
   candidate for an early, self-contained, quotable Mathlib-facing result.
3. **Its cheapest half is independent of everything.** §4.4 (Theorems 51/52/53–60) needs only the
   definition of a perfect linear congruence and 𝒱ₙ. It is a perfect "week 1, parallel track,
   confidence-building" module, and it exercises exactly the **Z**ₚ/clone machinery that Sections 2 and 5
   will also need.
4. **It pays a debt to Corollary 3**, which is the kind of statement (six equivalent characterisations of
   Taylor algebras) that a Mathlib-facing project actually wants.
5. **It re-uses 100% of Sections 2 + 5** and needs no new theory there, so the marginal cost is bounded
   and predictable.

Reasons for caution:
1. **§4.4 is the buggiest prose in the paper.** G1 (undefined symbol), G2 (genuine hypothesis mismatch,
   needing a repair the paper does not give), G3 (a false intermediate claim), G9/G10/G11 (three
   "obvious" steps that are structural inductions or clone lemmas) all live there, in six pages. Budget
   *at least* 2× the naive page-proportional estimate.
2. **The Theorem 48 induction (G7) is the kind of thing that eats a week in Lean** — a multiset order,
   plus an "augment the list, then argue the measure still drops" step that the paper does not verify.
3. **Two hidden group-theory lemmas (G4)** need to be found and proved before anything in §4.3 typechecks.
4. It adds ~15% to the surface area of an already very large project while advancing the headline theorem
   by exactly zero.

**Concrete sequencing proposal.**
* *Phase 0 (parallel, any time):* `Zhuk/XYSym/Boxtimes.lean` — §4.4 in full (Lemmas 51, 53–57, Theorems
  52, 60, Corollary 59, Lemma 58, and Theorem 47). Depends only on `PerfectLinearCongruence`, `𝒱ₙ`,
  `ZMod p`, `Clo`. ~1500–2500 lines. Do the G2 repair explicitly in the blueprint before writing Lean.
* *Phase 1 (after §2 + §5 land):* `Zhuk/XYSym/FreeRelation.lean` (the index type, R, reductions, the
  S_n action, and the two G4 lemmas) then `Zhuk/XYSym/Reduction.lean` (Theorems 49, 45, Lemma 50) then
  `Zhuk/XYSym/BuildReduction.lean` (Theorem 46).
* *Phase 2 (last):* `Zhuk/XYSym/Main.lean` — Theorem 48 (the multiset induction) + Theorem 2 + Corollary 3.

Do **not** put Section 4 on the critical path to the dichotomy, and do not let its blueprint chapters
block Section 3's. Mark the whole chapter "independent second result" in the blueprint so nobody wastes
time trying to thread it into the main proof.

---

# 7. One-line summary for the route decision

Section 4 is a self-contained, strictly-downstream second theorem: it consumes Section 2 (a subset of what
Section 3 consumes) and is consumed by nothing. Formalize Sections 2 + 5 + 3 first; keep Section 4 as an
optional stretch chapter whose §4.4 half can be started immediately and in parallel, and whose §4.1–4.3
half is a small replay of Section 3's reduction idiom on a cleaner index structure — but budget for ~10
unstated auxiliary lemmas, one genuine proof gap (G2), one false intermediate claim (G3), one undefined
symbol (G1), and a well-founded-induction argument (G7) that the paper does not verify.
