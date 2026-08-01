# The hard half: WNU-free ⟹ CSP(Γ) is NP-complete

**Scope.** Everything below concerns *only* the hardness direction. Sources read:

* `papers/2005.00593.txt` — Zhuk, *Strong subalgebras and the Constraint Satisfaction
  Problem*, JMVLSC 2021 (arXiv 2005.00593v1). Read in full for §§1–5.3 and §6.8; §6
  statement list enumerated. This is the only source on disk that contains a
  **self-contained** hardness proof.
* `zeb/csp.tex` — Brady, *Notes on CSPs and Polymorphisms* (17k lines). Read: §"Crash
  course on NP-completeness" (L701–1190), §"The Inv-Pol Galois connection" (L1193–1560),
  §"Varieties, Birkhoff's HSP theorem, and the hardness proof" (L1880–2045), §"Cores and
  Idempotent Reducts" + §"Reflections and Height 1 Identities" (L2046–2334), §"Taylor
  Algebras" (L2336–2470), §"Cyclic terms" (L14873+, skimmed).
* `papers/2104.11808.txt` — Barto–Brady–Bulatov–Kozik–Zhuk, *Minimal Taylor algebras…*
  §§1–2.3. Used only for the pp-interpretability formulation of the dichotomy; the paper
  **does not prove** hardness, it cites it.
* `papers/src2404/main.tex` — Zhuk 2404.01080. Confirms that the paper the blueprint is
  based on **does not prove hardness either**: main.tex:431, "The NP-hardness for
  constraint languages without a WNU follows from [bulatov2001algebraic, CSPconjecture]
  and [miklos]" (= Bulatov–Jeavons–Krokhin and Maróti–McKenzie).
* Mathlib at `/home/alvaro/claude/zhuk-lean/.lake/packages/mathlib`, audited file by file
  under `Mathlib/Computability/`, plus `Mathlib/ModelTheory/` and
  `Mathlib/Combinatorics/Optimization/ValuedCSP.lean`.

**Headline.** The hardness half splits cleanly into three layers with wildly different
formalization costs:

| Layer | Content | Cost |
|---|---|---|
| **A. Algebra** | no WNU ⟹ a *WNU-blocker* (an NAE-shaped relation) is pp-definable over the constant-expanded core | very large (Zhuk §§3,4,6 ≈ 35 pp.), but self-contained |
| **B. Gadget** | pp-definable NAE-shape + core trick ⟹ an explicit satisfiability-preserving map of instances, with a linear size bound | small (~1–2k Lean lines), fully rigorous, no computation model needed |
| **C. Complexity** | "that map is a polynomial-time many-one reduction" and "NAE-3SAT is NP-hard" | Mathlib has **nothing**; honest options are to axiomatize the seed or to skip layer C entirely |

The recommendation (§7) is: **prove A and B as theorems, state C as a clearly-marked
interface with the seed hardness as an explicit hypothesis, never as a `sorry`.**

---

## 1. What exactly is to be proved

Zhuk 2005.00593, Theorem 5.5 (p. 20), verbatim:

> **Theorem 5.5.** [9, 24] Suppose Γ does not have a WNU polymorphism, then CSP(Γ) is
> NP-hard.

with references [9] = Bulatov–Jeavons–Krokhin, *Classifying the complexity of constraints
using finite algebras*, SICOMP 34(3):720–742, 2005; [24] = Maróti–McKenzie, *Existence
theorems for weakly symmetric operations*, Algebra Universalis 59:463–489, 2008.

Two conventions must be pinned down before anything else.

**Convention 1.1 (WNU is NOT required to be idempotent).** Zhuk 2005.00593 L116–120 and
2404 main.tex:409–411 both define: an operation `w : A^n → A` is a *weak near-unanimity
operation* if

```
w(y,x,x,…,x) = w(x,y,x,…,x) = ⋯ = w(x,…,x,y)   for all x,y ∈ A.
```

**No `w(x,…,x) = x` clause.** This is load-bearing: in the proof of Theorem 5.5 the WNU of
Γ is built as `w(x₁,…,x_m) = w'(f(x₁),…,f(x_m))` where `f` is a non-injective unary
polymorphism, and this `w` has `w(x,…,x) = f(x) ≠ x`. If you formalize WNU with an
idempotency clause, that step becomes false. Inside §4, by contrast, Zhuk works with
*idempotent* algebras, where every term operation is automatically idempotent, so the
distinction is invisible there — but it is a real trap at the §5 boundary.

Note also that under this definition a constant operation is a WNU; that is deliberate
(a language with a constant polymorphism is trivially tractable).

**Convention 1.2 (arity).** The WNU equations are vacuous for n = 1 and Zhuk never says
`n ≥ 3` in the definition, though every existence statement in §4 is for `n ≥ 3`.
A unary `w` satisfies the (empty) WNU condition trivially, so *literally* every Γ has a
WNU polymorphism (take `w = id`). **This is a genuine defect of the printed definition**
and must be repaired in a blueprint: the intended reading is `n ≥ 2` (equivalently `n ≥ 3`,
since Theorem 4.14(2) produces prime arities `p > |A| ≥ 2`). Formalize as: `∃ n ≥ 2, ∃ w :
A^n → A, w ∈ Pol Γ ∧ IsWNU w`. Check: for n = 2 the condition is `w(y,x) = w(x,y)`, i.e.
commutativity, which is the right notion.

**The target statement, cleaned up:**

> Let `A` be a finite nonempty set and `Γ` a finite set of finitary relations on `A`.
> If there is no `n ≥ 2` and no `w : A^n → A` preserving every `R ∈ Γ` with
> `w(y,x,…,x) = ⋯ = w(x,…,x,y)`, then CSP(Γ) is NP-complete.

Membership in NP is trivial (§3.9); the content is hardness.

---

## 2. Definitions, formalization-ready

Throughout `A` is a finite nonempty set, `n, m, k` arities.

### 2.1 Relations, constraint languages, instances

* **Relation of arity `n`:** `R ⊆ A^n`. Lean: `Set (Fin n → A)`.
* **Constraint language:** a set `Γ ⊆ R_A = {R ⊆ A^n | n ∈ ℕ}` (Zhuk §2.3 L225).
  For CSP(Γ) as a decision problem Γ must be *finite*; §4 uses `Inv(A)` which is infinite.
  A signature-indexed presentation is better for Lean: `sig : ι → ℕ`,
  `rel : (i : ι) → Set (Fin (sig i) → A)`.
* **Instance** (Zhuk §5.1 L753–757): a formula
  `R₁(v_{1,1},…,v_{1,n₁}) ∧ ⋯ ∧ R_s(v_{s,1},…,v_{s,n_s})`, `R_j ∈ Γ`, `v_{j,l} ∈ {x₁,…,x_N}`.
  Lean: a variable type `V` plus `List (Σ i : ι, Fin (sig i) → V)`.
  Repeated variables inside one constraint are allowed and are used by the proofs
  (e.g. `R(x,x,x,y)` in Lemma 4.9).
* **CSP(Γ):** decide whether an instance has a solution `s : V → A` with
  `∀ c ∈ constraints, rel c.1 (s ∘ c.2)`.

**Gap 2.1.** Zhuk never says whether the variable list `{x₁,…,x_n}` is part of the input
or is inferred, nor whether an instance may repeat a constraint, nor whether the empty
instance is allowed (it is satisfiable iff `A ≠ ∅`). Harmless, but a Lean formalization
must choose; choose "variables = an arbitrary `Fintype V`, constraints = a `List`".
Also: with `A = ∅` every nonempty instance is unsatisfiable and the empty one is
unsatisfiable too if `V` is nonempty. The whole theory assumes `|A| ≥ 1` silently.

### 2.2 Preservation, Pol, Inv

Zhuk §2.3 L226–233; Brady L234–239.

* `f : A^k → A` **preserves** `R ⊆ A^m` (`f ▷ R`, `f` is a *polymorphism* of `R`, `R` is
  an *invariant* of `f`) iff for all `α₁,…,α_k ∈ R`, the coordinatewise value
  `(f(α₁(1),…,α_k(1)), …, f(α₁(m),…,α_k(m)))` is in `R`.
  Lean: `∀ M : Fin k → Fin m → A, (∀ i, M i ∈ R) → (fun j => f (fun i => M i j)) ∈ R`.
* `Pol(Γ) = {f | ∀ R ∈ Γ, f ▷ R}`; `Inv(F) = {R | ∀ f ∈ F, f ▷ R}`;
  `Inv(𝐀) = Inv(basic operations of 𝐀)`.
* Equivalently (Brady L241): `f ▷ R` iff `R ⊆ A^m` is a subuniverse of `(A;f)^m`.
  This is the identification `Inv(𝐀) = subpowers of 𝐀` used constantly in §§3–4.

### 2.3 pp-formulas, pp-definability, relational clones, clones

Zhuk §2.3 L234–239, Brady L549–557 and L1199.

* A **pp-formula over Γ** is `∃y₁…∃y_n Φ` with `Φ` a conjunction of atoms `R(z_{i₁},…,z_{i_r})`,
  `R ∈ Γ`. Brady additionally allows equality atoms; Zhuk handles equality by declaring it
  a member of every relational clone.
* `R` is **pp-defined** by such a formula if `R(x₁,…,x_m) ⟺ ∃ȳ Φ(x̄,ȳ)`.
* A **relational clone** is a set of relations containing the equality relation
  **and the empty relation** (Zhuk L237–239; Brady omits the empty relation, see Gap 2.3)
  and closed under pp-definitions. `⟨Γ⟩ = RelClo(Γ)` is the relational clone generated.
  Equivalent generator-level description (Brady L213): contains `=`, closed under
  permutation of coordinates, adding dummy coordinates, existential projection,
  intersection.
* A **clone** is a set of operations containing all projections and closed under
  composition `f ∘ (g₁,…,g_k)` (Zhuk L219–224, Brady L223–227). `Clo(𝐀)` = term
  operations of `𝐀`.

**Gap 2.2 (pp-formula ≡ instance).** The identification "a pp-formula over Γ with `m`
free variables = an instance of CSP(Γ) with `m` distinguished variables, and the defined
relation = the projection of the solution set onto them" is used everywhere without
comment (it is what makes the gadget reduction work). Make it a *definition* in Lean, not
a lemma: define pp-definability *via* instances. Then Brady L204 ("any new relation which
can be built out of these four operations can be viewed as the solution set to some
instance of CSP(Γ), projected onto some subset of the variables") is true by construction.

**Gap 2.3 (the empty relation).** Zhuk puts `∅ ⊆ A^n` into every relational clone by
fiat, Brady does not. This matters for the Galois connection: `∅` is preserved by every
operation but is pp-definable from Γ only if Γ already forces unsatisfiability. Under
Zhuk's convention `Inv(Pol(Γ)) = ⟨Γ⟩` is fine; under Brady's it is fine too because
his `Pol` is over a *nonempty* domain and his proof (L1258) covers finitely generated
subalgebras, and `∅` is the subalgebra generated by 0 elements — which requires 0-ary
operations to exist. **Decision for Lean:** define relational clones with `∅` included
(Zhuk's convention), and state the Galois theorem for nonempty relations, treating `∅`
separately. This is the single most likely place to lose a day.

### 2.4 The Galois connection Pol/Inv

Zhuk §2.3 L240–244, citing [7] = Bodnarchuk–Kaluzhnin–Kotov–Romov 1969 and
[15] = Geiger 1968:

> Pol and Inv are mutually inverse bijective mappings between clones and relational
> clones… Precisely, for any algebra 𝐀 we have `Clo(𝐀) = Pol(Inv(𝐀))`, and for any
> `Γ ⊆ R_A` we have `RelClo(Γ) = Inv(Pol(Γ))`.

Only the second identity is needed for hardness, and only the inclusion
`Inv(Pol(Γ)) ⊆ ⟨Γ⟩`. Brady gives a **fully explicit, formalization-ready proof**
(csp.tex L1258–1272):

> **Theorem.** If Γ is a set of relations on a finite domain `D`, then `Inv(Pol(Γ)) = ⟨Γ⟩`.
> In fact, if `S ⊆ D^m` is preserved by `Pol(Γ)` and can be generated by `k` elements of
> `D^m`, then `S` can be defined by a pp-formula over Γ which involves at most `|D|^k`
> auxiliary variables.

The construction (worth recording in full because it is what a Lean proof will do):

1. Let `x₁,…,x_k ∈ D^m` generate `S`; let `X` be the `m × k` matrix with the `x_i` as
   columns, with rows `X_1,…,X_m ∈ D^k`.
2. Then `S = {f(X) | f ∈ Pol_k(Γ)}`. (⊆: `π_i(X) = x_i` and the right side is closed
   under `Pol(Γ)` because `Pol(Γ)` is a clone; ⊇: `S ∈ Inv(Pol(Γ))`.)
3. `Pol_k(Γ) ⊆ D^{D^k}` is pp-definable over Γ: use one variable `z_α` for each `α ∈ D^k`
   (interpretation: `z_α = f(α)`) and impose, for every `R ∈ Γ` of arity `r` and every
   `(α₁,…,α_r) ∈ (D^k)^r` such that `(α₁(i),…,α_r(i)) ∈ R` for all `i ≤ k`, the atom
   `R(z_{α₁},…,z_{α_r})`.
4. `S(u₁,…,u_m) ⟺ ∃(z_α)_{α ∈ D^k}  Φ(z) ∧ ⋀_j u_j = z_{X_j}`.

**Observation 2.4 (equality-free by construction).** Step 4 introduces equality atoms
`u_j = z_{X_j}`, but they can be eliminated by *taking the free variables to be the
variables `z_{X_j}` themselves*, provided the rows `X_1,…,X_m` are pairwise distinct.
`X_j = X_{j'}` iff every generator has equal `j,j'` coordinates iff (taking the generators
to be all of `S`) every tuple of `S` has equal `j,j'` coordinates. For the WNU-blocker
this is false. **So the pp-definition needed in Theorem 5.5 can be produced with no
equality atoms at all**, which removes the only hand-wave in Zhuk's Theorem 5.5 proof
(see Gap 4.7). This is a concrete simplification a formalization should adopt.

**Note.** For finite `A`, taking `k = |S|` and generators = all elements of `S` makes
step 1 unconditional (for `S ≠ ∅`), so no finite-generation hypothesis is needed. The
auxiliary-variable count is `|A|^{|S|}` — astronomically large but *constant in the input*.

### 2.5 pp-powers, pp-interpretability, pp-constructions

Not used by Zhuk's proof, but this is the language in which 2104.11808 states the theorem,
and in which the classical BJK reduction is packaged. Definitions from Brady L2219–2226:

* **pp-power** of `𝔄`: a structure `𝔅` with domain `A^n` such that each `m`-ary relation
  of `𝔅`, read as an `mn`-ary relation on `A`, is pp-definable over `𝔄`.
* **pp-interpretation** (standard, not in Brady in this form): `𝔅` is pp-interpretable in
  `𝔄` if there are `n`, a pp-definable `D ⊆ A^n`, a pp-definable equivalence `σ` on `D`,
  and a surjection `h : D ↠ B` with kernel `σ` such that `h^{-1}` of every relation of `𝔅`
  (and of `=_B`) is pp-definable over `𝔄`. pp-power = pp-interpretation with `D = A^n`,
  `σ = ` equality.
* **pp-construction** (Brady Defn L2225): `𝔄` pp-constructs `𝔅` if `𝔅` is homomorphically
  equivalent to a pp-power of `𝔄`. Transitive (Brady L2244).
* **Reduction theorem** (Brady Prop L2222): if `𝔅` is homomorphically equivalent to a
  pp-power of `𝔄`, there is a reduction `CSP(𝔅) → CSP(𝔄)` computable in **linear time and
  logarithmic space**.
* **ERP theorem** (Barto–Opršal–Pinsker; Brady Thm L2280): `Pol(𝔅)` contains a reflection
  of `Pol(𝔄)^n` iff there is a height-1 clone homomorphism `Pol(𝔄) → Pol(𝔅)`; combined
  with Brady Prop L2271 this says pp-constructability = existence of a minion homomorphism.
* 2104.11808 Theorem 1.1 states the dichotomy as: *if every finite structure is
  homomorphically equivalent to a finite structure pp-interpretable in `𝔄`, then CSP(𝔄) is
  NP-hard; otherwise it is in P.*

**Assessment.** For a Lean formalization of the hard half, pp-interpretability is
**overhead you do not need**. Zhuk's route produces a *pp-definition on the nose* (of a
WNU-blocker over `Γ' = f(Γ) ∪ constants`), plus two bespoke instance-level reductions
(`Γ ↔ f(Γ)`, `Γ' → f(Γ)`). Building the pp-power/reflection machinery would triple the
work for no gain. Record pp-interpretability in the blueprint as *context*, not as an
API.

### 2.6 The algebraic reduction of Bulatov–Jeavons–Krokhin

The BJK package, as it is actually used, is four separate statements. Brady states them
individually; the classical citation for all four is [BJK 2005].

* **(BJK-1) Relational-clone invariance.** `Γ' ⊆ ⟨Γ⟩` finite ⟹ `CSP(Γ') ≤_log CSP(Γ)`.
  Proof: replace each `Γ'`-atom by its pp-definition, existential variables become fresh
  instance variables. (Brady L194–204; Zhuk uses this implicitly in Theorem 5.5.)
* **(BJK-2) HSP reduction.** Brady Thm L1891: if `𝐁` is a subalgebra, a power, or a
  quotient of `𝐀`, then `CSP(𝐁) ≤_log CSP(𝐀)`. Proof at L1901–1905: subalgebra = add a
  unary constraint; power = split each variable into an `n`-tuple; quotient = lift each
  relation along `/σ`.
* **(BJK-3) Homomorphic equivalence / cores.** `𝔄 ≡_hom 𝔅` ⟹ `CSP(𝔄) = CSP(𝔅)` as sets of
  yes-instances (Brady L192). Every finite `𝔄` has a core, unique up to isomorphism
  (Brady Prop L2072).
* **(BJK-4) Rigidification.** For `𝔄` a core, `CSP(𝔄^{rig}) ≡_log CSP(𝔄)`, where `𝔄^{rig}`
  adjoins all singleton unary relations (Brady Thm L2101; Zhuk Theorem 5.4). On the
  algebraic side this is the passage to idempotent algebras (Brady Prop L2129).

Zhuk's §5.2 is exactly (BJK-3) + (BJK-4), reproved.

### 2.7 WNU, Taylor, cyclic — and which implications are cheap

* **Taylor term** (Brady Defn L2340): an idempotent term `t` of arity `n` satisfying, for
  each `i ≤ n`, an identity `t(…x at position i…) ≈ t(…y at position i…)` with the other
  entries filled arbitrarily by `x`s and `y`s.
* **WNU ⟹ Taylor is trivial** and does not need Maróti–McKenzie. Given an idempotent WNU
  `w` of arity `n ≥ 2`, for coordinate `i ≠ 1` use the identity
  `w(y,x,…,x) ≈ w(x,…,x,y at i,x,…,x)` (left has `x` at `i`, right has `y` at `i`);
  for `i = 1` use `w(x,y,x,…,x) ≈ w(y,x,…,x)`. Both are instances of the WNU equations.
  So `w` *is literally* a Taylor term.
* **Taylor ⟹ WNU is Maróti–McKenzie** (2008), the hard direction. Equivalently
  Barto–Kozik's cyclic term theorem. This is precisely what Zhuk's §4 re-proves via strong
  subalgebras (his Theorem 4.14 (3) ⟹ (2)).
* Consequence for the chain: **the hypothesis "no WNU" cannot be converted to "no Taylor"
  cheaply.** Any route from "no WNU" to hardness must contain either Maróti–McKenzie,
  or Barto–Kozik's cyclic term theorem, or Zhuk's §4. There is no shortcut. (Route
  comparison in §3.11.)

---

## 3. The chain, link by link

Notation of Theorem 5.5's proof: `f` a unary polymorphism of Γ of minimal range,
`B = f(A)`, `Γ' = f(Γ) ∪ {x = a | a ∈ B}`, `𝐁 = (B; Pol(Γ'))`.

```
      Γ has no WNU polymorphism
              │  (D)
              ▼
      Γ' has no WNU polymorphism ;  𝐁 = (B;Pol(Γ')) is idempotent
              │  (E)  Zhuk Thm 4.14 ⟸ Lem 4.5 ⟸ Lem 4.4 ⟸ Thm 3.3, Thm 3.5, Lem 3.4
              ▼
      ∃ WNU-blocker R = (B₀∪B₁)³ \ (B₀³∪B₁³) ∈ Inv(𝐁)
              │  (F)  Galois: Inv(Pol(Γ')) = ⟨Γ'⟩
              ▼
      R is pp-definable over Γ'
              │  (G)  gadget: NAE₃ ↦ R ↦ pp-definition
              ▼
      CSP(NAE₃) ≤ CSP(Γ')  ≤ CSP(f(Γ))     (C) Thm 5.4 + Lem 5.3, uses core-ness
                            ≡ CSP(Γ)       (A) Lem 5.2, (B) f(Γ) is a core
              │  (H) Schaefer: CSP(NAE₃) is NP-hard
              ▼
      CSP(Γ) is NP-hard ;  and (I) CSP(Γ) ∈ NP
```

### 3.1 Link A — relation renaming under a unary polymorphism

> **Lemma 5.2** [17]. Suppose `f` is a unary polymorphism of Γ. Then CSP(Γ) is
> polynomially equivalent to CSP(f(Γ)).

with `f(Γ) = {f(R) | R ∈ Γ}` a language on the domain `f(A)`, and `f(R) = {(f(a₁),…,f(a_m)) | a ∈ R}`.

**Reconstructed proof** (Zhuk gives one sentence, L778–780): the instance map is
"replace each `R_i` by `f(R_i)`, keep variables and scopes". Then
`I` satisfiable ⟹ compose a solution with `f` to get a solution of `f(I)`; conversely a
solution of `f(I)` takes values in `f(A)` and satisfies each `f(R) ⊆ R` (because `f`
preserves `R`), hence is a solution of `I`. Both directions one line. Constant-size
instance map, no blow-up at all.

*Formalization note.* This is trivial in Lean once instances are indexed by a signature:
the map is the identity on the constraint list, only the interpretation changes.

### 3.2 Link B — `f(Γ)` is a core

> A constraint language is called a core if every unary polymorphism of Γ is a bijection.
> It is not hard to show that if `f` is a unary polymorphism of Γ with minimal range, then
> `f(Γ)` is a core [9].  (Zhuk L785–787)

**"It is not hard to show" — reconstructed.** Let `g` be a unary polymorphism of `f(Γ)`,
`g : f(A) → f(A)`. Then `g ∘ f : A → A` is a unary polymorphism of Γ: for `R ∈ Γ`,
`(g∘f)(R) = g(f(R)) ⊆ f(R) ⊆ R` since `g` preserves `f(R) ∈ f(Γ)` and `f` preserves `R`.
Its range is contained in `f(A)`; by minimality of `|range f|`, `|range(g∘f)| = |f(A)|`,
so `g` is surjective on the finite set `f(A)`, hence bijective. ∎

**Gap 3.2.** "minimal range" needs `A` finite and `Pol₁(Γ) ∋ id` nonempty — both fine.
`f(Γ)` really is a language on `f(A)`; a formalization must handle the domain change
(dependent types!). See §6.3 for the recommended workaround (keep the domain `A` and carry
a `Set A` of admissible values).

### 3.3 Link C — adding constants to a core

> **Lemma 5.3.** Suppose `A = {0,1,…,k−1}`, `Γ ⊆ R_A` and `𝐀 = (A; Pol(Γ))`. Then
> `Sg_{𝐀^k}({(0,1,…,k−1)})` has a quantifier-free pp-definition over Γ.

Proof (Zhuk L792–799): `σ(z₀,…,z_{k−1}) := ⋀_{R ∈ Γ, (a₁,…,a_s) ∈ R} R(z_{a₁},…,z_{a_s})`.
Then `(0,…,k−1) ∈ σ`, and `(b₀,…,b_{k−1}) ∈ σ` says exactly that `g(x) = b_x` preserves
every `R ∈ Γ`.

*Missing step:* to conclude `σ = Sg(…)` one needs both inclusions. `Sg ⊆ σ` because `σ` is
quantifier-free-pp over Γ hence in `Inv(Pol(Γ)) = Inv(𝐀)`, i.e. a subuniverse of `𝐀^k`
containing the generator. `σ ⊆ Sg` because each `(b₀,…,b_{k−1}) ∈ σ` gives
`g ∈ Pol₁(Γ)` = a *basic operation of 𝐀*, and `(b₀,…,b_{k−1}) = g(0,1,…,k−1)`. The second
inclusion silently uses that `𝐀`'s basic operations are *all* of `Pol(Γ)` — a convention
introduced at L790 and never restated. Flag it.

> **Theorem 5.4** [9]. Let `Γ ⊆ R_A` be a core constraint language, and
> `Γ' = Γ ∪ {x = a | a ∈ A}`. Then CSP(Γ') is polynomially reducible to CSP(Γ).

Proof (Zhuk L803–818): given an instance `I'` of CSP(Γ'), introduce `k` fresh variables
`z₀,…,z_{k−1}`, replace each constraint `x = a` by `x = z_a` (i.e. substitute `z_a` for
`x`), and add the constraints of `σ(z₀,…,z_{k−1})`. Forward: set `z_a := a`. Backward: a
solution assigns `(z₀,…,z_{k−1}) = (b₀,…,b_{k−1}) ∈ σ`, so `φ(x) = b_x` is a unary
polymorphism, bijective since Γ is a core; "composing φ we can define a unary bijective
polymorphism ψ such that `ψ(b₀,…,b_{k−1}) = (0,…,k−1)`"; apply `ψ` to the solution.

**Gap 3.3a ("composing φ").** The unstated argument: `φ` is a bijection of the finite set
`A`, so it has finite order `d` in `Sym(A)`, and `ψ := φ^{d−1} = φ^{-1}` is a composition
of polymorphisms, hence a polymorphism. Formalizable, ~20 lines, but it *is* an omitted
step.

**Gap 3.3b (equality constraints).** "replace every constraint `x = a` by `x = z_a`"
produces equality atoms, which are not in Γ. What is meant is *substitution*: replace
every occurrence of the variable `x` by `z_a` throughout the instance. If `x` is
constrained to two different constants the instance is unsatisfiable and one must handle
that. A Lean formalization needs a variable-substitution operation on instances (or a
union-find). Small but real.

### 3.4 Link D — "no WNU" passes from Γ to Γ'

> If Γ' has a WNU polymorphism `w'`, then `w(x₁,…,x_m) = w'(f(x₁),…,f(x_m))` is a WNU
> polymorphism of Γ.  (Zhuk L832–834)

Check: for `R ∈ Γ` and `α₁,…,α_m ∈ R`, `f(α_i) ∈ f(R) ∈ f(Γ) ⊆ Γ'`, so
`w'(f(α₁),…,f(α_m)) ∈ f(R) ⊆ R`. And the WNU equations for `w` follow from those for `w'`.
This is where Convention 1.1 bites: `w(x,…,x) = f(x)`, so `w` is not idempotent.

### 3.5 Link E — the algebraic heart

`Γ'` contains all constant relations, so every `f ∈ Pol(Γ')` is idempotent; hence
`𝐁 = (B; Pol(Γ'))` is a **finite idempotent algebra**, and `Clo(𝐁) = Pol(Γ')` (already a
clone). "Γ' has no WNU polymorphism" = "𝐁 has no WNU term operation".

> **Theorem 4.14.** For every finite idempotent algebra `𝐀` TFAE:
> (1) there exists a WNU term operation;
> (2) there exists a WNU term operation of each prime arity `p > |A|`;
> (3) there does not exist an essentially unary algebra `𝐁 ∈ HS(𝐀)` of size at least 2;
> (4) there does not exist a WNU-blocker `R ∈ Inv(𝐀)`.

Cycle used: (1)⇒(4) Lemma 4.8; (4)⇒(3) Lemma 4.10; (3)⇒(2) Lemma 4.5 + primality;
(2)⇒(1) trivial. **For hardness only `¬(1) ⟹ ¬(4)` is needed**, i.e. only the arc
(4)⇒(3)⇒(2)⇒(1); **Lemma 4.8 is not needed**, and neither are Lemmas 4.9, 4.11, 4.12 nor
the entire p-WNU-blocker apparatus. Recording this is worth real formalization time.

**Definitions (Zhuk §4.3 L586–595).**

* A **WNU-blocker** is a relation `R = (B₀ ∪ B₁)³ \ (B₀³ ∪ B₁³)` with `B₀, B₁ ⊆ A`
  nonempty and disjoint. (Equivalently: the preimage of `NAE₃` under the map
  `B₀ ∪ B₁ → {0,1}`.)
* A **p-WNU-blocker** (`S ⊆ A`, `s ≥ 1`, `p` prime, `φ : S ↠ ℤ_p^s`):
  `R = {(a₁,a₂,a₃,a₄) ∈ S⁴ | φ(a₁) + φ(a₂) = φ(a₃) + φ(a₄)}`.
  **The addition is in `ℤ_p^s`, not in ℤ.** (I initially mis-read this and derived a
  contradiction in Lemma 4.12; with mod-`p` arithmetic Lemma 4.12 checks out exactly —
  see §4.10. Typo in the source: the tuple is written `{(a₁,a₂,a₃,a₄}` with a brace.)

**Statements the hardness arc actually needs**, in dependency order:

* **Lemma 3.2** [Barto–Kazda]: `B` absorbs `𝐀` with an `n`-ary term iff there is no
  `B`-essential `R ≤ 𝐀^n`. *(Already formalized in `zhuk-lean/ZhukLean/Relational.lean`
  as `exists_witnesses_of_not_hasEssential`.)*
* **Theorem 3.3**: every finite idempotent `𝐀` with `|A| ≥ 2` has (1) a nontrivial binary
  absorbing subuniverse, or (2) a nontrivial central subuniverse, or (3) a nontrivial PC
  subuniverse, or (4) a congruence `σ` with `𝐀/σ` p-affine, or (5) a nontrivial projective
  subuniverse.
* **Theorem 3.5**: `R ≤_sd 𝐀₁×⋯×𝐀_n`, `n ≥ 2`, `B_i ≤_T 𝐀_i`. Then (1)
  `R ∩ (B₁×⋯×B_n) ≤_T R`; (2) *if `T ≠ PC` or `𝐀₁` has no nontrivial central subuniverse*
  then `pr₁(R ∩ (B₁×⋯×B_n)) ≤_T 𝐀₁`; (3) if `R` is `(B₁,…,B_n)`-essential then
  `T ∈ {C,PC}` and `n = 2`.
* **Lemma 3.4**: a nontrivial projective subuniverse that is not binary absorbing forces an
  essentially unary `𝐔 ∈ HS(𝐀)` of size ≥ 2.
* **Lemma 4.2 / Cor 4.2.1**: `𝐁 ∈ HSP(𝐀)`, `|B| > 1` ⟹ `∃ 𝐁' ≤ 𝐁`, `|B'| > 1`,
  `𝐁' ∈ HS(𝐀)`; essential unarity is inherited.
* **Lemma 4.3 / Cor 4.3.1**: p-affine passes to subalgebras of size > 1, hence
  `HSP → HS`.
* **Lemma 4.4**: `𝐀` finite idempotent, `n ≥ 3`, `∅ ≠ R ≤ 𝐀^n` symmetric ⟹ (1) `R` has a
  constant tuple, or (2) essentially unary `𝐁 ∈ HS(𝐀)`, `|B| > 1`, or (3) p-affine
  `𝐁 ∈ HS(𝐀)` with `p | n`.
* **Lemma 4.5**: `𝐀` finite idempotent with no `n`-ary WNU term (`n ≥ 3`) ⟹ (1) or (2) as
  above (essentially unary in `HS(𝐀)`, or p-affine in `HS(𝐀)` with `p | n`).
* **Lemma 4.10**: essentially unary `𝐁 ∈ HS(𝐀)` of size ≥ 2 ⟹ a WNU-blocker in `Inv(𝐀)`.

**Theorem 4.14 (3)⇒(2) in detail** (Zhuk L705–711): if there is a prime `p > |A|` with no
`p`-ary WNU, Lemma 4.5 gives an essentially unary `𝐁 ∈ HS(𝐀)` (⇒ ¬(3)) or a `p'`-affine
`𝐁 ∈ HS(𝐀)` with `p' | p`, so `p' = p`; but then `p = p'ˢ ≤ |B| ≤ |A| < p`, contradiction.
*(This is where the p-affine branch dies, and why the hardness half needs no
p-WNU-blockers.)*

**Verified proof sketches** (I checked these line by line; details and gaps in §4):

*Lemma 4.4* — induction on `|A|`; "empty-property": WLOG `R ∩ B^n = ∅` for every proper
nonempty subuniverse `B`. Symmetry ⟹ all projections equal ⟹ `pr₁(R) = A`. Then five
cases of Theorem 3.3. Cases (1)–(3): `B ≤_T A` nontrivial, `C = pr₂(R ∩ (B×A^{n−1}))`;
if `C ≠ A` then `C ≤_T A` by 3.5(2), `R` is `C`-essential, contradicting 3.5(3) since
`n ≥ 3`; if `C = A` take minimal `k` with `pr_{[k]}(R) ∩ B^k = ∅`, show `k > 2` and that
`pr_{[k]}(R)` is `B`-essential, again contradicting 3.5(3). Case (4): `p ∤ n`; pick `k`
with `p | (kn − 1)`, set
`t(x₁,…,x_{kn}) = m(…m(m(m(x₁,x₁,x₂),x₁,x₃),x₁,x₄),…,x_{kn})` where `m/σ = x ⊖ y ⊕ z`;
then `t/σ = x₁ ⊕ ⋯ ⊕ x_{kn}` *(verified: the `j`-th partial is `x₂+⋯+x_{j+1} − (j−1)x₁`,
so the last is `Σ − (kn−1)x₁ = Σ`)*; applying `t` to `k` copies of the `n` cyclic shifts
of a tuple of `R` lands in `B^n ∩ R` for `B` the σ-class of `k·(a₁/σ ⊕ ⋯ ⊕ a_n/σ)`,
contradicting the empty-property. Case (5): Lemma 3.4.

*Lemma 4.5* — take `D = 𝐀^{|A|²}`, `M` the `|A|²×2` matrix listing all pairs, `α, β` its
columns, `R₀ ⊆ D^n` the `n` tuples with exactly one `β`, `R = Sg_D(R₀)`. `R` is symmetric.
Apply Lemma 4.4 to `(D, R)`. A constant tuple `(γ,…,γ) ∈ R` means `(γ,…,γ) = t(ρ₁,…,ρ_n)`
for an `n`-ary term `t`; reading off coordinates (which enumerate all pairs `(x,y)`) shows
`t` is an `n`-ary WNU on `A`. The other two cases transfer from `HS(D) ⊆ HSP(𝐀)` to
`HS(𝐀)` by Cor 4.2.1 / 4.3.1.

*Lemma 4.10* — `𝐁 ≅ S/σ`, `S ≤ 𝐀`; take two σ-classes `B₀ ≠ B₁`; then
`(B₀∪B₁)³ \ (B₀³∪B₁³) ∈ Inv(𝐀)`. **Zhuk gives no proof.** Reconstruction: since `𝐀` is
idempotent, so is `𝐁`; an idempotent essentially unary operation is a projection
(`g(x₁,…,x_n) = h(x_i)` and `h(x) = g(x,…,x) = x`). So *every* basic operation of `𝐁` is a
projection. Now let `g` be a basic operation of `𝐀` of arity `n` and `α₁,…,α_n ∈ R`. Each
`α_i ∈ (B₀∪B₁)³ ⊆ S³`, so `g(α₁,…,α_n) ∈ S³`; modulo σ it equals `α_i` for the `i` with
`g/σ = π_i`, whose σ-classes lie in `{B₀,B₁}` and are not all equal. Hence
`g(α₁,…,α_n) ∈ R`. ∎ *(≈ 40 Lean lines, but it is an omitted proof in the source.)*

### 3.6 Link F — Galois gives a pp-definition

`Inv(𝐁) = Inv(Pol(Γ')) = ⟨Γ'⟩`, so the WNU-blocker `R` is pp-definable over `Γ'`.
Zhuk adds parenthetically:

> (we also need the equality and empty relations but they can always be propagated out
> from the pp-definition of `R`)

**Gap 3.6.** This is the one genuine hand-wave in Theorem 5.5. Rigorous version:
(i) an *empty*-relation atom would force `R = ∅`, but `R ∋ (b₀,b₀,b₁)`, so no such atom
occurs; (ii) an equality atom between two distinct *free* variables would force a
coordinate identity on `R`, which fails; (iii) equality atoms involving an existential
variable are eliminated by substitution; (iv) atoms `x = x` are dropped.
**Better: use Observation 2.4** and produce an equality-free pp-definition directly from
Brady's explicit construction — then (i)–(iv) are unnecessary. Recommended.

### 3.7 Link G — the gadget reduction

> Let `NAE₃` be the ternary relation on `{0,1}` containing all tuples except `(0,0,0)`
> and `(1,1,1)`. Consider an instance `I` of `CSP({NAE₃})`, which is known to be an
> NP-hard problem [27]. Replace each `NAE₃`-relation by `R`, then replace each `R` by its
> pp-definition over `Γ'` (all existentially quantified variables are the new variables of
> the instance). The obtained instance is equivalent to `I`.  (Zhuk L838–844)

**Correctness (Zhuk gives none; here in full).** Fix `b₀ ∈ B₀`, `b₁ ∈ B₁` and
`φ : B₀ ∪ B₁ → {0,1}` with `φ(B₀) = 0`, `φ(B₁) = 1`.
* (⇒) If `s : V → {0,1}` solves `I`, then `s'(v) := b_{s(v)}` takes values in `B₀ ∪ B₁`,
  and for a constraint `NAE₃(u,v,w)` the triple `(s'u,s'v,s'w)` lies in `(B₀∪B₁)³` and is
  not inside `B₀³` (some coordinate has `s = 1`) nor `B₁³`; so it is in `R`.
* (⇐) If `s'` solves the `R`-instance, then all its values lie in `B₀ ∪ B₁` (since
  `R ⊆ (B₀∪B₁)³`) and `s := φ ∘ s'` solves `I` (a triple in `R` is not all-`B₀`, not
  all-`B₁`).
Then unfolding pp-definitions preserves satisfiability by (BJK-1).

**Size.** Each `NAE₃` constraint is replaced by one copy of a *fixed* gadget of
`c = |A|^{|R|}` variables and `≤ c'` constraints, where `c, c'` depend only on `Γ`.
So the map is a **local, constant-fan-out rewriting**: `|I'| ≤ c'·|I| + O(1)` and it is
computable by a single pass. This is why "polynomial time" is not in doubt and why the
computation-theoretic layer is pure bookkeeping.

### 3.8 Link H — the seed

`CSP({NAE₃})` is positive NAE-3SAT = 2-colourability of 3-uniform hypergraphs;
NP-complete by Schaefer 1978 [27]. Brady proves the whole chain from scratch:
generic NP problem (L779, NP-complete under logspace reductions L829) → Circuit-SAT
(L962–967) → 3-SAT (Thm L977) → 1-IN-3 SAT (Thm L1008) → NAE-SAT (Thm L1035) →
`k`-coloring (Thm L1061). The NAE step (L1037–1054) is a pp-definition of 1-IN-3 from NAE
plus one auxiliary variable `w` forced to differ from `z` by `(z,z,w) ∈ NAE`, exploiting
the `0↔1` symmetry.

### 3.9 Link I — membership in NP

Not stated anywhere in Zhuk (he says "NP-hard" in Thm 5.5 and "NP-complete" in Thm 5.1).
Trivial: guess `s : V → A` (size `|V|·log|A|`), check each constraint in time
`O(|constraints| · maxarity)`.

### 3.10 Route comparison

**Route Z (Zhuk 2005.00593 §§3,4,5,6).** As above. Self-contained modulo Schaefer.
Cost centre: Theorem 3.3, whose proof (§6.8, L2181–2255) runs through Lemmas 6.32, 6.33
and depends on Lemmas 6.16, 6.17, 6.26, 6.29, 6.30, 6.31, Theorem 6.15, Corollaries 6.1.1,
6.9.1, Lemma 6.14 — i.e. essentially all of §6 (≈ 20 printed pages, 33 numbered
statements), a re-derivation of the idempotent part of Rosenberg's maximal-clone
classification (full-projective / uniquely-determined / central relations, linear
algebras, Maltsev ⟹ p-affine). Note Zhuk's *intro* attributes the idea to Rosenberg
[26] but §6 does **not** import Rosenberg's theorem; it is proved from scratch.

**Route B (classical, Brady's presentation).**
`no WNU` ⟹ (Maróti–McKenzie, external) `no Taylor term` ⟹ (Taylor's theorem, Brady
L2349 + Birkhoff L1926 + König compactness L1954) a 2-element algebra with only
projections in `HSP(𝐀)` ⟹ (strictly-simple lemma, Brady L2406, itself *"following Zhuk"*)
in `HS(𝐀)` ⟹ (Cor L2426) the same NAE-shaped relation ⟹ same gadget.
Cost: the last three steps are cheap (≈ 2 pages), but the first step is
Maróti–McKenzie or Barto–Kozik's cyclic term theorem — the latter needs absorption theory
and the loop lemma (Brady chapter "Absorption and Bounded Width", thousands of lines).
**Neither route is cheap; Route Z at least keeps everything inside one paper and reuses
the strong-subalgebra machinery the tractability half needs anyway.**

**Route H (honest hybrid, recommended).** Formalize Links A–D, F–G in full (they are
small), and make Link E an explicit *interface*: a `Prop` (`HasWNUBlockerInInv`) with the
consumer theorem proved from it, and Zhuk §4 developed separately against the strong
subalgebra API that the tractability half is building anyway. This lets the hardness half
be *finished* long before Theorem 3.3 is.

---

## 4. Gaps, hand-waves, implicit conventions — consolidated list

Numbered for reference; severity: **H** = will break a formalization, **M** = costs a day,
**L** = cosmetic.

1. **[H] WNU is non-idempotent in the definition, idempotent in every use.** §1,
   Convention 1.1. Both readings appear within four pages.
2. **[H] The WNU definition has no arity bound**, making it vacuously satisfiable at
   arity 1. Must be repaired to `n ≥ 2`. §1, Convention 1.2.
3. **[H] Theorem 3.3's five cases are not exclusive, but Lemma 4.4's proof needs them
   ordered.** Lemma 4.4 Case A applies Theorem 3.5(2), whose side condition is
   "`T ≠ PC` or `𝐀₁` has no nontrivial central subuniverse". Zhuk applies it with no
   comment. The repair: read Theorem 3.3 as *"the first applicable case"*, in the order
   BA, central, PC; then in case (3) `𝐀` provably has no nontrivial central subuniverse.
   A blueprint must state Theorem 3.3 in this prioritized form or add the side hypothesis
   to case (3).
4. **[M] Lemma 4.10 has no proof.** "Then the relation `(B₀∪B₁)³ \ (B₀³∪B₁³)` is an
   invariant of `𝐀`." The argument (§3.5) needs idempotency to turn "essentially unary"
   into "all operations are projections". Without idempotency the statement is false.
5. **[M] Lemma 5.3's `σ = Sg(...)` needs both inclusions**, and the `⊆` direction uses the
   convention `𝐀 = (A; Pol(Γ))`, i.e. that *all* polymorphisms are basic operations.
6. **[M] Theorem 5.4's "composing φ we can define ψ"** = `φ⁻¹ = φ^{ord(φ)−1}`. Unstated.
7. **[M] Theorem 5.5's "equality and empty relations… can always be propagated out".**
   The only real hand-wave in the hardness proof. See §3.6; avoidable via Observation 2.4.
8. **[M] Theorem 5.5 never proves the gadget is correct.** "The obtained instance is
   equivalent to `I`" — the two-direction argument in §3.7 is omitted entirely.
9. **[M] "It is not hard to show that if `f` is a unary polymorphism with minimal range
   then `f(Γ)` is a core [9]"** — proof omitted; reconstructed in §3.2.
10. **[L, but I got it wrong first] p-WNU-blocker arithmetic is mod `p`.** In Lemma 4.12
    the claimed identity `R' = {φ(a₁)+φ(a₂) = φ(a₃)+φ(a₄)}` is *false over ℤ* and *true
    over ℤ₂*. I verified Lemma 4.12 completely: `R''` excludes exactly the patterns
    `(a,a,a,ā)`, the four conjuncts exclude the eight odd-parity patterns, and those are
    exactly the complement of `{φa₁+φa₂ ≡ φa₃+φa₄ (mod 2)}`. Also: the derivation of `R''`
    uses that `B₀` and `B₁` are both nonempty (to choose `y` of either parity) — unstated.
11. **[L] Typos.** `pr₁(A) = ⋯ = pr_n(A)` in Lemma 4.4 should be `pr₁(R) = ⋯ = pr_n(R)`;
    `{(a₁,a₂,a₃,a₄}` (brace) in §4.3 and Lemma 4.11; `f(x₁,…,x_n) = h(x₁)+…+h(x_n)` in
    Lemma 4.1 should be `w`; "case (5): there exists a nontrivial CBT subuniverse" in
    Lemma 4.4 should read "projective" (CBT is never defined in the paper).
12. **[M] `HSP` with infinite powers.** Lemma 4.2 is stated for `𝐁 ∈ HSP(𝐀)` and proved by
    induction on `n` with `S ≤ 𝐀^n`, i.e. for finite powers only. Every *use* is with a
    finite power (`D = 𝐀^{|A|²}`), so define `HSP` with finite powers and note the
    restriction. (Brady, L2406, is explicit that for finite algebras
    `HSP_fin = HSP ∩ finite`.)
13. **[M] Domain changes.** `f(Γ)` lives on `f(A)`, `𝐁` on `B = f(A)`, quotients live on
    `S/σ`. In prose this is free; in Lean each is a different type. §6.3.
14. **[L] "polynomially equivalent" / "polynomially reducible" are never defined** in
    2005.00593. Neither is "NP-hard". The paper simply does not have a complexity-theoretic
    layer; it has instance transformations of evidently linear size.
15. **[H] `CSP(Γ)` is defined for *finite* Γ only in the informal sense.** §4 works with
    `Inv(𝐀)`, an infinite language. The Galois step (Link F) produces a *single* relation
    `R ∈ ⟨Γ'⟩`, which is fine, but a blueprint must be explicit that Γ, Γ' are finite and
    that `𝐁`'s signature is `Pol(Γ')` (infinite) while `Inv(𝐁)` relations get used
    one at a time.

---

## 5. What a Lean formalization needs

### 5.1 Algebraic layer (no computation)

Already partly present in `zhuk-lean`, which models algebras as `FirstOrder.Language`
structures (`L.Structure M`, `L.Term (Fin m)`, `L.Substructure`). What is missing:

* **Relations and languages with relation symbols.** `zhuk-lean` uses algebraic languages
  only (`L.IsAlgebraic`). The hardness half needs relations as first-class objects. Do
  *not* try to make `Pol`/`Inv` interact with `FirstOrder.Language` relation symbols;
  define relations concretely as `Set (Fin n → A)`.
* `Pol`, `Inv`, `Clo`, `RelClo`, subuniverse-of-a-power, `Sg`.
* **The Galois theorem `Inv (Pol Γ) = ⟨Γ⟩`** — Brady's constructive proof (§2.4). This is
  the single most valuable reusable piece; ≈ 300–500 Lean lines. Nothing like it exists in
  Mathlib.
* Congruences, quotients, `HS`, `HSP_fin`. `zhuk-lean/survey/09-mathlib-probe.lean`
  already shows the congruence/quotient pattern (`Cong` + `L.Prestructure` +
  `quotientStructure`) works for algebraic languages.
* Essentially unary algebras; the fact that idempotent + essentially unary ⟹ all
  operations are projections.
* WNU-blockers, and Lemma 4.10.
* All of §4: Lemmas 4.2, 4.3, 4.4, 4.5, Theorem 4.14 — on top of Theorem 3.3 / 3.5 / 3.4
  from the strong-subalgebra development.

### 5.2 Syntactic / reduction layer (no computation model)

* `Instance Γ`, `Instance.Satisfiable`, variable substitution, disjoint-union of
  instances, gadget substitution.
* pp-definition = instance with distinguished free variables; `ppDefines`.
* Instance-level reduction with a size bound:

```lean
structure GadgetReduction {A₁ A₂ : Type} (Γ₁ : Lang A₁) (Γ₂ : Lang A₂) where
  toFun    : Instance Γ₁ → Instance Γ₂
  sat_iff  : ∀ I, (toFun I).Satisfiable ↔ I.Satisfiable
  c        : ℕ
  size_le  : ∀ I, (toFun I).size ≤ c * I.size + c
```

Composition of `GadgetReduction`s is immediate (constants multiply). This structure is
the honest carrier of "there is a linear-time, log-space many-one reduction" *without*
committing to a machine model — and it is exactly what all four BJK reductions and the
Zhuk gadget produce.

### 5.3 Complexity layer: Mathlib audit

**Audited directory:** `zhuk-lean/.lake/packages/mathlib/Mathlib/Computability/` —
`Ackermann, AkraBazzi/, ContextFreeGrammar, DFA, Encoding, EpsilonNFA, Halting, Language,
MyhillNerode, NFA, Partrec, PartrecBasis, PartrecCode, PostTuringMachine, Primrec/,
RecursiveIn, RE, Reduce, RegularExpressions, StateTransition, Tape, TMComputable,
TMConfig, TMToPartrec, TuringDegree, TuringMachine/{Computable, Config,
PostTuringMachine, StackTuringMachine, Tape, ToPartrec}`.

What exists that is relevant:

| Item | Where | Verdict |
|---|---|---|
| `Computability.Encoding α Γ`, `FinEncoding` | `Computability/Encoding.lean` | usable as the input-encoding notion |
| `ManyOneReducible (≤₀)`, `OneOneReducible (≤₁)`, `ManyOneEquiv`, `ManyOneDegree` | `Computability/Reduce.lean` | **computable** many-one reductions, **no resource bounds**; refl/trans lemmas present |
| `Nat.Partrec`, `Partrec`, `Computable`, `ComputablePred`, `RePred` | `Partrec.lean`, `Halting.lean` | decidability, not complexity |
| `Turing.FinTM2`, `TM2Outputs`, `TM2OutputsInTime`, `TM2Computable`, `TM2ComputableInTime`, `TM2ComputableInPolyTime` (field `time : Polynomial ℕ`) | `TuringMachine/Computable.lean` (292 lines) | **the only polytime notion in Mathlib**, and it is a stub |
| `idComputableInPolyTime`, `idComputable` | ibid. | the *only two theorems* in that file — literally the identity function |
| `ValuedCSP`, `FractionalOperation`, `IsFractionalPolymorphismFor` | `Combinatorics/Optimization/ValuedCSP.lean` | VCSP vocabulary; **no `Pol`/`Inv`, no decision problem, no CSP(Γ)** |
| `FirstOrder.Language.BoundedFormula`, `IsAtomic`, `IsQF`, `IsPrenex` | `ModelTheory/Complexity.lean` | *formula* complexity, unrelated to computational complexity |

What does **not** exist anywhere in Mathlib (verified by grep over the whole library):

* the classes **P** and **NP** — no definition, no notation;
* **polynomial-time many-one reduction** as a relation between decision problems;
* **NP-hardness / NP-completeness**;
* **Cook–Levin**, Circuit-SAT, 3-SAT, NAE-SAT, `k`-coloring, or any concrete NP-complete
  problem;
* **logspace** computation or logspace transducers;
* **composition lemmas for `TM2ComputableInPolyTime`** (so you cannot even chain two
  polytime functions);
* **clones, relational clones, polymorphisms, Birkhoff's HSP theorem, varieties,
  congruences of general algebras**. (`grep -rl "HSP\|\bclone\b" Mathlib/` → empty.)

**Cost of building layer C honestly.** To say `NPComplete (CSP Γ)` in the standard sense
you need: a machine model with a time measure, closure of polytime under composition, the
definition of NP, and NP-hardness of a seed. The seed is Cook–Levin. For calibration, the
only mechanized Cook–Levin I am aware of is Balbach's Isabelle/AFP entry (2023), which is
on the order of tens of thousands of lines — *(recollection, not verified from disk)*. That
is comparable to the entire rest of this project. **Do not put it on the critical path.**

---

## 6. Proposed Lean formulation

### 6.1 The recommendation in one sentence

Prove the algebra and the gadget as theorems; expose the complexity claim as a
**parametrized corollary whose hypothesis is the seed hardness**, so that nothing is
axiomatized silently and nothing is `sorry`ed.

### 6.2 Three tiers

**Tier 1 — pure algebra (the real theorem).** No computation, no syntax:

```lean
/-- Zhuk 2005.00593, Theorem 4.14, hardness arc. -/
theorem exists_wnuBlocker_of_no_wnu
    {A : Type} [Fintype A] [DecidableEq A] (𝐀 : IdempotentAlgebra A)
    (h : ¬ ∃ n ≥ 2, ∃ w : (Fin n → A) → A, w ∈ 𝐀.Clo ∧ IsWNU w) :
    ∃ B₀ B₁ : Set A, B₀.Nonempty ∧ B₁.Nonempty ∧ Disjoint B₀ B₁ ∧
      wnuBlocker B₀ B₁ ∈ Inv 𝐀
```

**Tier 2 — the reduction, as an explicit satisfiability-preserving instance map.**

```lean
/-- Zhuk 2005.00593, Theorem 5.5, computational content. -/
theorem gadgetReduction_of_no_wnu
    {A : Type} [Fintype A] [DecidableEq A] (Γ : Lang A) [Fintype Γ.ι]
    (h : ¬ HasWNUPolymorphism Γ) :
    Nonempty (GadgetReduction NAE₃ Γ)
```

Read: *there is a map from NAE-3SAT instances to CSP(Γ) instances that preserves
satisfiability in both directions and blows up the size by at most a constant factor.*
This is a complete, unconditional, honest statement of everything the mathematics
establishes. It is also, in Lean, *automatically a computable function* — every
`GadgetReduction.toFun` you can write with `def` on `List`/`Fin`/`Finset` data is
executable — so the only thing missing relative to "polynomial-time many-one reduction" is
a formal cost model, and `size_le` already certifies the only nontrivial part of the cost
(linear output size).

**Tier 3 — complexity wrapper, seed-relative.** Define, in the project (not Mathlib):

```lean
/-- A decision problem is a predicate on a type with a `FinEncoding`. -/
structure DecisionProblem where
  Input : Type
  enc   : Computability.FinEncoding Input
  Yes   : Input → Prop

def PolyManyOneReducible (P Q : DecisionProblem) : Prop := …   -- explicit, project-local
def NPHard (Q : DecisionProblem) : Prop := ∀ P, InNP P → PolyManyOneReducible P Q

theorem csp_npHard_of_no_wnu
    (seed : NPHard NAE3SAT)                      -- Schaefer/Cook–Levin, NOT proved here
    (h : ¬ HasWNUPolymorphism Γ) : NPHard (CSP Γ)

theorem csp_inNP : InNP (CSP Γ)

theorem csp_npComplete_of_no_wnu (seed : NPHard NAE3SAT)
    (h : ¬ HasWNUPolymorphism Γ) : NPComplete (CSP Γ)
```

`seed` as an explicit hypothesis is the crux of the honesty: the file compiles with no
axioms beyond Mathlib's, the theorem is true as stated, and a reader sees at a glance
exactly what is imported. (An `axiom nae3sat_npHard : NPHard NAE3SAT` would be equivalent
logically but hides the import from `#print axioms`; the hypothesis form does not.)

### 6.3 Design decisions that will bite

* **Domain changes (Gap 13).** Do *not* let `f(Γ)` live on a new type. Carry a
  `D : Set A` of admissible values through the whole development and define
  `Pol`/`Inv`/instances relative to `D`. This turns "pass to the core" and "pass to a
  subalgebra" into set-shrinking rather than type-changing. The `zhuk-lean` `Center.lean`/
  `Absorbs.lean` files already work with `Set M` rather than subtypes for exactly this
  reason — keep that.
* **Quotients (`S/σ`)** cannot be avoided (`HS(𝐀)`), and there the type does change.
  `Mathlib.ModelTheory.Quotients` + a hand-rolled `Cong` structure works (already probed in
  `survey/09-mathlib-probe.lean`).
* **Arity bookkeeping.** `Fin n → A` everywhere, never `A × A × A`, even for the ternary
  WNU-blocker; the gadget code has to be uniform in arity.
* **Instances as `List`, not `Finset`.** Multiplicity is irrelevant to satisfiability but
  relevant to `size`; `List` gives a free `length`.
* **Decidability.** `Fintype A`, `DecidableEq A`, `DecidablePred (· ∈ R)` for every
  relation, so that `toFun` is genuinely executable and `Satisfiable` is decidable.
* **Do not build pp-interpretability/pp-powers/minions.** §2.5.
* **Do not attempt `TM2ComputableInPolyTime`.** With no composition lemma in Mathlib, any
  attempt costs more than the entire hardness half.

### 6.4 The alternative "purely algebraic" statement, and why it is weaker

One could stop at: *"Γ pp-constructs NAE-3SAT"*. Two problems.
(a) For non-core Γ the NAE-shape is pp-definable only over `f(Γ) ∪ constants`, so the
statement must be `Γ pp-constructs …` in the Barto–Opršal–Pinsker sense (pp-power **+
homomorphic equivalence**), which needs the pp-power machinery (§2.5) — more work than
Tier 2, not less.
(b) It hides the two bespoke reductions (Links A and C) that are the only non-pp steps.
**Tier 2's `GadgetReduction` is strictly better**: it is a single uniform notion that all
four reduction kinds (relation renaming, pp-unfolding, core rigidification, gadget
substitution) instantiate, it composes definitionally, and it directly feeds Tier 3.

---

## 7. Suggested module architecture (hardness half)

```
CSP/Core/Relation.lean        -- Set (Fin n → A), preserves, Pol, Inv, Sg, subpowers
CSP/Core/Clone.lean           -- clones, RelClo, generated clone
CSP/Core/Instance.lean        -- Instance Γ, Satisfiable, substitution, size, union
CSP/Core/PP.lean              -- pp-definability = instance with free variables
CSP/Core/Galois.lean          -- Inv (Pol Γ) = ⟨Γ⟩ (Brady's explicit construction) ★
CSP/Core/Reduction.lean       -- GadgetReduction, composition, from pp-definability
CSP/Hard/WNU.lean             -- IsWNU (n ≥ 2, non-idempotent), WNU ⟹ Taylor
CSP/Hard/Blocker.lean         -- WNU-blocker; blocker ⟹ GadgetReduction NAE₃ Γ' ★
CSP/Hard/Core.lean            -- minimal-range endomorphism, core, Lemma 5.2 ★
CSP/Hard/Constants.lean       -- Lemma 5.3 + Theorem 5.4 (rigidification) ★
CSP/Hard/EssentiallyUnary.lean-- ess. unary + idempotent ⟹ projections; Lemma 4.10 ★
CSP/Hard/HSP.lean             -- Lemma 4.2/4.3 + corollaries (HSP_fin → HS) ★
CSP/Hard/Symmetric.lean       -- Lemma 4.4 (constant tuple) — needs Thm 3.3/3.5/Lem 3.4
CSP/Hard/Maroti.lean          -- Lemma 4.5, Theorem 4.14
CSP/Hard/Main.lean            -- Theorem 5.5 as `Nonempty (GadgetReduction NAE₃ Γ)`
CSP/Complexity/Model.lean     -- project-local DecisionProblem, InNP, PolyManyOne, NPHard
CSP/Complexity/Wrapper.lean   -- seed-relative NP-completeness
```

★ = independent of the strong-subalgebra development; can be finished immediately and
gives a complete, `sorry`-free hardness theorem *conditional on* `Theorem 4.14`, which is
then the single interface to the heavy algebra. Rough sizing using the project's own
calibration (≈ 134 Lean lines per source statement, ≈ 200 per source page, from
`survey/12-prior-art-conventions.md`): the ★ modules + Galois ≈ 2.5–3.5k lines;
`Symmetric`+`Maroti` ≈ 1.5k on top of Theorem 3.3; Theorem 3.3 itself (§6 of 2005.00593,
33 statements, 20 pages) ≈ 4–6k lines; complexity wrapper ≈ 400 lines.

---

## 8. Risks

* **R1.** Theorem 3.3 is the whole ballgame. If the tractability half's blueprint takes its
  strong-subalgebra existence theorem in the *WNU-assumed* form (as 2404 does), it will
  **not** discharge Theorem 3.3, which is stated for arbitrary finite idempotent algebras.
  Check this early: 2404 assumes a WNU throughout; 2005.00593 Theorem 3.3 does not.
* **R2.** The prioritized-case convention (Gap 3) must be baked into the blueprint's
  statement of Theorem 3.3, or Lemma 4.4 will not go through.
* **R3.** The `Inv(Pol Γ) = ⟨Γ⟩` proof needs care about `∅` and about generation
  (Gap 2.3); budget a day for edge cases.
* **R4.** Domain-change plumbing (`f(Γ)`, `S/σ`) is the classic Lean tarpit. Decide the
  `Set A`-based convention up front and never deviate.
* **R5.** Nobody has formalized any NP-hardness in Lean/Mathlib. If the project's stated
  goal is "the CSP Dichotomy Theorem", the phrase "NP-complete" in the goal must be
  renegotiated to the seed-relative form *before* the blueprint is written, or the goal
  is unreachable.
* **R6.** Schaefer's NP-hardness of positive NAE-3SAT is itself a chain of four reductions
  (Brady L962–1054). Even *stating* it needs the Tier-3 vocabulary. Keep it as the single
  hypothesis; do not try to prove `CSP(NAE₃) ≤ CSP(Γ)` from 3-SAT instead — NAE₃ is the
  right seed because the blocker is literally an NAE-shape.
* **R7.** Convention 1.2 (arity ≥ 2 in the WNU definition) is a *correction to the
  published definition*. If a reviewer of the blueprint compares against the paper
  verbatim, this will look like an error; document it as a deliberate repair with the
  reason (arity-1 WNUs make the theorem false as stated).
