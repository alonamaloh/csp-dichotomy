# Repairs

Worked proofs for the three confirmed issues, ready to drop into the rendering. None of the
three needs new mathematics; the hardest, D4, needs a citation Zhuk's later paper dropped,
plus a short reduction to make it applicable in the later setting.

Notation follows the blueprint. `⋘` is the strong-reduction relation, `<_T^A` the typed
reduction, `ℳT` the multi-types.

---

## D2 — `CORPropagationModuloCongruence`

**Statement.** Let `δ` be a congruence on `A`. Then

- (f) `C ⋘^A B ⟹ C/δ ⋘^{A/δ} B/δ`
- (t) `C <_{T(σ)}^A B ⋘ A ⟹ (C/δ = B/δ` or `C/δ <_S B/δ` or `C/δ <_T^{A/δ} B/δ)`
- (s) for `T ∈ {BA, C, S}`, `C <_T B ⟹ C/δ ≤_T B/δ`
- (m) `C ≤_{ℳT}^A B ⋘ A` and `B/δ` is S-free `⟹ C/δ ≤_{ℳT}^{A/δ} B/δ`

**Proof.** Apply Propagation (`LEMPropagation`) to the canonical surjection
`π : A ↠ A/δ`, whose clauses (f), (ft), (fs), (fm) are the four above. The identification is
literal rather than approximate: `X/δ` is *defined* as the image `{x/δ : x ∈ X}`, which is
`π(X)`. ∎

**Note.** I had flagged in an earlier draft that clause (m) needed care, because
Propagation (fm) hypothesises "`f(B)` is S-free" while the corollary says "`B/δ` is S-free".
That dissolves: `f(B) = π(B) = B/δ`. They are the same condition, and the specialisation is
mechanical after all.

---

## D4 — `n = 2` for type `C` in the stable-intersection theorem

The theorem concludes, in case (c), that `n = 2` and `T₁ = T₂ = C`. The proof in
`StrongSubalgebras.tex:2594+` establishes that all types agree and then argues `n = 2` **only
for PC**, where equal congruences make the `Cᵢ` pairwise disjoint. Type `C` gets nothing.

The missing argument is Theorem 3.7 of Zhuk, *Strong subalgebras and the CSP*
(arXiv:2005.00593), which is the same statement for subuniverses of a *single* algebra:

> Assume that `T₁ = ⋯ = Tₙ = C`. Let `R` be the `n`-ary relation consisting of all the
> constant tuples. Then `R` is a `(B₁,…,Bₙ)`-essential relation, which contradicts
> Lemma 6.11.

with **Lemma 6.11**: *for `n ≥ 3` and `Cᵢ ≤_C Aᵢ`, no `(C₁,…,Cₙ)`-essential relation
`R ≤ A₁×⋯×Aₙ` exists.* Its proof pushes an essential relation down to arity 3, bootstraps to
`C₁`-essential relations of unbounded arity, and contradicts the Barto–Kazda criterion
(*`B` absorbs `A` with an `n`-ary term iff no `B`-essential relation of arity `n` exists*)
against the fact that a central subuniverse absorbs.

The 2404 setting is not literally that of Theorem 3.7 — there the `Bᵢ` are subuniverses of one
algebra `A`, whereas here `Cᵢ` is central in `Bᵢ` and the `Bᵢ` differ. So we need a reduction
first.

**Lemma (reduction to a common algebra).** Under hypotheses (1)–(3) of the stable-intersection
theorem with all `Tᵢ = C`, put `D = ⋂_{i∈[n]} Bᵢ` and `Eᵢ = Cᵢ ∩ D`. Then `D` is a nonempty
subuniverse, `Eᵢ ≤_C D` for each `i`, and

  `⋂_{i∈[n]} Eᵢ = ∅`,  `⋂_{i≠j} Eᵢ ≠ ∅` for every `j`.

*Proof.* `D` is an intersection of subuniverses, hence a subuniverse. It is nonempty: by (3)
at `j = 1`, `B₁ ∩ C₂ ∩ ⋯ ∩ Cₙ ≠ ∅`, and `Cᵢ ⊆ Bᵢ`, so this set is contained in `D`.

`Eᵢ ≤_C D`: `Cᵢ` is central in `Bᵢ` and `D` is a subalgebra of `Bᵢ`, so by
`LEMBACenterImplyIntersection` (*if `B ≤_T A` and `C ≤ A` with `T ∈ {BA, C}` then
`B ∩ C ≤_T C`*), `Cᵢ ∩ D ≤_C D`.

The first display is (2) intersected with `D`. For the second, since `Cᵢ ⊆ Bᵢ`,

  `⋂_{i≠j} Eᵢ = D ∩ ⋂_{i≠j} Cᵢ = B_j ∩ ⋂_{i≠j} Cᵢ`,

which is exactly hypothesis (3). ∎

Note each `Eᵢ` is a *proper* central subuniverse of `D`: if `Eⱼ = D` then
`⋂_i Eᵢ = ⋂_{i≠j} Eᵢ ≠ ∅`, contradicting (2).

**Proposition (the case (c) claim).** Under (1)–(3) with all `Tᵢ = C`, we have `n = 2`.

*Proof.* Suppose `n ≥ 3`. Reduce as above to `Eᵢ <_C D`. Let

  `R = {(a, a, …, a) : a ∈ D} ≤ Dⁿ`,

the diagonal, a subuniverse of `Dⁿ` by idempotence. Then `R` is `(E₁,…,Eₙ)`-essential:

- it misses the box `E₁×⋯×Eₙ`, since a constant tuple lies in that box exactly when its
  entry lies in `⋂ᵢ Eᵢ = ∅`;
- it meets each box `E₁×⋯×D×⋯×Eₙ` with the `j`-th coordinate freed, since such a constant
  tuple exists exactly when `⋂_{i≠j} Eᵢ ≠ ∅`.

Both are literally the two displays of the reduction lemma. By Lemma 6.11 no such relation
exists for `n ≥ 3`. ∎

**Formalization dividend.** Every ingredient of Lemma 6.11 is already formalized in
`zhuk-lean`: `IsEssential`, `not_isEssential_of_witnesses` (absorption forbids essential
relations), `exists_witnesses_of_not_hasEssential` (Barto–Kazda), and
`exists_ternary_witnesses` (central ⟹ ternary absorbing, which is Corollary 6.11.1). So the
repair for the most worrying of the three is the part of the project already done.

---

## D8 — minimal ℳT subuniverses

The main induction picks, for each variable, "the minimal `D⁽²⁾_x ≤_{ℳT} D⁽¹⁾_x` containing
`s(x)`", and then applies `LEMMinimalPCLinearReductionIsConsistent`, whose hypothesis (5)
requires `D⁽²⁾_x` to be *a minimal ℳT subuniverse* — minimal outright, not merely among those
containing `s(x)`. The lemma bridging the two was deleted from the source, along with its
citation. It is true, and here is a proof.

Fix `T ∈ {L, PC, D}` and `B` with `B ⋘ A`. Let `Σ` be the set of congruences on `A` that are
`T`-dividing for `B`; it is finite, `A` being finite. For `b ∈ B` put

  `M(b) = B ∩ ⋂_{σ ∈ Σ} [b]_σ`,

the intersection of `B` with the `σ`-block of `b`, over all `σ ∈ Σ`. Discard from the
intersection any `σ` with `B ∩ [b]_σ = B`, which contributes nothing.

**Lemma A.** `M(b)` is the least `ℳT` subuniverse of `B` containing `b`.

*Proof.* Each surviving `B ∩ [b]_σ` is `<_T^A B` by the definition of a `T`-dividing
congruence, and `M(b)` is a finite intersection of these containing `b`, hence nonempty, so
`M(b) ≤_{ℳT}^A B`. Conversely any `C ≤_{ℳT}^A B` with `b ∈ C` is an intersection
`⋂ⱼ (B ∩ E_j)` of blocks of congruences in `Σ`; each `E_j` contains `b`, so `E_j = [b]_{σ_j}`,
whence `M(b) ⊆ C`. ∎

**Lemma B.** If `c ∈ M(b)` then `M(c) = M(b)`.

*Proof.* `c ∈ M(b)` gives `c ∈ [b]_σ` for every `σ ∈ Σ`, hence `[c]_σ = [b]_σ` for every
`σ ∈ Σ`, and the two intersections coincide. ∎

**Proposition (the deleted lemma).** If `C` is an inclusion-minimal `ℳT` subuniverse of `B`
containing `b`, then there is no `C' ⊊ C` with `C' ≤_{ℳT}^A B`.

*Proof.* By Lemma A, `C = M(b)`. Let `C' ⊆ C` be `ℳT`; being `ℳT` it is nonempty, so pick
`c ∈ C'`. Then `c ∈ C = M(b)`, so `M(c) = M(b) = C` by Lemma B. But `C'` is an `ℳT` set
containing `c`, so `M(c) ⊆ C'` by Lemma A, giving `C = M(c) ⊆ C' ⊆ C`. Hence `C' = C`, and
no proper such `C'` exists. ∎

So minimal-containing-a-point and minimal-outright coincide, which is what the main induction
needs. The content is Lemma B: the map `b ↦ M(b)` is a closure whose image consists of
pairwise disjoint minimal sets, because membership in `M(b)` is decided blockwise and blocks
of an equivalence relation either coincide or are disjoint.

---

## D6 — `LEMBridgeFromRelation` applied without its third hypothesis

**The gap.** `LEMBridgeFromRelation` requires, besides subdirectness and rectangularity of the
first and last variables, that there exist `(b₁,ā,aₙ)` and `(a₁,ā,bₙ)` in `R` with
`(a₁,ā,aₙ) ∉ R`. The proof of `LEMConnectedProperties`(a) invokes it for every constraint
along a path and never discharges that hypothesis.

**It can fail.** Machine-checked witness, `R = {(x,z,y) ∈ ℤ₄ × ℤ₂ × ℤ₄ : x ≡ z ≡ y (mod 2)}`:
subdirect; `Con₁(R,1)` is congruence mod 2 and coordinate 1 is rectangular; and the third
hypothesis is unsatisfiable. The construction then yields
`δ(x₁,x₂,y₁,y₂) = ∃z. R(x₁,z,y₁) ∧ R(x₂,z,y₂)`, whose projection onto the first two
coordinates is *equal to* `Con₁(R,1)` rather than properly containing it — so `δ` is not a
bridge, condition (3) of the bridge definition failing. The lemma is genuinely inapplicable
and genuinely necessary.

**The repair: cruciality supplies the hypothesis.**

*Lemma.* Let `R` be an `n`-ary relation for which the third hypothesis fails at coordinates
`1` and `n`. Then `R` is the conjunction of its two projections:
`R = {(x,ā,y) : (x,ā) ∈ pr_{[n-1]}(R) and (ā,y) ∈ pr_{[n]∖{1}}(R)}`.

*Proof.* `⊆` is immediate. For `⊇`: from `(a₁,ā) ∈ pr_{[n-1]}(R)` get `bₙ` with
`(a₁,ā,bₙ) ∈ R`; from `(ā,aₙ) ∈ pr_{[n]∖{1}}(R)` get `b₁` with `(b₁,ā,aₙ) ∈ R`. Failure of
the hypothesis is exactly the assertion that `(a₁,ā,aₙ) ∈ R`. ∎

*Corollary.* A constraint that is crucial in a reduction satisfies the third hypothesis at
every pair of its coordinates.

*Proof.* Otherwise the constraint is equivalent to the conjunction of its two projections,
each of which is strictly weaker than it. Weakening it therefore replaces it by constraints
whose conjunction defines the same relation, so the weakened instance has the same solution
set — and in particular still has no solution in the reduction, contradicting cruciality. ∎

On the witness: `pr₁,₂(R) = {(x,z) : x ≡ z}` and `pr₂,₃(R) = {(z,y) : y ≡ z}`, whose
conjunction is `R`. Exactly the degenerate shape the corollary rules out.

*Our rendering:* carry criticality explicitly. Either add "every constraint relation is
critical" to the definition of a connected instance, or state `LEMConnectedProperties` for
crucial instances and cite the corollary. The second is cheaper and matches every call site.
This is the notion 2404 inherited from `LEMCrucialMeansIrreducible` and then stopped using.

---

## D7 — two gaps in the main induction

### (i) The endgame proves *connected*, but (1c) demands *linked*. **CONFIRMED, repaired.**

Both endgames of Case 2 finish with "…which means that `𝓘` is connected and satisfies (1b) if
its solution set is subdirect or (1c) otherwise". But (1c) requires a **linked** connected
subinstance, and only connectedness was established.

*Repair, via irreducibility.* Suppose `𝓘` is connected with non-subdirect solution set. Take
`𝓙 = Υ = 𝓘`, legitimate since an instance is a weakening, hence an expanded covering, of
itself. It remains to see `𝓘` is linked. If it were not, then `𝓘` itself would witness the
failure of irreducibility: its variables are among its own, each constraint is the projection
of itself onto all its variables, it is not fragmented (connectedness of the
constraint-adjacency graph forces constraints to share variables), it is not linked, and its
solution set is not subdirect — precisely conditions (i)–(v). Since `𝓘` is irreducible by
standing hypothesis, it is linked. ∎

Two lines, and it explains why irreducibility is a hypothesis of the theorem at all.

### (ii) Case 1 derives (1c) for the wrong reduction. **CONFIRMED, repaired.**

Case 1 obtains a 1-consistent `D⁽²⁾ ≤_T D⁽¹⁾`, shows `𝓘` is crucial in `D⁽²⁾`, and closes with
"applying the inductive assumption to `D⁽²⁾` we derive the required conditions".

Conditions (1a) and (1b) mention no reduction and transfer verbatim. (1c) does not: it asserts
an expanded covering **crucial in the ambient reduction**. The inductive hypothesis delivers
`𝓚` crucial in `D⁽²⁾`; the goal needs a covering crucial in `D⁽¹⁾`, and the containment runs
the wrong way — an instance with no solution in the smaller `D⁽²⁾` may have one in `D⁽¹⁾`.

**First, the induction structure, which is load-bearing and unstated.** The proof opens
"We prove the claim by induction on the size of `D⁽¹⁾`. *Let us prove (2) first.*" That
ordering is not stylistic. Part (2) at a given measure uses (1) only at strictly smaller
measure, whereas part (1) at that measure uses **(2) at the same measure** — Case 1 does
exactly this at `main.tex:3507`, applying (2) to a weakening `𝓙` of `𝓘` at the pair
`(D⁽¹⁾, D⁽²⁾)`. So the induction is really

> strong induction on `k = μ(D⁽¹⁾)`; at each level establish (2) for *all* instances, then (1)
> for all instances.

which is acyclic: `(2)_k ← (1)_{<k}`, `(1)_k ← (2)_k, (1)_{<k}`.

**Why that alone does not close the gap.** One would like to apply (2) to `𝓚` at
`(D⁽¹⁾, D⁽²⁾)` and conclude, contrapositively, that `𝓚⁽¹⁾` has no solution. But `𝓚` is an
expanded *covering*, so it has more variables than `𝓘`, and under `μ = Σ_x |D⁽¹⁾_x|` its
measure is **larger**, not equal. The device that works for a weakening does not work for a
covering. Nor is the measure easily repaired: `max_x` is preserved by coverings but not
decreased by `≤_T` reductions, which may be proper at only one variable.

**The repair, which avoids re-entering the induction.** Take the union with `𝓘` and reweaken.

*Proposition.* Under the hypotheses of Case 1, if (1c) holds for `(𝓘, D⁽²⁾)` then it holds for
`(𝓘, D⁽¹⁾)`.

*Proof.* Let `𝓚` be an expanded covering of `𝓘`, crucial in `D⁽²⁾`, with linked connected
subinstance `Υ` whose solution set is not subdirect. Put `𝓛 = 𝓚 ∧ 𝓘`.

`𝓛` is an expanded covering of `𝓘`: `𝓚` is one, `𝓘` is a weakening of itself hence one by
(p2), and the union of two expanded coverings is one by (p5).

`𝓛⁽¹⁾` has no solution: `𝓛` contains every constraint of `𝓘`, so a solution of `𝓛⁽¹⁾`
restricts on `Var(𝓘)` to a solution of `𝓘⁽¹⁾`, and `𝓘` is crucial in `D⁽¹⁾`.

Hence by Remark `GetCrucialInstance` we may weaken `𝓛` to an instance `𝓛'` crucial in `D⁽¹⁾`.

Every constraint of `𝓚` survives that weakening. Each is crucial in `D⁽²⁾`, so weakening it
yields a solution in `D⁽²⁾`, which lies in `D⁽¹⁾` as `D⁽²⁾ ⊆ D⁽¹⁾`; and weakening it inside any
weaker instance yields only more solutions. So each is already crucial in `D⁽¹⁾` at every stage
of the process, and the process only weakens constraints that are not.

Therefore `Υ ⊆ 𝓚 ⊆ 𝓛'`, its properties being intrinsic to `Υ` and untouched, and `𝓛'` is an
expanded covering of `𝓘` crucial in `D⁽¹⁾`. That is (1c) at `D⁽¹⁾`. ∎

The ingredients are (p2), (p5), `GetCrucialInstance`, and the observation that cruciality in a
*smaller* reduction gives the weakening half of cruciality in a larger one. No appeal to the
induction at a larger measure, so the measure `Σ_x |D⁽¹⁾_x|` survives intact.

*Our rendering:* state the induction as the two-phase scheme above — it must be explicit
anyway, since (1) legitimately uses (2) at the same level — and insert this proposition where
the source writes "we derive the required conditions".

---

## C10 — eliminating the projective alternative, and two steps under the call sites

Three separate things are needed here; only the first is what C10 asked about.

### (i) The elimination

**Lemma (no essentially unary quotient).** Let `U` be a finite algebra with a WNU term
operation `w` and `|U| ≥ 2`. Then some term operation of `U` depends on more than one
variable.

*Proof.* Suppose not, so every term operation of `U` has at most one non-dummy variable. A
WNU is idempotent by definition here, so `w(x,…,x) = x`. If `w` has a non-dummy coordinate
`i` then `w(x_1,…,x_n) = g(x_i)` for a unary `g`, and `g(x) = w(x,…,x) = x`, so `w = pr_i`;
if `w` has no non-dummy coordinate it is constant, and idempotence forces `|U| = 1`. So
`w = pr_i`. The WNU identities equate the `n` terms in which a single `y` sits at each position
in turn against a background of `x`s. Two of them are `w` with `y` at position `i`, which
evaluates to `y`, and `w` with `y` at some position `≠ i` (one exists, as `n ≥ 2`), which
evaluates to `x`. Hence `x = y` for all `x, y ∈ U`, i.e. `|U| = 1`. ∎

The same statement is Theorem 4.14, (1) ⇒ (3) of arXiv:2005.00593, where it is routed through
WNU-blockers; the direct proof above is shorter and is what a formalization should carry.

**Corollary.** If `A` has a WNU term operation then no `U ∈ HS(A)` with `|U| ≥ 2` is
essentially unary. *Proof.* The WNU identities and idempotence are identities, hence hold of
`w^U` for every `U ∈ HS(A)`; apply the lemma. ∎

**Proposition (Theorem 6.15 with two cases).** Let `A`, `B` be finite idempotent algebras
with WNU term operations, `R ≤_sd A × B`, and `C = {c ∈ A | ∀b ∈ B: (c,b) ∈ R}`. Then
`C = ∅`, or `C` is a central subuniverse of `A`, or `B` has a nontrivial binary absorbing
subuniverse.

*Proof.* Apply Theorem 6.15 of arXiv:2005.00593 in its three-case form. Cases 1 and 2 are the
second and third alternatives (case 1 being read with the convention that `∅` is central,
which the first alternative here absorbs). In case 3, `B` has a nontrivial projective
subuniverse `P`. By Lemma 3.4 of the same paper, either `P` is a binary absorbing subuniverse
of `B` — and `P` is nontrivial, so this is the third alternative — or there is an essentially
unary `U ∈ HS(B)` with `|U| ≥ 2`, which the corollary forbids. ∎

Zhuk runs this same elimination on this same trichotomy in the proof of his Theorem 4.15,
step (4) ⇒ (5). He never applies it to Theorem 6.15, which is why 2404's two-case form arrives
underived.

**What still has to be proved from scratch**, if the rendering is to be self-contained: 2005's
Theorem 6.15 itself, and its Lemma 3.4 (projective ⇒ BA or essentially unary quotient). Lemma
3.4 is short and I have checked it: with `R_n = A^n ∖ (A∖B)^n ∈ Inv(A)` (Lemma 3.1) and a
binary `B`-essential `R` (Barto–Kazda, our `LemAbsorptionImpliesEssential` at `n = 2`), put
`R' = R ∩ R_2` and `D = pr_1(R')`. Every pair of `R'` has exactly one coordinate in `B`, since
`R ∩ B² = ∅` and `R_2` forbids both outside; so
`S(x,y) = ∃x'∃y'\, R'(x,x') ∧ R'(y,y') ∧ R_2(x',y') ∧ R_2(x,y)` is exactly
`((D∩B) × (D∖B)) ∪ ((D∖B) × (D∩B))`, both parts nonempty by the two essentiality witnesses.
Then `σ(x,y) = ∃z\, S(x,z) ∧ S(y,z)` is the congruence on `D` with blocks `D∩B` and `D∖B`, and
`D/σ` has two elements. Projectivity gives each term operation `f` a coordinate `i` with
`f(b̄) ∈ B` whenever `b_i ∈ B`; preservation of `S` upgrades this to `f(b̄) ∈ D∖B` whenever
`b_i ∈ D∖B` (feed `f` a tuple opposite to `b̄` coordinatewise, possible as both blocks are
nonempty). So `f|_D` is `pr_i` modulo `σ`. Sound as written.

### (ii) The empty alternative is not removable

Our `conv:empty` forbids empty subuniverses, so the two-case form cannot be stated. It is
false without the `C = ∅` alternative: `A = B = ℤ_p` with `R = {(x, x+1) : x ∈ ℤ_p}` is
subdirect, has `C = ∅`, and `ℤ_p` has no nontrivial BA subuniverse.

Every call site discharges it by exhibiting an element of `C`, so nothing downstream changes.

### (iii) The full-fibre step, at `StrongSubalgebras.tex:545, 837, 921`

Each of subsubcases 1B3, 2A3, 2B3 asserts, of a relation `R'` on
`(B/δ)^{|A|} × (B_{m-1}/σ_m)`, that surjectivity of the projection onto the first `|A|`
coordinates yields a `d` with `(B/δ)^{|A|} × {d} ⊆ R'`. That inference is invalid in general.
What makes it true:

**Lemma (full fibre).** Let `F` be a finite set with `|F| ≤ N`, and let `W ⊆ F^N × E` satisfy
`pr_{1..N}(W) = F^N` and be closed under coordinate substitution: if `(x_1,…,x_N,e) ∈ W` and
`g : [N] → [N]` then `(x_{g(1)},…,x_{g(N)},e) ∈ W`. Then there is `d ∈ E` with
`F^N × {d} ⊆ W`.

*Proof.* Write `F = {F_1,…,F_t}`, `t ≤ N`, and let `x̄ = (F_1,…,F_t,F_t,…,F_t) ∈ F^N`. By
surjectivity pick `d` with `(x̄, d) ∈ W`. Any `ȳ ∈ F^N` is `x̄ ∘ g` for some `g : [N] → [N]`,
since every entry of `ȳ` occurs among the entries of `x̄`; closure gives `(ȳ, d) ∈ W`. ∎

The hypotheses hold at all three sites. In each, `R'` is cut out by a conjunction of unary and
binary conditions on the first `|A|` entries together with a condition relating each entry to
the last coordinate — at line 837, `∀i,j: (a_i,a_j) ∈ σ ∩ ω`, `∀i: a_i ∈ B_{m-1}`, and
`(a_i,b) ∈ σ_m` — and any such condition survives substituting entries for one another. And
`|B/δ| ≤ |A|` because `B ⊆ A`.

This is why the arity is `|A|`: the exponent must be at least the number of blocks so that one
tuple can enumerate them. A rendering that normalises it away breaks all three proofs.

### (iv) Two obligations per call site

At `StrongSubalgebras.tex:551, 843, 928` the appeal concludes "a BA subuniverse on `X` or a
center on `Y`, which contradicts the definition of a dividing congruence". Two steps sit
between the lemma and that contradiction:

- *Properness.* "BA and center free" (`main.tex:1363`) forbids only **proper** nonempty
  central subuniverses. The witness is printed two lines above each appeal — at 533, 824, 903,
  the statement that `(…)^{|A|} × B_n/σ_n ⊄ R'` — but never linked to it. Supply the link.
- *Power to base.* Alternative (2) produces a BA subuniverse of `(B/δ)^{|A|}`, not of `B/δ`.
  The bridge is `LEMBACenterSOnPowerImplies`, cited at line 2024 and omitted at the other
  three.

---

## D11–D13 — one hypothesis repairs all three

Call a bridge `δ` from `σ` to `σ` **pair-reflexive** if `(x₁,x₂) ∈ proj_{1,2}(δ)` implies
`(x₁,x₂,x₁,x₂) ∈ δ`. It is not a new notion: `LEMPCCongruencePropertyInductiveStep`
(`StrongSubalgebras.tex:1379`) already carries it, as hypothesis (2).

**Lemma (free of charge).** For any bridge `δ` from `σ` to `σ`, the relation

  `δ°(x₁,x₂,x₃,x₄) = ∃x₅∃x₆ δ(x₁,x₂,x₅,x₆) ∧ δ(x₃,x₄,x₅,x₆)`

is a pair-reflexive bridge from `σ` to `σ`, symmetric under swapping the two pairs, with
`proj_{1,2}(δ°) = proj_{3,4}(δ°) = proj_{1,2}(δ)` and `δ°~ = δ̃ ∘ δ̃^{-1} ⊇ δ̃`.

*Proof.* Pair-reflexivity and symmetry are immediate from the shape of the formula. Clause (4)
holds because `(x₁,x₂) ∈ σ ⟺ (x₅,x₆) ∈ σ ⟺ (x₃,x₄) ∈ σ`; clause (3) because
`(x₁,x₂) ∈ proj_{1,2}(δ)` gives `(x₁,x₂,x₁,x₂) ∈ δ°`, and conversely `δ°` cannot project
further than `δ` does. Stability is inherited. The last equality is the composition formula
`\widetilde{δ_1 ∘ δ_2} = \widetilde{δ_1} ∘ \widetilde{δ_2}` applied to `δ` and `δ^{-1}`. ∎

**D11.** Replace `StrongSubalgebras.tex:1154–1157` by `σ = δ°`. Everything the proof then uses
is supplied: `ω = proj_{1,2}(σ) = proj_{1,2}(δ)` is linked by hypothesis; `ω ⊆ σ̃` because
`ω ⊆ δ̃ ⊆ δ̃ ∘ δ̃^{-1}` (the second inclusion because `δ̃` is reflexive, which in turn holds
because `0_A ⊆ proj_{1,2}(δ) ⊆ δ̃`); `(a,b,a,b) ∈ σ` by pair-reflexivity; `(a,a,b,b) ∈ σ` by
`ω ⊆ σ̃`; and `σ̃` is symmetric, which is what legitimises the `WLOG` at line 1170.

**D12.** Add pair-reflexivity to `LEMNiceBridgeGivesAbelianGroup`. The proof's one broken step
then works: `δ ⊆ δ ∘ δ` by taking `(y₁,y₂) = (x₁,x₂)` in the composition, so
`δ₀ = δ ∘ δ ⊇ δ`, and the counting argument finishes as written. In the structural language of
`NOTES-verification.md`, pair-reflexivity says `φ = id`, which is exactly the hypothesis the
`ℤ₃` counterexample violates.

**D13.** Add pair-reflexivity to `LEMNontrivialReflexiveBridgeImplies`. Then at line 1273:

*Claim.* `σ* ⊆ proj_{1,2}(δ)`.
*Proof.* `proj_{1,2}(δ)` is a subalgebra of `A²`, stable under `σ` by clause (1), and
`⊋ σ` by clause (3); `σ*` is the minimal such. ∎

So for `(x₁,x₂) ∈ σ* ∩ B²`, pair-reflexivity puts `(x₁,x₂,x₁,x₂)` in
`δ' = δ ∩ B⁴ ∩ (σ*×σ*)`, whence `proj_{1,2}(δ') = σ* ∩ B²` — subdirect on `B` because `σ*` is
reflexive, and connected because `B` is a block of `LeftLinked(σ*)`. The same computation
gives `proj_{1,2}(δ ∩ B⁴) = B²` at line 1290 once `B² ⊆ σ*` is known.

**Why it costs nothing.** `LEMNontrivialReflexiveBridgeImplies` is cited once in the paper, at
line 1368, on the object `δ°` — pair-reflexive by the lemma above. `LEMNiceBridgeGivesAbelianGroup`
is cited once, from inside that proof, on `δ° ∩ B⁴`, which inherits it.

*Our rendering:* state pair-reflexivity as part of the definition of the *symmetrised* bridge
and carry it through §5.4. It is the property that makes "compose the bridge with itself"
mean what the prose wants it to mean.

## D14 — solved: the citation needs the subrelation form, not the box form

The step at `StrongSubalgebras.tex:1394` is **true**. What is wrong is the citation.
`LEMBACenterLinkedness` (Barto–Kozik Prop. 2.15(i)) restricts a relation by a **box**
`B₁ × B₂`, and `proj_{1,2,3}(δ ∩ B⁴)` is not a box restriction of `proj_{1,2,3}(δ)` — a tuple
of `δ` whose first three coordinates lie in `B` need not have its fourth there. Applied to
`W = proj_{1,2,3}(δ)` with `B₁ = P ∩ B²`, `B₂ = B`, the box form yields linkedness of
`proj_{1,2,3}(δ) ∩ B³`, which is genuinely larger in general: for the min-semilattice on
`{0,1,2}` with `B = {0,1}`, the subalgebra `K = {(0,0),(1,2)} ≤ A²` meets `B²` and has
`1 ∈ proj_1(K) ∩ B`, while `proj_1(K ∩ B²) = {0}`.

What is needed instead is the **subrelation** form of the same principle, and it follows from
tools already present in §5.

**Lemma A (no absorbing diagonal).** Let `C` be a finite idempotent algebra with `|C| ≥ 2`.
Then `0_C` is not an absorbing subuniverse of `C²`, of any arity; in particular
`0_C ≰_{BA} C²` and `0_C ≰_C C²`.

*Proof.* Suppose `t` is `n`-ary and absorbs at every position. Fix `i`, take `a_j ∈ C` for
`j ≠ i` and `b,c ∈ C`, and apply `t` coordinatewise to the tuples `(a_j,a_j)` for `j ≠ i` and
`(b,c)` at position `i`. The result `(t(ā;b), t(ā;c))` lies in `0_C`, so `t(ā;b) = t(ā;c)`.
As `b,c` were arbitrary, `t` does not depend on its `i`-th argument — and this holds for every
`i`, so `t` is constant. Idempotence then forces `|C| = 1`. A central subuniverse is
absorbing by definition (`main.tex:1345`), so the central case is included. ∎

**Lemma B (absorption preserves linkedness — subrelation form).** Let `W ≤_sd P × A` be
linked and let `∅ ≠ W' ≤_T W` with `T ∈ {BA, C}`. Put `P' = proj_1(W')`, `A' = proj_2(W')`.
Then `W' ≤_sd P' × A'` is linked.

*Proof.* Let `Φ_k(x,y)` be the pp-formula in one binary relation symbol obtained by iterating
`x ∼ y ⟺ ∃z\, W(x,z) ∧ W(y,z)` `k` times. `W ∘ W^{-1}` is reflexive and symmetric on `P`
because `W` is subdirect, so for `k ≥ |P|` the formula `Φ_k` interpreted in `W` defines
`LeftLinked(W) = P²`; interpreted in `W'` and for `k ≥ |P'|` it defines
`λ := LeftLinked(W')`. Take `k ≥ max(|P|,|P'|)`. By `LEMBACenterSImplyPPDefinition`, replacing
every occurrence of `W` by `W' <_T W` gives `λ ≤_T P²`. Since `λ ⊆ P'²` and `P'² ≤ P²`,
`LEMBACenterImplyIntersection` gives `λ ≤_T P'²`. Now `λ` is a congruence on `P'`, so
`λ × λ` is a congruence on the algebra `P'²`, and the image of `λ` under
`P'² ↠ (P'/λ)²` is `0_{P'/λ}`; by `LEMBACenterSImplyFactor`,
`0_{P'/λ} ≤_T (P'/λ)²`. Lemma A forces `|P'/λ| = 1`, i.e. `λ = P'²`. ∎

**The step.** `W = proj_{1,2,3}(δ)` is subdirect over `P × A` (`P = proj_{1,2}(δ)`) and linked
by hypothesis (3). Write

  `W(x₁,x₂,x₃) = ∃x₄\, δ(x₁,x₂,x₃,x₄) ∧ A(x₁) ∧ A(x₂) ∧ A(x₃) ∧ A(x₄)`

with `A` the full unary relation, and replace `A` by `B`. `LEMBACenterSImplyPPDefinition`
replaces *each appearance* of a relation, so this is a **single** application — no transitivity
of `≤_{BA}` or `≤_C` is needed, which is worth arranging, since transitivity of `≤_C` is one of
the things Zhuk 2021 asserts in passing. Hence

  `W' := proj_{1,2,3}(δ ∩ B⁴) ≤_T W`.

`W'` is nonempty, containing `(b,b,b)` for every `b ∈ B` because `δ` is reflexive. Its
projections are `proj_{1,2}(W') = P ∩ B²` — hypothesis (2) puts `(x₁,x₂,x₁,x₂)` in `δ ∩ B⁴`
for every `(x₁,x₂) ∈ P ∩ B²` — and `proj_3(W') = B`. Lemma B now gives that `W'` is linked,
i.e. `RightLinked(proj_{1,2,3}(δ ∩ B⁴)) = B²`, which is exactly what Case 1 asserts. The rest
of Case 1 is unchanged. ∎

Lemma B also discharges, for free, the subdirectness hypothesis that the box form needed and
that the source never checked.

**Machine-checked.** Over five 2- and 3-element and four 4-element Taylor algebras
(min-semilattices, the dual discriminator, `ℤ₂` minority, `ℤ₃`, `ℤ₂²`, a semilattice square):
`527 + 99 477` pairs (`W` linked subdirect, `W'` a proper binary-absorbing subuniverse of
`W`) with **no counterexample to Lemma B**, and `0_C` absorbing `C²` in no algebra tested.

*Our rendering:* state Lemmas A and B in §5.1 alongside `LEMBACenterLinkedness` — B is the
form the paper actually uses, here and arguably at the other restriction sites — and cite B
at line 1394.

---

## D15 — `LEMMainExistenceOfIrreducibleCongruence`: read `δ` for `σ`, and restore stability

**The step.** `δ ⊇ σ` maximal with `|B/δ| > 1`; `B/δ` BA and center free; suppose
`δ = S₁ ∩ ⋯ ∩ S_k` with each `Sᵢ ⊋ δ` **stable under `δ`** (this is the definition of
irreducible at `main.tex:1237`, and the source drops the stability clause). Pick `i` with
`B² ⊄ Sᵢ`, which exists because otherwise `B² ⊆ δ`.

*Properness.* `(Sᵢ ∩ B²)/δ ⊊ (B/δ)²`. Indeed, stability under `δ` makes `Sᵢ` a union of
products of `δ`-blocks, so if every pair of `δ`-blocks meeting `B` contained a point of
`Sᵢ ∩ B²`, then `Sᵢ` would contain every such product and hence `B² ⊆ Sᵢ`. ∎

*Linkedness.* `LeftLinked(Sᵢ)` is a congruence containing `Sᵢ ⊋ δ ⊇ σ`, so by maximality of
`δ` it collapses `B`, i.e. `B² ⊆ LeftLinked(Sᵢ)`, i.e.
`(LeftLinked(Sᵢ) ∩ B²)/δ = (B/δ)²`. `LEMLeftLinkedStayFull` **with the congruence `δ`** — its
hypothesis "`B₁/σ` is BA and center free" is met by `B/δ`, which is exactly what was proved two
lines earlier — gives `LeftLinked(Sᵢ ∩ B²)/δ = (B/δ)²`.

*Conclusion.* `(Sᵢ ∩ B²)/δ` is a proper linked subdirect relation on `B/δ`, so
`LEMLinkedImpliesBACenter` yields a proper nonempty BA or central subuniverse of `B/δ`,
contradicting the second line. Hence `δ` is irreducible. ∎

The source writes `σ` for `δ` at both lines 2220 and 2222 while stating the conclusion for
`B/δ`; with `σ` the properness step has no support and the conclusion does not match the
relation's domain.

## D16 — `LEMLInearOnTheTopIsEasy`: **solved**, by a different route

The source's route (fix `a`, show `ξ(x,z) = ζ(x,a,z)` is bijective) can be pushed further than
the source pushes it, but it stalls at excluding a proper BA or central subuniverse of `A`.
Abandon it. The lemma follows from a statement we have already repaired.

**Proposition.** Let `σ` be a linear congruence on `A ∈ 𝒱ₙ` with `σ* = A²`. Then
`A/σ ≅ ℤ_p` for some prime `p`.

*Proof.* `σ` is linear, so by `LEMLinearEquivalentConditions`(1 ⇒ 2) there is a bridge `δ` from
`σ` to `σ` with `δ̃ ⊋ σ`. Replace `δ` by `δ° = δ ∘ δ^{-1}`, which is a symmetric pair-reflexive
bridge with `δ̃° ⊇ δ̃ ⊋ σ` (the lemma of D11–D13). `LEMNontrivialReflexiveBridgeImplies` then
applies: (1) `σ*` is a congruence, and (3) there is a prime `p` such that for every block `B`
of `σ*`,

  `(B/σ; (δ° ∩ B⁴)/σ) ≅ (ℤ_p^{n_B}; x₁ − x₂ = x₃ − x₄)`.

By hypothesis `σ* = A²`, which as a congruence has the single block `A`. So
`A/σ ≅ ℤ_p^m` for some `m ≥ 0`, with the group structure carried by the difference relation.

`m = 0` is impossible: it gives `|A/σ| = 1`, i.e. `σ = A²`, and an irreducible congruence is
proper (convention C4).

`m ≥ 2` is impossible, **by irreducibility**. `A/σ` is Abelian, hence affine over `ℤ_p`
(`LEMAbelianEqualAffineForWNU`), so `w` acts on it as `Σᵢcᵢxᵢ` with `Σcᵢ = 1` — the constant
term vanishes by idempotence. For `i ∈ [m]` put `θᵢ = {(x,y) ∈ (ℤ_p^m)² : xᵢ = yᵢ}`. Each `θᵢ`
is a linear subspace of `(ℤ_p^m)²`, hence closed under any coordinatewise affine map, hence a
subalgebra of `(A/σ)²`; it is stable under `0_{A/σ}` vacuously; and `θᵢ ⊋ 0_{A/σ}` because
`m ≥ 2`. But `⋂ᵢ θᵢ = 0_{A/σ}`, so `0_{A/σ}` is reducible — and `σ` is irreducible iff
`0_{A/σ}` is (convention C9, item 2). Contradiction.

So `m = 1` and `A/σ ≅ ℤ_p` as groups. It is an isomorphism **of algebras** because `w` acts as
`x₁ + ⋯ + xₙ`: that is the proposition of convention item C1, whose proof runs exactly here —
the WNU identities force all `cᵢ` equal, specialness forces `c² = c`, and `nc = 1` rules out
`c = 0`. ∎

This route uses only in-paper material plus C1, where the source's route imports
`LEMBuildingPerfectCongruence` (Zhuk 2020, Cor. 8.17.1) — so it is also **one fewer external
dependency**.

### Salvage: the source's `ζ` really is a function

Worth keeping, because it repairs half of the original argument and is needed if the
perfect-linear machinery is used elsewhere.

**Lemma.** If `ζ ≤ A × A × ℤ_p` witnesses that `σ` is a perfect linear congruence, then `ζ` is
the graph of a homomorphism `G : A² → ℤ_p` with `G^{-1}(0) = σ`.

*Proof.* Put `t(x,y,z) = w(x,y,…,y,z)` with `n − 2` copies of `y`. On `ℤ_p` this is
`x + (n−2)y + z = x − y + z`, because `p | n − 1` (C1). Let `b, b', b''` lie in the fibre of
`ζ` over `(a₁,a₂)`. Applying `t` to the three tuples `(a₁,a₂,b)`, `(a₁,a₂,b')`, `(a₁,a₂,b'')`
gives `(t(a₁,a₁,a₁), t(a₂,a₂,a₂), b − b' + b'') = (a₁, a₂, b − b' + b'')` by idempotence. So
the fibre is closed under `x − y + z`, hence is a coset of a subgroup of `ℤ_p`: empty, a
singleton, or all of `ℤ_p`. It is not all of `ℤ_p`, since that fibre would contain `0` and a
nonzero element, making `(a₁,a₂)` both `σ`-related and not. It is not empty on `σ*`, since
`proj_{1,2}(ζ) = σ*`. ∎

## D17 — **solved**: pass to a minimal subfamily, and the type argument does the rest

Case 1 of `LEMMaximalMultExtention` cannot be closed as written — see the analysis below — but
the citation of `THMMainStableIntersection` was pointing at the right tool. It just has to be
applied to a different family, and the case then disappears rather than being contradicted.

Write `X̄` for `X/σ`, and `C₁ = C₁¹ ∩ ⋯ ∩ C₁ᵗ` with `C₁ʲ <_{T(σⱼ)}^A B₁`.

**Step 1 (minimal subfamily).** By `CORPropagationModuloCongruence`(t), each `C̄₁ʲ` is `B̄₁`, or
`<_S B̄₁`, or `<_T B̄₁`. Choose `F ⊆ {C̄₁¹,…,C̄₁ᵗ}` **minimal** with `⋂F ∩ B̄₂ = ∅`. One exists,
since the whole family has `⋂ ∩ B̄₂ = C̄₁ ∩ B̄₂ = ∅`; and `F ≠ ∅`, since `⋂∅ = B̄₁` meets `B̄₂`.
No member of `F` equals `B̄₁`, since such a member constrains nothing and could be dropped.

**Step 2 (walk down `B̄₂`'s chain).** `⋂F ∩ Ā = ⋂F ≠ ∅` and `⋂F ∩ B̄₂ = ∅`, so along a chain
witnessing `B̄₂ ⋘ Ā` there is a first step `B̄₂' <_{T'(τ)} B̄₂''` with `⋂F ∩ B̄₂' = ∅` and
`⋂F ∩ B̄₂'' ≠ ∅`.

**Step 3 (types).** Apply `THMMainStableIntersection` to the family `F ∪ {B̄₂'}`, with ambients
`B̄₁` for the members of `F` and `B̄₂''` for `B̄₂'`. Its hypothesis (2) is the empty
intersection, which is Step 2. Hypothesis (3), leave-one-out, holds in both shapes:

- omit a member `C̄₁ᵏ ∈ F`: minimality of `F` gives `⋂(F∖\{k\}) ∩ B̄₂ ≠ ∅`, and `B̄₂ ⊆ B̄₂'`,
  and everything in sight lies in `B̄₁`;
- omit `B̄₂'`: that is `⋂F ∩ B̄₂'' ≠ ∅`, which is Step 2.

So all the types coincide, and the theorem's four conclusions allow only `BA`, `C`, `L` or
`PC`. **Hence no member of `F` has type `S` in `B̄₁`.**

**Step 4 (the case evaporates).** By Step 1 each member of `F` is `B̄₁`, `<_S B̄₁` or `<_T B̄₁`;
the first is excluded by minimality and the second by Step 3. So every member is `<_T B̄₁`, and

  `⋂F <_{ℳT}^{Ā} B̄₁`,

proper because `⋂F ∩ B̄₂ = ∅` while `B̄₁ ∩ B̄₂ ≠ ∅`. That is exactly what Case 2 needs, with
`⋂F` in place of `C̄₁` — and **the ambient is still `B̄₁`**, so `LEMMultiplyByAllLinear` returns
congruences `δᵢ` with `δᵢ* ⊇ (B̄₁)²`, and their preimages `ωᵢ ⊇ σ` satisfy `ωᵢ* ⊇ B₁²`, as the
statement requires.

**Step 5 (back to `C₁`).** Let `C₁'` be the preimage of `⋂F`, so `C₁ ⊆ C₁'`. Step 4 gives
`(C₁' ∘ (ω₁ ∩ ⋯ ∩ ω_r)) ∩ B₂ = ∅`, hence `(C₁ ∘ (ω₁ ∩ ⋯ ∩ ω_r)) ∩ B₂ = ∅`. Since each
`ωᵢ ⊇ σ` and `σ` is maximal with that property, `σ = ω₁ ∩ ⋯ ∩ ω_r`. ∎

So the S-free split disappears: one never needs `B̄₁` to be S-free, only that a *minimal*
subfamily cutting `B̄₂` out contains no `S`-typed member, which the stable-intersection theorem
delivers.

### Why the source's Case 1 cannot be patched in place

Worth recording, because it is what forced the detour. The two facts the source derives —
that a BA-and-central `D ≤ E <_S B̄₁` meets both `C̄₁` and `B̄₂` — are true, but come from
`LEMStrongNonemptyIntersection`, not from the theorem cited. And they cannot yield
`C̄₁ ∩ B̄₂ ≠ ∅`, because the whole configuration **reproduces itself** on `D`: `D ⋘ Ā`,
`C̄₁ ∩ D ⋘ D`, `B̄₂ ∩ D ⋘ D`, still disjoint, with `D ∩ B̄₂ ≠ ∅`. Every consequence of the two
facts survives the descent, so no iteration of them closes the case. The descent is not
useless — `C₁ ∩ D ≤_{ℳT}^A D` properly, so the lemma's hypotheses are inherited and an
induction on `|B₁|` is available — but it shrinks the ambient, and the conclusion's congruence
family is indexed by the ambient (`ω* ⊇ B₁²`) while the one call site (`main.tex:2685`)
consumes the original `B₁` in one of its two branches. Step 1 above avoids the descent
altogether.

---

## Status

| | fixable? | needs new mathematics? |
|---|---|---|
| D2 | yes, one line | no |
| D4 | yes | no — a citation Zhuk dropped, plus a reduction |
| D8 | yes | no — short, but the proof is genuinely absent from the source |
| D6 | yes | no — cruciality supplies the missing hypothesis |
| D7(i) | yes | no — two lines, via irreducibility |
| D7(ii) | yes | no — union with `𝓘`, reweaken; plus the two-phase induction made explicit |
| C10 | yes | no — the elimination is Lemma 3.4 plus "WNU forbids an essentially unary quotient" |
| D11 | yes, one character | no |
| D12 | yes | no — the statement was wrong, not the mathematics; add pair-reflexivity |
| D13 | yes | no — same hypothesis as D12 |
| D14 | yes | no — the citation needed the subrelation form of absorption-preserves-linkedness |
| D15 | yes | no — read `δ` for `σ`, and restore the stability clause |
| D16 | yes | no — via `LEMNontrivialReflexiveBridgeImplies`(3) and irreducibility; one fewer external import than the source |
| D17 | yes | no — pass to a minimal subfamily; `THMMainStableIntersection` then excludes type `S` |
