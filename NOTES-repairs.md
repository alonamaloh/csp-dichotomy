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

## Status

| | fixable? | needs new mathematics? |
|---|---|---|
| D2 | yes, one line | no |
| D4 | yes | no — a citation Zhuk dropped, plus a reduction |
| D8 | yes | no — short, but the proof is genuinely absent from the source |
