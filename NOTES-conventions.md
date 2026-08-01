# Conventions, legislated

The ten items marked **convention** in `ch10-defects.tex` are places where the source admits
more than one reading and the choice is invisible in prose but forced in a formalization.
This file fixes each one, says what the rendering does, and — where the item turned out not to
be a matter of choice at all — gives the argument.

Two of the ten are not conventions on inspection. **C1** is a theorem, and it is proved below.
**C10** is a missing lemma, resolved in `NOTES-verification.md`. The remaining eight are
genuine choices, and for six of them the source's own text makes one choice the only coherent
one.

---

## C1 — `ℤ_p ∈ 𝒱ₙ` requires `p | n−1`. **Not a convention: a theorem.**

`main.tex:1115` declares *"In the paper every algebra `ℤ_p` belongs to `𝒱ₙ` for a fixed `n`,
hence the algebra `ℤ_p` is uniquely defined"*, with `w^{ℤ_p} = x₁ + ⋯ + xₙ (mod p)`. That
operation is idempotent only when `n ≡ 1 (mod p)`, so the declaration is a constraint on
`p`, and the source never says where the constraint comes from. It comes from specialness.

**Proposition.** Let `A ∈ 𝒱ₙ` and let `σ` be a linear congruence on `A` with prime `p`, so
that some block `B` of `σ*` has `B/σ` affine over `ℤ_p` with `|B/σ| > 1`. Then `p | n−1`, and
the operation `w` induces `x₁ + ⋯ + xₙ` on `B/σ`.

*Proof.* `σ*` is a congruence in the linear case, so `B` is a subalgebra and `B/σ` is an
algebra on which `w` acts. `B/σ` is affine, hence polynomially equivalent to a `ℤ_p`-module,
so `w` acts as `w(x̄) = Σᵢ cᵢxᵢ + d`. Idempotence gives `Σᵢ cᵢ = 1` and `d = 0`. The WNU
identities `w(y,x,…,x) = w(x,y,x,…,x) = ⋯` read `c₁y + (1−c₁)x = c₂y + (1−c₂)x = ⋯`, so all
`cᵢ` are equal to a single `c` with `nc = 1`. Specialness,
`w(x,…,x,y) = w(x,…,x,w(x,…,x,y))`, compares the coefficient of `y` on the two sides and
gives `c² = c`, so `c ∈ {0,1}`; `c = 0` contradicts `nc = 1`. Hence `c = 1`, `n ≡ 1 (mod p)`,
and `w` acts as the sum. ∎

Verified by enumeration for `p ∈ {2,3,5,7}` and `3 ≤ n < 12`: a special idempotent affine WNU
of arity `n` on `ℤ_p` exists exactly when `p | n−1`, and is then `x₁+⋯+xₙ`.

**Rendering.** State the proposition where `ℤ_p` is first used as an algebra, and *separate the
two roles of `ℤ_p`*: as the abelian group `(ℤ_p; +, −)` supplying the relation
`x₁−x₂ = x₃−x₄` in the definition of a linear congruence, where no arity constraint arises;
and as the algebra `(ℤ_p; x₁+⋯+xₙ) ∈ 𝒱ₙ`, where it does. Only the second occurs in
`main.tex:1300` (`ζ ≤ A × A × ℤ_p`, a subalgebra of a product, which requires a common
signature) and in `main.tex:3484`.

## C2 — `σ*` is a tolerance. **Legislated.**

`σ*` is defined (`main.tex:1246`) as the minimal `δ ≤ A × A` with `δ ⊋ σ` and `δ` stable
under `σ`. Nothing in that makes it transitive.

**Rendering.** `σ*` is a reflexive symmetric subalgebra of `A²`, and *not* a congruence. Both
facts need one line and neither is in the source:

- *Existence and uniqueness of the minimum.* If `δ₁, δ₂` are two such relations then `δ₁∩δ₂`
  is one too unless it equals `σ`, and `δ₁∩δ₂ = σ` is exactly what irreducibility forbids. So
  the family is closed under intersection and has a least element.
- *Symmetry.* `(σ*)^{-1}` is another such relation, so it equals `σ*` by minimality. This is
  used silently at `StrongSubalgebras.tex:1538` ("switching `x₁` and `x₂`").
- *Reflexivity.* `σ ⊆ σ*`.

That `σ*` is a congruence is *item (2) of the definition of a linear congruence*
(`main.tex:1371`) and *conclusion (1) of `LEMNontrivialReflexiveBridgeImplies`* — i.e. it is
a property of linear congruences, proved, not a property of irreducible ones. Typing it as a
congruence would make item (2) vacuous and collapse the linear/PC distinction.

## C3 — the empty set. **Legislated, and it bites two statements.**

`∅` is a subuniverse of every idempotent algebra, is vacuously absorbing (`t(∅,…,A,…,∅) ⊆ ∅`
holds because the left side is empty) and vacuously central (the clause quantifies over
`a ∈ A ∖ C` against `Sg(∅) = ∅`).

**Rendering.** Follow `main.tex:1629` — *"we do not allow empty subuniverses"* — and make
`⋘`, `<_T`, `≤_T` relations between nonempty sets, with the dotted variants for the empty
case, as `ch1-conventions.tex` already does. Then two statements must be restated, because
they are true in the source only by the vacuous reading:

- `LEMCentralRelationImplies` (`StrongSubalgebras.tex:208`) needs a third alternative
  `C = ∅`. Witness that it is needed: `A = B = ℤ_p`, `R = {(x,x+1)}`, `C = ∅`, and `ℤ_p` has
  no nontrivial BA subuniverse. Every call site discharges the new alternative by exhibiting
  a point of `C`.
- `LEMLinkedImpliesBACenter` (`StrongSubalgebras.tex:222`) concludes *"there exists a BA or
  central subuniverse on `A` or `B`"* with no properness. Read literally it is vacuous —
  `A` is a BA subuniverse of itself. Insert *proper nonempty*, which is how it is used at
  `StrongSubalgebras.tex:1282`.
- The clause defining `<_S` (`main.tex:1522`) needs its `D` nonempty, else it is universally
  true.

## C4 — is `σ = A²` irreducible? **Legislated: the empty family is allowed, so no.**

The source gives two formulations of irreducibility (`main.tex:1237`), and *they agree only
under the empty-family reading*, which settles the question.

- Formulation 1: `σ` is not an intersection of *other* stable subalgebras of `A²`. The empty
  intersection is `A²`, so `σ = A²` is reducible.
- Formulation 2: there are no `S₁,…,S_k ≤ A/σ × A/σ` with `0_{A/σ} = ⋂Sᵢ` and `Sᵢ ≠ 0_{A/σ}`.
  With `k = 0` this says `0_{A/σ} ≠ (A/σ)²`, i.e. `|A/σ| > 1`, i.e. `σ ≠ A²`.

Forbid the empty family and formulation 2 no longer excludes `σ = A²` while formulation 1
still does. **Rendering.** Allow `k = 0`. Then irreducible implies proper, `σ*` exists, and
`\cite{ZhukJACM}`'s word "proper" — which `\cite{ZhukSimplified}` drops — is recovered as a
consequence rather than being reinstated by hand.

## C5 — `⋘` is data. **Legislated, and §5.5 shows why.**

`C ⋘^A B` is defined (`main.tex:1588`) as the existence of a chain
`C = Bₙ <_{Tₙ} ⋯ <_{T₁} B₀ = B`; several §5 proofs then speak of *"the dividing congruences
coming from `C ⋘^A B`"* (`main.tex:1600`), which is a function of the chain, not of the pair.

The sharpest instance is the `D × D` case of `LEMTwoStableIntersection`
(`StrongSubalgebras.tex:1840`). The step works only if the chain witnessing `C₂ ⋘ A` is the
chain witnessing `B₂ ⋘ A` extended by the single step `C₂ <_{D(σ₂)} B₂` — that is what makes
the dividing congruences of `C₂ ⋘ A` equal to those of `B₂ ⋘ A` together with `σ₂`, which is
the whole content of the appeal.

**Rendering.** `⋘` carries its witness: a list of pairs (subset, typed step with its
congruence). Statements that mention "the congruences coming from `C ⋘ B`" take the chain as
an argument. Extension of a chain by one step is an operation on the data, and the `⋘`
relation is its propositional truncation, used only where no congruence is named.

## C6 — "dimension". **Legislated: composition length.**

`∏ᵢ ℤ_{qᵢ}` with distinct primes is not a vector space over anything, so it has no dimension.

**Rendering.** Use the composition length of the finite abelian group, which for `ℤ_p^n` is
`n` and agrees with the source wherever the source is meaningful, and prove additivity along
short exact sequences (Jordan–Hölder). Nothing in §5 uses the notion; it is confined to the
step-2 linear-algebra argument.

## C7 — "linked instance". **Legislated: the per-variable definition.**

Two inequivalent definitions coexist: global connectivity of the value graph, in Informal
Claim (IC3), and the per-variable condition in §3.1. The second does not imply the first,
because a fragmented instance is per-variable linked in each component.

**Rendering.** Use the §3.1 definition and carry non-fragmentation as a separate hypothesis
wherever the informal reading was doing that work. This is not cosmetic: the retracted D10
turned on exactly this pair of conditions at the `SolveNonlinked` call site.

## C8 — quotients of subsets. **Legislated.**

`B/σ` denotes the *image* `{b/σ : b ∈ B}` in `A/σ`, for `B` any subset of `A` and `σ` a
congruence on `A` — not the quotient of `B` by a congruence of `B`. Consequently
`(C₁ ∩ ⋯ ∩ C_t)/δ ⊆ ⋂ᵢ Cᵢ/δ` always, with equality *false* in general.

**Rendering.** Define the image operation once, prove only the inclusion, and flag every site
that needs the reverse. The reverse inclusion is established on the fly inside
`lem:propagation`(fm) and must be extracted as a standalone lemma with its hypothesis visible.

## C9 — the sentences beginning "Notice that". **Legislated: promote to lemmas.**

Four items, three of them from the source's own "Notice that" sentences.

1. `main.tex:1378`: the relation `S` from item (3) of the definition of a linear congruence is
   a bridge from `σ` to `σ` with `S̃ = proj_{1,2}(S) = proj_{3,4}(S) = σ*`. **Checked, true.**
   Clause (4) is `x₁−x₂ = 0 ⟺ x₃−x₄ = 0` inside each block; clause (3) holds because some
   block has `n_B ≥ 1`, else `σ* = σ`; `S̃ = σ*` because `x−x = y−y` always. It is consumed
   at `StrongSubalgebras.tex:1360` (direction 1 ⇒ 2 of `LEMLinearEquivalentConditions`).
2. `main.tex:1386`: `σ` is irreducible / PC / linear iff `0_{A/σ}` is. Needed to justify the
   "factorize by `σ` and assume `σ = 0`" opening used in three §5.4 proofs.
3. `main.tex:1550`: the two formulations of S-freeness agree. **Trivial** — unfold `<_S`
   (`main.tex:1522`): `C <_S A` iff some `D ≤ C` is simultaneously BA and central in `A`, so
   `∃C <_S A` iff `∃D <_{BA,C} A`. One line, but it must be written, since `S`-freeness is a
   hypothesis of `CORPropagationModuloCongruence`(m).
4. `lem:rect-basics` of the blueprint belongs to the same list.

## C10 — the dropped projective alternative. **Resolved; see `NOTES-verification.md`.**

Not a convention: a lemma with a proof. Case 3 of Zhuk 2021 Theorem 6.15 is eliminable under
the standing Taylor hypothesis via Lemma 3.4 of the same paper plus "a WNU forbids an
essentially unary quotient of size ≥ 2". The surviving two-case statement still needs the
`C = ∅` alternative of C3.

---

## What legislating cost

Six of the ten (C2, C3, C4, C5, C8, C9) are decided by internal evidence: in each case one
reading makes some statement of the source true or some proof valid and the other does not, so
the "choice" is really a reconstruction. Two (C6, C7) are free choices where the source is
simply ambiguous and either reading can be made to work. Two (C1, C10) are not conventions at
all and have been proved.
