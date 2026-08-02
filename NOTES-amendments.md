# The amendment ledger

Every obligation the reading has produced, with the amendment our rendering makes and where
its proof lives. This is the checklist the writing works from; if an item is not here, the
rendering does not silently differ from the source.

`V` = `NOTES-verification.md`, `R` = `NOTES-repairs.md`, `C` = `NOTES-conventions.md`.

---

## 1. Defects — things the source gets wrong or omits

| # | what | amendment | new maths? | where |
|---|---|---|---|---|
| D2 | `CORPropagationModuloCongruence` is stated, used five times, never proved | specialise `LEMPropagation` to the canonical surjection `π : A ↠ A/δ`; clauses (f), (t), (s), (m) are its (f), (ft), (fs), (fm) verbatim once `X/δ` is read as `π(X)` | no | R |
| D4 | `n = 2` for type `C` in case (c) of the stable-intersection theorem is unargued | reduce to a common algebra `D = ⋂Bᵢ`, `Eᵢ = Cᵢ ∩ D`; the diagonal of `Dⁿ` is `(E₁,…,Eₙ)`-essential, which Zhuk 2021 Lemma 6.11 forbids for `n ≥ 3` | no — a citation the later paper dropped, plus a reduction | R |
| D6 | `LEMConnectedProperties`(a) applies `LEMBridgeFromRelation` without its third hypothesis, which can fail | carry cruciality: a constraint crucial in a reduction satisfies the hypothesis at every pair of coordinates, else it is the conjunction of two strictly weaker projections | no | R |
| D7(i) | both endgames of Case 2 prove *connected* where (1c) demands *linked* | if `𝓘` were not linked it would witness the failure of its own irreducibility | no | R |
| D7(ii) | Case 1 derives (1c) relative to `D⁽²⁾`, the goal is `D⁽¹⁾` | take `𝓛 = 𝓚 ∧ 𝓘` and reweaken by `GetCrucialInstance`; every constraint of `𝓚` survives. Also state the induction as two-phase: `(2)_k ← (1)_{<k}`, `(1)_k ← (2)_k, (1)_{<k}` | no | R |
| D8 | the main induction needs *minimal* `ℳT`, the construction gives *minimal containing `s(x)`*; the bridging lemma was deleted | `M(b) = B ∩ ⋂_{σ∈Σ}[b]_σ` is the least `ℳT` set containing `b`, and `c ∈ M(b) ⟹ M(c) = M(b)`, so the two notions coincide | no | R |
| D11 | the symmetrisation at `StrongSubalgebras.tex:1154` reads `δ(x₁,x₂,x₅,x₅)`, which forces `x₁ = x₂`, so it is never a bridge | one character: `x₅ → x₆`. The source writes the correct formula at line 1365 | no | R |
| D12 | `LEMNiceBridgeGivesAbelianGroup` is **false**; `ℤ₃`, `δ = {x₁−x₂+x₃−x₄ = 0}` satisfies every hypothesis and no conclusion | add pair-reflexivity, which is exactly `φ = id` in the structure `δ = {φ(x₁−x₂) = x₃−x₄}`, and the broken step `δ ⊆ δ∘δ` becomes one line | no — the statement was wrong, not the mathematics | V, R |
| D13 | `LEMNontrivialReflexiveBridgeImplies` asserts linkedness of `proj_{1,2}(δ ∩ B⁴ ∩ σ*×σ*)` from an inclusion that bears on a different hypothesis | same pair-reflexivity, plus `σ* ⊆ proj_{1,2}(δ)` by minimality of `σ*` | no | R |
| D14 | Case 1 of `LEMPCCongruencePropertyInductiveStep` cites the **box** form of absorption-preserves-linkedness for a **subrelation** restriction | use the subrelation form: `W ≤_sd P×A` linked, `∅ ≠ W' ≤_T W` ⟹ `W'` linked. Proved from `LEMBACenterSImplyPPDefinition`, `LEMBACenterImplyIntersection`, `LEMBACenterSImplyFactor` and the elementary fact that `0_C` never absorbs `C²` | no | R |
| D15 | `LEMMainExistenceOfIrreducibleCongruence` factors the relation by `σ` where the argument needs `δ`, and the properness that step requires is unsupported | read `δ` for `σ` in the last four lines, and restore the "stable under `δ`" clause the source drops when unfolding irreducibility — that clause is exactly what makes the factored relation proper | no | V, R |
| D16 | `LEMLInearOnTheTopIsEasy` asserts "`ξ` is a bijective relation", which is the entire content of the lemma | abandon that route: `LEMNontrivialReflexiveBridgeImplies`(3) with `σ* = A²` gives `A/σ ≅ ℤ_p^m`, and irreducibility forces `m = 1` (the `m` coordinate congruences would exhibit `0_{A/σ}` as a proper intersection); C1 upgrades it to an isomorphism of algebras | no — and **one fewer external import** than the source's route | V, R |
| D17 | Case 1 of `LEMMaximalMultExtention` concludes that two sets meet from the fact that each meets a third | pass to a **minimal** subfamily `F` of the `C̄₁ʲ` cutting `B̄₂` out; minimality supplies `THMMainStableIntersection`'s leave-one-out hypothesis, and its conclusion admits only `BA, C, L, PC`, so no member of `F` is `S`-typed — the case evaporates instead of being contradicted | no | V, R |
| D3 | claimed citation cycle in §5 | **refuted** — 58 statements, 152 edges, acyclic | — | V |
| D10 (orig) | recursion-depth bound not established | **refuted** — the precondition is in the prose, discharged at the call site | — | V |
| D10 (now) | the arity `n^{n!}` in the special-WNU lemma | **moot** — state it as "there exist `N` and a special idempotent WNU of arity `N` in `Clo(w)`" | — | V |

**None of the fourteen confirmed defects needs new mathematics, and all fourteen are repaired.** Three needed a citation the
later paper dropped (D4, D14, C10), one was a typo (D11), one a false statement with a live
counterexample (D12), and the rest were omitted steps.

## 2. Conventions

All ten legislated in `C`. Two are not conventions: **C1** (`ℤ_p ∈ 𝒱ₙ` requires `p | n−1`) is
a theorem — specialness forces the affine coefficient `c` to satisfy `c² = c`, hence `c = 1`
— and **C10** is a missing lemma, resolved by Zhuk 2021 Lemma 3.4 plus "a WNU forbids an
essentially unary quotient of size ≥ 2". Six of the remaining eight (C2, C3, C4, C5, C8, C9)
are decided by internal evidence rather than taste; only C6 and C7 are free choices.

## 3. Statements our conventions force us to restate

| statement | why | restatement |
|---|---|---|
| `LEMCentralRelationImplies` (208) | true only because `∅` counts as central (C3), and the source drops Zhuk 2021's projective alternative (C10) | *`C = ∅`, or `C` is central in `A`, or `B` has a nontrivial BA subuniverse* — with the elimination of the projective case proved |
| `LEMLinkedImpliesBACenter` (222) | "there exists a BA or central subuniverse" is vacuous — every algebra is a BA subuniverse of itself | insert *proper nonempty*; that is how it is used at line 1282 |
| the `<_S` clause (`main.tex:1522`) | vacuously true for `D = ∅` | require `D` nonempty |
| `σ*` | typed as a congruence it collapses the linear/PC distinction (C2) | a reflexive symmetric subalgebra of `A²`; *that it is a congruence* is item (2) of the definition of linear and conclusion (1) of `LEMNontrivialReflexiveBridgeImplies` |
| `CORReverseHomomorphism` | its type list is `{BA,C,S,L,D}` where the stable-intersection theorem uses `{BA,C,S,L,PC}` | fix one convention; harmless, since `D` subsumes `L` and `PC` |

## 4. Steps used but not stated — the expansion work

Not defects. These are the places where the rendering must write out an argument the source
performs silently. Grouped by where they sit.

**§5.3, `LEMIntersectionPCLinearIsGood` and its corollary.**
1. Part (s), branch `𝒯_ℓ = D`: the text asserts a *proper* containment where the cited lemmas
   give `≤`. Split the case — equality gives the conclusion outright.
2. Subsubcases 2A1, 2B1: properness comes from the minimal choice of `m` (resp. `n`);
   nonemptiness from the constant tuples `(b/δ,…,b/δ)`.
3. Subsubcase 2B3: "the single block is `C_n/ω_n`" needs `B ∩ C ≠ ∅`.
4. **The full-fibre step**, at lines 545, 837, 921: *"since `proj_{1..|A|}(R') = (B/δ)^{|A|}`
   there exists `d` with `(B/δ)^{|A|} × {d} ⊆ R'`"* is a non sequitur as stated. It holds
   because `R'` is closed under coordinate substitution and `|B/δ| ≤ |A|`. **The arity `|A|`
   is load-bearing; a rendering that normalises it away breaks three proofs.**
5. Is minimality of the chains `k, ℓ` used? I found no use. Identify one or drop the
   hypothesis.
6. `CORIntersectionPCLinearIsGood` writes `δ = f^{-1}(σ)` with `f` undefined — read `f₁` — and
   admits "empty" where the lemma requires `B ∩ C ≠ ∅`.

**§5.4, first block.**
7. `δ̃` is reflexive, from `0_A ⊆ proj_{1,2}(δ) ⊆ δ̃`. Everything reflexive downstream needs it.
8. `proj_{1,2}(σ ∩ E⁴) = ω ∩ E²`, which is what makes Case 1's choice of `E` the right one.
9. That `E` exists: the transitive closure of `(ω ∪ ω^{-1}) ∩ D²` is a congruence on `D`, so
   its blocks are subuniverses. Maximality of `E` is never used.
10. The `WLOG` at line 1170 needs `σ̃` symmetric.
11. `{a} ∘ ω` is a subuniverse, because `{a}` is one by idempotence.
12. The appeal to `CORMainStableIntersection` at 1214 is correct but not in the corollary's
    shape: widen the three boxes to `{a}×A×C×B`, `{a}×C×C×A`, `{a}×C×A×B`, use `⋘` reflexive,
    and note that `n = 3` with all types `C` kills every alternative.
13. `C' ≤_C C` comes out of `LEMBACenterSImplyPPDefinition` as `≤_C A`; intersect with `C`.
    And the appeal to `proj_1(ξ) = A` should be to `{a} ∘ ω = A`.
14. Uniqueness and symmetry of `σ*`, both from minimality.

**§5.4, second block.**
15. Ternary absorption from centrality in Case 2 of `LEMPCCongruencePropertyInductiveStep`.
16. Case 3's use of `LEMAbsorbingEquality` needs the equality case treated separately.
17. `proj_{1,3}(δ)` is symmetric, from hypothesis (1) — this is what makes
    `{a} ∘ proj_{1,3}(δ) ≠ {a}` follow from linkedness.
18. `LEMPCBridgesAreTrivial` Case 1: the pigeonhole that turns uniqueness for `δ ∘ δ^{-1}`
    into uniqueness for `δ^{-1} ∘ δ`, and the elimination of two of the four combinations of
    `proj` conditions.
19. Its Case 2: hypothesis (3) for `ξ ∩ B⁴` may fail, and then the conclusion follows
    directly; the lemma cannot be *cited* on a non-bridge, so the case must be inlined.
20. The hedge at 1560, *"This case can be considered in the same way as Case 2."*

**§5.5.**
21. `LEMBridgeBetweenCongruences`: clause (4) is an equivalence and only one direction is
    proved; the converse is where the other half of `ω ∩ σ₁ = ω ∩ σ₂` is spent.
22. `LEMTwoStableIntersection`: properness of `C₁ ∩ B₂` in `B₁ ∩ B₂`; properness after
    factoring by `σ₂`; the "which block" upgrade; **the `D × D` case must apply (d) to
    `C₂`, not `B₂`** — against `B₂` it does not follow; the chain for `C₂ ⋘ A` must extend the
    chain for `B₂ ⋘ A` (convention C5); and `(c₁,c₂) ∈ ω ∖ σ₁`.
23. The missing mirror case `T₁ = D`, `T₂ ∈ {BA,C}`.

**Elsewhere.**
24. The four hedges: the `BA` case at line 146; that Zhuk 2021 Lemma 6.24's proof really does
    transfer from `BA` to `S` (line 177); the case at 1560; "the inclusion `⊆` is obvious" at
    2428.
25. `LEMPreserveLinkdness`: the four-line proof unpacks to a two-phase argument that should be
    written out.
26. Zhuk 2021 Lemma 6.11, needed for D4, has a printed proof that cites *itself* three times
    where it means the preceding lemma. Our rendering must supply both.

## 5. What is open

Three different kinds of thing, and only the second is a live mathematical question.

### (a) Not read

**§5 is now read in full** — all 44 proofs across all seven subsections. What remains unread is
outside §5: `main.tex`'s CSP half (instances, coverings, cruciality, the main induction, the
algorithm) has been read only where D6, D7 and D8 touch it, and §4 (`XYSymmetric.tex`, 1 640
lines) is out of scope by decision, with D10 declared moot.

### (b) Read, and unresolved

Nothing. D16 and D17 are settled. One small item remains: **does `LEMIntersectionPCLinearIsGood` use the minimality of its
chains `k, ℓ`?** The proof fixes minimal chains for `B ⋘ A` and `C ⋘ A` and I could not find a
step that consumes minimality; a shorter chain would only make the induction measure smaller.
Either identify the use or drop the hypothesis. Nothing depends on the answer for
correctness — a redundant hypothesis costs only bookkeeping — but a formalization has to
decide.

The hedge *"the inclusion `⊆` is obvious"* (line 2428) sits inside §5.7 and belongs to (a).

### (c) External imports a self-contained rendering must absorb

Not defects; scope. In descending order of weight:

- **Brady, *Notes on CSPs and Polymorphisms* (arXiv, 2022), Theorem 3.11.1** — *a proper
  linked subdirect relation forces a BA or central subuniverse on one side.* Imported as
  `LEMLinkedImpliesBACenter` and used at `StrongSubalgebras.tex:1282` and inside
  `LEMBAConLeftOrCenterOnRight`, hence throughout §5.4. This is essentially the Absorption
  Theorem and is the single heaviest thing §5 takes on faith. Sections 3.11.2, 3.11.3 and
  3.15 of the same notes are also cited.
- **Zhuk 2021 (arXiv:2005.00593)** — the strong-subalgebra calculus: Lemmas 3.1, 3.2, 3.4,
  6.1, 6.8, 6.9, 6.11, 6.24, 6.25, Corollary 6.11.1, Theorem 6.15. Two of these are load
  bearing for our own repairs (6.11 for D4, 3.4 + 6.15 for C10) and have been read verbatim.
- **Zhuk 2017 (arXiv:1704.01914)** Theorem 8.15 (strongly rich relations come from abelian
  groups) and Lemma 8.16, themselves cited onward to a further paper.
- **Barto–Kazda**, *Deciding Absorption*, Lemma 2.9 and Proposition 2.14; **Barto–Kozik**,
  Proposition 2.15(i); **Hobby–McKenzie** for Abelian ⟺ affine under a WNU;
  **Maróti–McKenzie** for the WNU arity.

So the honest distance to self-containedness is roughly fifteen imported statements, of which
Brady 3.11.1 and Zhuk 2021 Theorem 6.15 are the two that are real work.

## 6. Risk register

- **Least-tested repairs.** D7(ii)'s reweakening and D6's cruciality corollary each touch the
  CSP-instance machinery rather than the algebra, and each has been checked against only the
  call site that motivated it.
- **Least-tested positive verdicts.** `LEMSelfIntersectionPC` was read only where the
  `LEMCentralRelationImplies` call sites forced it open, and §5.3's three small lemmas were
  never opened at all — yet `LEMTotallySymmetricRelationForIrreducible` is what splits the
  main case of `LEMIntersectionPCLinearIsGood`, the largest proof in §5.
- **Best-tested claims.** Everything reducible to a finite check has had one: D6's witness in
  `ℤ₄ × ℤ₂ × ℤ₄`, D12's counterexample in `ℤ₃`, D14's Lemma B over ~100 000 pairs, C1 over
  `p ∈ {2,3,5,7}`, the acyclicity of 152 proof-dependency edges, and the statement audit over
  all 81 labelled statements. Two of the original claims died to exactly such checks.
