# Verification notes

Working notes, not a publication. For each claimed issue in Zhuk arXiv:2404.01080v2: what is
actually true, checked against the source, and what our rendering must therefore do.

**Standard.** A claim counts as verified only when the cited lines *and the prose around them*
have been read, and the passage that does or does not discharge it can be quoted. The
original D10 failed exactly here: the reader took the pseudocode's `Input:` line as the
specification while the hypothesis was in the paragraph above it.

Line numbers are into `main.tex` / `StrongSubalgebras.tex` of the v2 arXiv source.

---

## Confirmed

### D2 — `CORPropagationModuloCongruence` is never proved. **CONFIRMED**

Stated at `main.tex:1682`. Used five times: `StrongSubalgebras.tex:2506, 2514, 2588, 3110`
and `main.tex:2999`. Never proved, and not attributed to any external source.

The paper's own convention (`main.tex:1058`) is *"we always duplicate statements if the proof
appears in a later section"*, implemented by `\newtheorem*{XXXLEM}` duplicates. Checking all
thirteen statements of §2.3 against that convention:

| restated in §5 | not restated |
|---|---|
| Ubiquity, Propagation, PropagateFromFactor, PropagateMultiplyByCongruence, PropagateToRelations, IntersectALL, MainStableIntersection, CORMainStableIntersection, MultiTypeStillStable, PreserveLinkdness, MaximalMultExtention | **CORPropagationModuloCongruence**, `LEMBACenterImplies` |

`LEMBACenterImplies` is declared as an external import (`\cite{zhuk2021strong}`), so its
absence is by design. `CORPropagationModuloCongruence` is the sole genuine omission.

*Our rendering:* prove it. It is Propagation specialised to the canonical surjection
`A ↠ A/δ`; the only care needed is matching clause (m)'s "`B/δ` is S-free" against (fm)'s
"`f(B)` is S-free".

### D4 — `n = 2` in case (c) of the stable-intersection theorem is unargued. **CONFIRMED**

Proof at `StrongSubalgebras.tex:2594+`. It reduces the general `n` to a pair by setting
`B₂' = B₂ ∩ C₃ ∩ … ∩ Cₙ`, obtains `T₁ = T₂` from `LEMTwoStableIntersection` +
`LEMNoBridgeBetweenDifferentTypes`, and then:

> *"If `T₁ = PC` then `σ₁∘σ₂ = σ₁ = σ₂` … Additionally, this implies that `n` cannot be
> greater than 2 for `T₁ = PC`, as in this case the intersection `C₁ ∩ C₂` must be empty."*

That argument is specific to PC: equal congruences make `C₁` and `C₂` distinct blocks, so
they are *pairwise* disjoint, which contradicts hypothesis (3) once `n ≥ 3`. For type `C`
there is no congruence and no analogue, and the proof offers nothing. Hypothesis (2) gives
only `C₁ ∩ … ∩ Cₙ = ∅`, never `C₁ ∩ C₂ = ∅`.

*Our rendering:* either prove `n = 2` for type `C` (some Helly-type property of central
subuniverses would do it), or weaken the conclusion and check the call sites. **Open —
decide before §6 is written.**

### D8 — the minimality step in Case 2 of the main induction. **CONFIRMED, description corrected**

I had written that `LEMMinimalContainingIsMinimal` "is commented out … yet is genuinely used
at `main.tex:3527`". The citation at 3527 is *also* commented out. The accurate statement is
that the step is asserted with no justification at all, and the lemma that would justify it
has been removed:

```
3526  For every variable x choose the minimal D^(2)_x ≤_{MT} D^(1) containing s(x).
3527  %By Lemma \ref{LEMMinimalContainingIsMinimal}
3528  %$D^{(2)}_{x}$ is a minimal \mathcal{M}T subuniverse.
3529  By Lemma \ref{LEMMultiTypeStillStable}
```

This matters because `LEMMinimalPCLinearReductionIsConsistent`, invoked two lines later, has
as hypothesis (5) that `D^(2)_x` is *a minimal ℳT subuniverse* — minimal outright. What line
3526 constructs is minimal *among ℳT subuniverses containing `s(x)`*. Those are not the same
condition, and the bridge between them is what was deleted.

The deleted statement (`main.tex:1864`) was: if `C` is inclusion-minimal with `b ∈ C` and
`C ≤_{ℳT} B`, then no `C' ⊊ C` has `C' ≤_{ℳT} B`.

*Our rendering:* prove that, or restructure to need only minimal-containing-a-point. Note it
is not obviously true — a proper ℳT subset avoiding `b` does not contradict minimality among
sets containing `b` — so check it before relying on it.

---

## Refuted

### D3 — the claimed citation cycle in §5. **REFUTED**

The claim was a cycle `Lemma 9 ⇒ 7 ⇒ 86 ⇒ 85 ⇒ Cor 22 ⇒ Thm 21 ⇒ Lemma 8 ⇒ Lemma 9`, closed
at `StrongSubalgebras.tex:1214`.

Checked mechanically: parsed every `\begin{proof}` in `main.tex`, `StrongSubalgebras.tex` and
`necessaryClaims.tex`, attributed it to its statement (including the `XXXLEM` duplicates), and
extracted its `\ref`s. **58 statements with proofs, 152 edges, no cycles.**

The named edge is real: `LEMBlockOfGoodBridgeDoesNotHaveBAC` (stated at line 1144) does invoke
`CORMainStableIntersection` at line 1214, in its `T = C` case. But it closes nothing.
`CORMainStableIntersection`'s transitive proof-closure is 25 statements and does not contain
`LEMBlockOfGoodBridgeDoesNotHaveBAC`; its direct dependencies are `LEMPropagation` and
`THMMainStableIntersection`, and the latter's closure is 15 statements, also disjoint from it.

*Our rendering:* nothing to do. §5 can be written in dependency order.

### D10 (original) — the recursion-depth bound. **REFUTED** (see `ch10-defects.tex`)

Retracted earlier. The precondition is in the prose at `1704.01914:892`, discharged at the
call site at `:635`, and the propagation argument is at `:1070`. The one genuinely missing
step is now Lemma 10.1 of the blueprint, proved.

---

## Moot

### D10 (current) — the arity `n^{n!}` in the special-WNU lemma

The concern is that the period of `y ↦ w(x,…,x,y)` need not divide `n!`. Note the suggested
counterexample (`n = 3`, a 5-cycle) does not work: idempotence forces `w(x,x,x) = x`, so `x`
is a fixed point of that map and a full 5-cycle on five elements is impossible. Cycles of
length up to `|A| − 1` remain possible, and `|A| − 1` need not divide `n!` when `|A| > n`.
Unresolved, and I do not have Maróti–McKenzie to check the actual statement.

*Our rendering:* moot. State it as *"there exist `N` and a special idempotent WNU of arity
`N` in `Clo(w)`"*, which is all the dichotomy proof consumes. The precise arity matters only
for §4 of the source, which is out of scope.

---

## Not yet checked

- **C1–C9** — the convention list. Cheaper: these are readings to legislate, not claims to
  falsify, so the failure mode is different. (C10 is settled below.)

---

## Running tally

Five claims checked in full. **Three confirmed** (D2, D4, D8 — one with its description
corrected), **two refuted** (D3, and the original D10). Both refutations came from readers
who worked from a formal-looking artifact — pseudocode in one case, a citation in the other —
without the surrounding text or, in D3's case, without checking that the cycle closed.

Neither refuted claim would have survived ten minutes of mechanical checking. That is the
argument for doing this pass before writing a line of the rendering.

---

# Adversarial reading of §5 — first pass

§5 is 3 144 lines, 44 statements with proofs, 152 proof-dependency edges. This records a
first pass: mechanical triage over the whole section, then close reading of the highest-risk
proofs. It is **not** a complete adversarial reading — see "what remains" below.

## Mechanical results over the whole section

**The dependency graph is acyclic** (already established in refuting D3). So §5 can be
written in dependency order, and there is no hidden simultaneous induction to untangle.

**Four hedges, total**, in thirteen printed pages:

| line | text | in | obligation |
|---|---|---|---|
| 146 | "For `T = BA` it is straightforward" | `LEMBACenterSImplyFactor` | supply the BA case |
| 177 | "For `T = S` just repeat the same proof **word to word** replacing BA by S" | `LEMBACenterSOnPowerImplies` | check that Zhuk 2021 Lem 6.24's proof really does transfer from BA to S |
| 1560 | "This case can be considered in the same way as Case 2" | the lemma preceding `LEMNoBridgeBetweenDifferentTypes` | write the case out |
| 2428 | "The inclusion `⊆` is obvious" | `LEMFactorByDelta` region | one line, but write it |

That is an unusually low density — for comparison the same regex over Brady's notes fires
many times per page. It is consistent with the impression that 2404 is careful prose, and it
means the rendering's job in §5 is mostly *expansion*, not repair.

## Closely read, and clean

**`LEMPreserveLinkdness` and its chain.** Flagged in the original survey on the grounds that
the workhorse `LEMPreserveLinkdnessOneStepAUX` assumes both `R ∩ (B₁×C₂) ≠ ∅` and
`R ∩ (C₁×B₂) ≠ ∅`, while the target lemma assumes only `R ∩ (B₁×B₂) ≠ ∅`. **Not a defect** —
the flag conflates AUX with `LEMPreserveLinkdnessOneStep`, which is what the four-line proof
actually invokes, and which needs only `R ∩ (B₁×B₂) ≠ ∅` and `S ∩ (C₁×B₂) ≠ ∅`.

The four-line proof is correct, and unpacks to a two-phase argument our rendering should
write out. Decompose both multi-type reductions into chains by `LEMMultiTypeStillStable`.
*Phase 1*: shrink coordinate 1 along its chain with `B₂` fixed; at each step the needed
`R ∩ (B₁⁽ʲ⁾ × B₂) ≠ ∅` is the previous step's conclusion, and the needed
`S ∩ (B₁⁽ʲ⁺¹⁾ × B₂) ≠ ∅` follows from `S ∩ (C₁×C₂) ≠ ∅` by monotonicity, since
`C₁ ⊆ B₁⁽ʲ⁺¹⁾` and `C₂ ⊆ B₂`. This yields `R ∩ (C₁ × B₂) ≠ ∅`. *Phase 2*: the same on the
transpose `R⁻¹`, whose rectangular closure is `S⁻¹`, shrinking coordinate 2 with `C₁` fixed —
legitimate because `C₁ ⋘ A₁`, by `LEMMultiTypeStillStable` plus transitivity of `⋘`.

I also checked that `OneStep`'s own proof discharges AUX's two mixed hypotheses. It does, both
by monotonicity: `R ∩ (B₁ × C₂') ⊇ R ∩ (B₁ × B₂) ≠ ∅` since `B₂ ⊆ C₂'`, and
`R ∩ (C₁ × B₂') ≠ ∅` by construction. The `C₂', B₂'` themselves exist by walking the ⋘-chain
from `A₂` down to `B₂` and taking the first place `R ∩ (C₁ × ·)` becomes empty, the top being
nonempty by subdirectness.

**`CORReverseHomomorphism`.** Clean. The projection `f₁ : R → A₁` is surjective by
subdirectness — used silently — and `f₁⁻¹(C₁) = R ∩ (C₁ × A₂ × ⋯ × Aₙ)`. Note its type list is
`{BA, C, S, L, D}` where the stable-intersection theorem uses `{BA, C, S, L, PC}`; harmless,
since `D` subsumes `L` and `PC`, but the rendering should fix one convention.

**`LemAbsorptionImpliesEssential`.** Not a proof at all — it is the Barto–Kazda criterion,
cited to *Deciding Absorption* Prop 2.14 and Zhuk 2021 Lem 3.2. My triage flagged it only
because the parser attached the *following* lemma's proof to it.

## What remains

The pass above touched roughly a dozen of the 44 proofs and read perhaps six adversarially.
The outstanding item is **`LEMIntersectionPCLinearIsGood`** (line 623): a 292-line proof with
20 distinct citations, by a wide margin the largest and most connected in §5, and the one that
`LEMTwoStableIntersection` leans on in its S-type and mixed-type cases. Nothing in the
mechanical triage suggests it is wrong, but nothing has checked it either. It should be read
in one sitting, with its citations' hypotheses discharged one at a time.

Also outstanding: §5.4 (`SUBSECTIONIrreduciblePCOrLinear`, lines 1022–1736) and §5.5 (types
interaction, 1736–1928), neither of which has been opened.

## `LEMIntersectionPCLinearIsGood` — read in full

The largest proof in §5 (line 623, 292 lines, 20 citations). **Structurally sound.** No
defect. Four items for the rendering, one of them a genuine missing case.

**Shape.** Fix minimal chains `B = B_k < ⋯ < B_0 = A` and `C = C_ℓ < ⋯ < C_0 = A`, put
`σ = ⋂σᵢ`, `ω = ⋂ωᵢ`, and induct on `k + ℓ`, proving (s) then (d). Part (d) introduces
`S ≤ (A/δ)^{|A|}`, the tuples pairwise related by `σ ∩ ω`; a total-symmetry lemma splits into
`S` = diagonal (giving `|(B∩C)/δ| = 1` and the "moreover" clause) or `(B/δ)^{|A|} ⊆ S`. In the
latter, `S_{m,n}` refines `S` by `aᵢ ∈ B_m ∩ C_n`, and one takes the least `m` (2A) or `n` (2B)
where containment fails, contradicting the dividing hypothesis in each of three type cases;
2C is the surviving case and gives `(B∩C)/δ = B/δ`.

I checked every appeal to the inductive hypothesis lands at strictly smaller `k + ℓ`: (s) uses
(s) and (d) at `k + (ℓ−1)`; 2B2 uses (s) at `(n−1) + k`; 2B3 uses (d) at `(n−1) + k`; and
`n ≤ ℓ` throughout. So the induction is sound — worth confirming, since a commented-out block
shows an earlier draft inducted lexicographically on `(|A/(σ∩ω)|, k+ℓ)` and the live proof
dropped the first component.

### The one real gap: part (s), the `𝒯_ℓ = D` branch

The text reads: *"In the second case `(G ∩ C_{ℓ−1})/ω_ℓ <_{BA,C} C_{ℓ−1}/ω_ℓ`, which
contradicts the definition of a divisible congruence."* The `<` is **proper**, but what the
cited lemmas supply is `≤` — `LEMBACenterImplyIntersection` gives `≤_T`, and factoring
preserves that. If the containment is an equality there is no contradiction, and the case is
not treated.

It is not a defect in the lemma, because the equality case gives the conclusion outright:
if `(G ∩ C_{ℓ−1})/ω_ℓ = C_{ℓ−1}/ω_ℓ` then every `ω_ℓ`-block meeting `C_{ℓ−1}` meets
`G ∩ C_{ℓ−1}`, in particular the block `E` with `C_ℓ = C_{ℓ−1} ∩ E`, so `G ∩ C_ℓ ≠ ∅` — which
is exactly what was to be proved. *Our rendering:* split the case rather than assert `<`.

### Three steps that are available but unstated

- **Properness from minimality.** 2A1 and 2B1 assert `S_{m,0} ∩ (B/δ)^{|A|} <_{T_m}
  (B/δ)^{|A|}` where the cited lemmas give `≤`. Properness is immediate from the minimal
  choice of `m` (resp. `n`); nonemptiness needs the observation that the constant tuples
  `(b/δ,…,b/δ)` for `b ∈ B` lie in `S_{m,0}`, since `B ⊆ B_m` and `(b,b) ∈ σ ∩ ω`.
- **2B3, the first alternative.** Part (d) offers "size 1 or all of `C_{ℓ−1}/ω_n`", but the
  text writes the first as "`= C_n/ω_n`", which is stronger: it fixes *which* block. Correct,
  but because `B ∩ C ≠ ∅` and `C ⊆ C_n` force `B_k ∩ C_n ≠ ∅`, so the single block is the one
  defining `C_n`. Then `B_k ∩ C_{n−1} ⊆ C_n` and `S_{k,n−1}` and `S_{k,n}` cut `(B/δ)^{|A|}`
  identically, contradicting minimality of `n`. Write the two steps out.
- **Is minimality of `k, ℓ` used?** The proof fixes minimal chains but I did not find a use.
  If a shorter chain existed for `C_{ℓ−1}` the measure would only be smaller and the induction
  still applies. Either identify the use or drop the hypothesis.

### One inherited dependency

2A3 and 2B3 both finish through `LEMCentralRelationImplies`, converting `R'` viewed as a
binary relation with a centre into a BA subuniverse on `B/δ` or a centre on the other factor.
This is the statement flagged as convention item C10, which appears to drop a third
alternative — a nontrivial *projective* subuniverse — present in Zhuk 2021 Thm 6.15. It is
used twice in the largest proof of §5, so C10 is not cosmetic and should be resolved before
this lemma is rendered.

Minor: the following `CORIntersectionPCLinearIsGood` writes `δ = f^{-1}(σ)` with `f`
undefined; read `f₁`. Its conclusion admits "empty" while the lemma requires `B ∩ C ≠ ∅`, so
the empty case needs its own line.

---

# C10 — `LEMCentralRelationImplies` and the dropped third case. **SETTLED**

The question was blocking: the source states `\cite{zhuk2021strong}, Theorem 6.15` with two
alternatives where the original has three, and the statement is used inside §5's largest
proof. Answer: **the third case is eliminable, the two-case statement is true, and the
elimination is an argument Zhuk himself runs elsewhere in the predecessor without ever
connecting it to Theorem 6.15.** Two further items surfaced from reading the call sites.

## The two statements, side by side

`StrongSubalgebras.tex:208`:

> Suppose `R ≤_sd A × B`, `C = {c ∈ A | ∀b ∈ B: (c,b) ∈ R}`. Then one of the following holds:
> (1) `C` is a central subuniverse of `A`; (2) `B` has a nontrivial binary absorbing
> subuniverse.

arXiv:2005.00593, Theorem 6.15 (p. 38), verbatim except for a third item:

> 3. `B` has a nontrivial projective subuniverse.

The word *projective* does not occur anywhere in the 2404 source — `grep -i projective` over
`main.tex`, `StrongSubalgebras.tex`, `necessaryClaims.tex`, `XYSymmetric.tex` returns nothing.
So the notion was removed from the paper, not merely from this one citation.

## Why case 3 collapses

The standing hypothesis is at `main.tex:1123`, *"In this paper we assume that every algebra is
a finite idempotent algebra having a WNU term operation"*, restated at the head of §2.3
(`main.tex:1641`) precisely for the statements §5 proves: *"Recall that all the algebras in
the following statements are assumed finite idempotent algebras having a WNU term operation
(Taylor)."* So the `B` of the lemma is Taylor.

The predecessor supplies exactly the needed step, as Lemma 3.4 (2005.00593, p. 8, proved
p. 44):

> Suppose `B` is a nontrivial projective subuniverse of a finite idempotent algebra `A`, and
> `B` is not a binary absorbing subuniverse. Then there exists an essentially unary algebra
> `U ∈ HS(A)` of size at least 2.

and an essentially unary `U ∈ HS(·)` of size ≥ 2 is exactly what a WNU forbids — this is
Theorem 4.14 (1) ⇔ (3) of the same paper, and it also has a two-line direct proof. So case 3
implies case 2 or a contradiction. **The two-case statement is a true statement about Taylor
algebras.** Proof written out in `NOTES-repairs.md`.

That Zhuk knows this is visible in the proof of his own Theorem 4.15, step (4) ⇒ (5):

> *"In case (5) Lemma 3.4 gives us a nontrivial binary absorbing subuniverse, which is a
> strong subuniverse, or an essentially unary algebra `U ∈ HS(A)`, which contradicts condition
> (4)."*

Same move, on the same case of the same trichotomy. It is simply never applied to
Theorem 6.15, so the two-case form in 2404 arrives with no derivation.

*Our rendering:* legitimate, and it should be stated as a lemma with a proof rather than
smuggled into a citation. C10 is **not** blocking any more.

## But the two-case form is true only because `∅` counts as central

Read against `main.tex`'s own definition (`main.tex:1345–1352`), a subuniverse `C` is central
if it is absorbing and `(a,a) ∉ Sg((\{a\}×C) ∪ (C×\{a\}))` for every `a ∈ A∖C`. Both clauses
are vacuous for `C = ∅`, so `∅` is central. It has to be, or the theorem is false: take
`A = B = ℤ_p` and `R` the graph of `x ↦ x+1`. `R ≤_sd ℤ_p × ℤ_p`, `C = ∅`, and `ℤ_p` has no
nontrivial BA subuniverse at all (`main.tex:3484`). Alternative (2) fails, so alternative (1)
must be holding vacuously.

This is convention item **C3** biting a specific statement. Our rendering forbids empty
subuniverses (`conv:empty`), so it cannot state the lemma as Zhuk does. It must read:

> `C = ∅`, or `C` is a central subuniverse of `A`, or `B` has a nontrivial binary absorbing
> subuniverse.

Harmless at every call site, because each site exhibits an element of `C` before applying the
lemma — see below — but a formalization that copies the two-case form and forbids `∅` proves
a false statement.

## The call sites: nine, not two, and each needs two unstated steps

`StrongSubalgebras.tex:268, 551, 606, 843, 928, 1008, 2024, 2079` (the ninth is the statement
itself). Eight of them run the lemma contrapositively against a *BA and center free* algebra —
defined at `main.tex:1363` as *"no proper nonempty binary absorbing subuniverse or proper
nonempty central subuniverse"*. Two obligations are therefore live at each site and are
discharged at none of them explicitly.

**(a) Properness of the center.** *Nonempty* central is not enough; the definition of BA and
center free only forbids *proper* nonempty ones, so `C` must be shown `≠ A`. Available at
every site, and in three of them the witness is even printed two lines earlier —
`(B_{k-1}/σ_k)^{|A|} × B_n/σ_n ⊄ R'` at line 533, `(B/δ)^{|A|} × B_m/σ_m ⊄ R'` at 824,
`(B/δ)^{|A|} × C_n/ω_n ⊄ R'` at 903 — but it is never connected to the appeal. Sites 606,
1008 and 2079 instead *use* the improper case, concluding that `R` is full; there the split
is explicit.

**(b) The power-to-base step.** Alternative (2) yields a BA subuniverse of a *power*, e.g. of
`(B/δ)^{|A|}`; the sites assert "a BA subuniverse on `B/δ`". That is
`LEMBACenterSOnPowerImplies`, cited at 2024 (*"Combining Lemmas … and
\ref{LEMBACenterSOnPowerImplies}"*) and omitted at 551, 843 and 928.

## A separate gap found in the same three proofs: the full fibre

Subsubcases 1B3 (line 545), 2A3 (line 837) and 2B3 (line 921) each contain, verbatim modulo
names:

> *"Since `proj_{1,2,…,|A|}(R') = (B/δ)^{|A|}`, there exists `d ∈ B_{m-1}/σ_m` such that
> `(B/δ)^{|A|} × {d} ⊆ R'`."*

**Surjectivity of a projection does not produce a full fibre**, and as stated this is a non
sequitur. It is nevertheless true, and the reason is the one that explains why the arity is
`|A|` and not something smaller: `R'` is totally symmetric in its first `|A|` coordinates and
closed under identifying them, because its definition is a conjunction of unary and binary
conditions on the entries; and `|B/δ| ≤ |A|`, so the tuple enumerating `B/δ` with repetition
already lies in `(B/δ)^{|A|}`, and every other tuple is a coordinate-substitution instance of
it with the same `d`. Written out in `NOTES-repairs.md`.

That the constant `|A|` is load-bearing is worth flagging on its own: a reader who normalises
the arity away breaks these three proofs.

## Tally

C10 resolves in the affirmative but is not a one-line legislation. It costs one imported
lemma with a proof (the elimination), one restatement (the `∅` alternative), two discharge
obligations per call site, and one genuinely missing three-line argument repeated at three
sites.
