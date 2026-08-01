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

---

# Adversarial reading of §5.4 — `SUBSECTIONIrreduciblePCOrLinear`

`StrongSubalgebras.tex:1022–1735`. Five statements with proofs, of which two are imported from
Hobby–McKenzie. Read line by line against the definitions in `main.tex:1185–1400`. This first
instalment covers `LemBridgeEquivalentToAbelianness` (1082), `LEMNiceBridgeGivesAbelianGroup`
(1103), `LEMBlockOfGoodBridgeDoesNotHaveBAC` (1144), `LEMNontrivialReflexiveBridgeImplies`
(1247) and `LEMLinearEquivalentConditions` (1346). `LEMPCCongruencePropertyInductiveStep`
(1372–1735) is separate.

**Three defects, and they are one defect.** All three are cured by a single missing property
of the bridge, which the one place that actually calls this chain supplies for free.

## D11 — the symmetrisation formula at line 1154 is degenerate as written. **CONFIRMED**

`LEMBlockOfGoodBridgeDoesNotHaveBAC` opens by symmetrising `δ`:

```
1154  \sigma(x_1,x_2,x_3,x_4) = \exists x_5 \exists x_6\;
1155  \delta(x_1,x_2,x_5,x_5)
1157  \wedge \delta(x_3,x_4,x_5,x_6).
```

Clause (4) of the definition of a bridge (`main.tex:1258`) is *"`(a₁,a₂,a₃,a₄) ∈ δ` implies
`(a₁,a₂) ∈ σ₁ ⟺ (a₃,a₄) ∈ σ₂`"*. The first conjunct has `x₅` in both of the last two places,
so `(x₅,x₅) ∈ 0_A` forces `(x₁,x₂) ∈ 0_A`, i.e. `x₁ = x₂`. Hence `proj_{1,2}(σ) ⊆ 0_A`, and
clause (3) demands `proj_{1,2}(σ) ⊋ σ₁ = 0_A`. **The relation defined is never a bridge**, for
any `σ₁`, and every later line of the proof — `(a,b,a,b) ∈ σ`, `ω = proj_{1,2}(σ)` linked —
is false of it.

It is a one-character typo. The intended relation is `δ ∘ δ^{-1}`,

  `σ(x₁,x₂,x₃,x₄) = ∃x₅∃x₆ δ(x₁,x₂,x₅,x₆) ∧ δ(x₃,x₄,x₅,x₆)`,

and the source writes exactly that, correctly, 210 lines later at `1365–1367`, in the proof of
`LEMLinearEquivalentConditions`, for the same purpose.

## D12 — `LEMNiceBridgeGivesAbelianGroup` is false as stated. **CONFIRMED, machine-checked**

Statement (line 1103): `σ` a congruence on `A`, `δ` a bridge from `σ` to `σ` with
`proj_{1,2}(δ) = δ̃ = A²` and `δ(x₁,x₂,x₃,x₄) = δ(x₃,x₄,x₁,x₂)`. Conclusion: there is an
abelian group `G` with `(A/σ; δ/σ) ≅ (G; x₁−x₂ = x₃−x₄)`.

**Counterexample.** `A = ℤ₃` with `w(x₁,…,x₄) = x₁+x₂+x₃+x₄ (mod 3)` — idempotent since
`4 ≡ 1`, and a special WNU, so `A ∈ 𝒱₄`. Take `σ = 0_A` and

  `δ = {(x₁,x₂,x₃,x₄) ∈ ℤ₃⁴ : x₁ − x₂ + x₃ − x₄ = 0}`.

Verified by exhaustion: `δ` is a subuniverse of `A⁴`; clause (4) holds; `proj_{1,2}(δ) = A²`;
`δ̃ = A²`; `δ` is symmetric; and **none of the six bijections `ℤ₃ → ℤ₃` carries `δ` to
`{x₁−x₂ = x₃−x₄}`**. Since every abelian group of order 3 is `ℤ₃`, no `G` works.

**What is true.** Factor out the diagonal: `δ` contains all `(a,a,b,b)`, so it is the preimage
of some `K ≤ G × G` under `(x₁,x₂,x₃,x₄) ↦ (x₁−x₂, x₃−x₄)`. Clause (4) makes `K` meet
`G × 0` and `0 × G` only at the origin, and subdirectness makes it a graph, so
`K = {(u, φ(u))}` for an automorphism `φ`, i.e.

  `δ = {(x₁,x₂,x₃,x₄) : φ(x₁−x₂) = x₃−x₄}`,

and the symmetry hypothesis says exactly `φ² = id`. Zhuk's conclusion is the case `φ = id`;
the counterexample is `φ = −id`, which is why it needs `p` odd.

Where the proof breaks: *"Composing the bridge `δ` with itself we get a bridge `δ₀ ⊇ δ`."*
`δ ∘ δ = {φ²(x₁−x₂) = x₃−x₄} = {x₁−x₂ = x₃−x₄}`, which for `φ = −id` does **not** contain `δ`.
The closing line *"It remains to show that `δ = δ₀`"* counts `|δ| = |δ₀| = |A|³` and needs the
containment it does not have.

## D13 — `LEMNontrivialReflexiveBridgeImplies`: linkedness is asserted, not shown. **CONFIRMED**

Line 1273 puts `δ' = δ ∩ B⁴ ∩ (σ* × σ*)` for `B` a block of `LeftLinked(σ*)` and says
*"Since `δ̃ ⊇ σ*`, `δ'` satisfies all the conditions of Lemma
\ref{LEMBlockOfGoodBridgeDoesNotHaveBAC}"*. Two of those conditions are that
`proj_{1,2}(δ')` properly contains `0_B` and is **linked**. What `δ̃ ⊇ σ*` gives is the third
condition, `proj_{1,2}(δ') ⊆ δ̃'`. Nothing offered bears on linkedness.

It does not follow. `proj_{1,2}(δ') = {(x₁,x₂) ∈ σ*∩B² : ∃(x₃,x₄) ∈ σ*∩B², δ(x₁,x₂,x₃,x₄)}`,
and the witness `(x₃,x₄)` supplied by minimality of `σ*` lies in `σ*` but in no particular
block. If it lands outside `B` for every choice, `proj_{1,2}(δ')` collapses to `0_B` and `δ'`
is not even a bridge.

The same gap recurs at line 1290, where `LEMNiceBridgeGivesAbelianGroup` is applied to
`δ ∩ B⁴` and needs `proj_{1,2}(δ ∩ B⁴) = B²`.

## The single cure

Call a bridge `δ` **pair-reflexive** if `(x₁,x₂) ∈ proj_{1,2}(δ)` implies `δ(x₁,x₂,x₁,x₂)`.

- D13 dies: `σ* ⊆ proj_{1,2}(δ)` by minimality of `σ*` (proof in `NOTES-repairs.md`), so
  pair-reflexivity puts `(x₁,x₂,x₁,x₂)` in `δ'` for every `(x₁,x₂) ∈ σ*∩B²`, giving
  `proj_{1,2}(δ') = σ*∩B²` exactly — which is linked precisely because `B` is a block of
  `LeftLinked(σ*)`. Same for `proj_{1,2}(δ ∩ B⁴) = B²`.
- D12 dies: pair-reflexivity is `φ = id`, and it also repairs the proof directly —
  `δ ⊆ δ∘δ` by taking `(y₁,y₂) = (x₁,x₂)`.
- D11 dies: `δ ∘ δ^{-1}` is pair-reflexive, so the corrected formula delivers what
  `LEMBlockOfGoodBridgeDoesNotHaveBAC` needs.

And it costs nothing. `LEMNontrivialReflexiveBridgeImplies` is invoked exactly once in the
whole paper, at line 1368, and the object it is invoked on is
`δ'(x₁,x₂,x₃,x₄) = ∃x₅∃x₆ δ(x₁,x₂,x₅,x₆) ∧ δ(x₃,x₄,x₅,x₆)` — pair-reflexive by construction.
`LEMNiceBridgeGivesAbelianGroup` is likewise invoked exactly once, from inside that call.

*Our rendering:* add pair-reflexivity to the hypotheses of
`LEMNiceBridgeGivesAbelianGroup` and `LEMNontrivialReflexiveBridgeImplies`, and fix the
formula in `LEMBlockOfGoodBridgeDoesNotHaveBAC`. Nothing downstream moves.

## Clean, with steps to write out

`LEMBlockOfGoodBridgeDoesNotHaveBAC` is otherwise **sound** — I checked it in full, both
cases, including the `T = BA` and `T = C` splits. Five steps are used without being stated:

1. `δ̃` is reflexive, because `0_A ⊆ proj_{1,2}(δ) ⊆ δ̃` — the first inclusion is clause (3) of
   the bridge definition. Everything reflexive downstream comes from this.
2. `proj_{1,2}(σ ∩ E⁴) = ω ∩ E²` for any subuniverse `E`, which is what makes the choice of
   `E` in Case 1 the right one. It needs `σ(x₁,x₂,x₁,x₂)` for `(x₁,x₂) ∈ ω` — pair-reflexivity
   again, from the corrected symmetrisation.
3. The `E` of Case 1 exists. Take the block containing `a` and `b` of the transitive closure
   of `(ω ∪ ω^{-1}) ∩ D²`, which is a congruence on `D` because the transitive closure of a
   subalgebra of `D²` is a subalgebra. Maximality of `E` is never used.
4. The `WLOG` at line 1170 needs `σ̃` symmetric, which holds for `δ̃ ∘ δ̃^{-1}`.
5. `{a} ∘ ω` is a subuniverse — because `{a}` is one, by idempotence — which is what makes it
   equal to `A` in Case 2.

The appeal to `CORMainStableIntersection` at line 1214 is **correct but not in the
corollary's shape**. The three displayed boxes `{a}×B×C×B`, `{a}×C×C×C`, `{a}×C×B×B` are the
tight boxes of three witnesses; the corollary wants `A` in the freed coordinate. Widening each
to `{a}×A×C×B`, `{a}×C×C×A`, `{a}×C×A×B` gives its hypothesis (4) with `n = 3`,
`B_i = A_i = A` (legitimate since `⋘` is reflexive, `main.tex:1598`), and since all three
types are `C` and `n = 3`, alternatives (ba), (l), (c), (pc) all fail — so hypothesis (3) must
fail, which is the conclusion. The three witnesses are `(a,b,a,b)`, `(a,a,a,a)` and
`(a,a,b,b)`.

Two more small things in the same proof: `C' ≤_C C` at line 1226 comes out of
`LEMBACenterSImplyPPDefinition` as `C' ≤_C A` and needs `LEMBACenterImplyIntersection` to
land in `C`; and the appeal there to `proj_1(ξ) = A` should be to `{a} ∘ ω = A`, since `C'`
constrains the fourth coordinate to `B` rather than to `b`.

`LEMNontrivialReflexiveBridgeImplies` is otherwise sound: the uniqueness of `σ*`, the upgrade
from "every block of `LeftLinked(σ*)` of size > 1 satisfies `B² ⊆ σ*`" to
`σ* = LeftLinked(σ*)`, and the prime argument (`p·x₁ = p·x₂` is pp-definable from
`x₁−x₂ = x₃−x₄`, and the resulting `S` contradicts minimality of `σ*`) all check out. Note
the contradiction is with *minimality of `σ*`*, not with irreducibility directly.

One statement needs a word: `LEMLinkedImpliesBACenter` (line 222) concludes *"there exists a
BA or central subuniverse on `A` or `B`"*, with no properness. Every algebra is a BA
subuniverse of itself, so read literally it is vacuous; it is used at line 1282 as though it
said *proper nonempty*. Same family as convention item C3.

## §5.4, second instalment: the three bridge-triviality lemmas

`LEMPCCongruencePropertyInductiveStep` (1372), `LEMPCBridgesAreTrivial` (1449),
`LEMNoBridgeBetweenDifferentTypes` (1565), `LEMBridgeTOPCCongruence` (1680).

Note that `LEMPCCongruencePropertyInductiveStep` carries as hypothesis (2) exactly the
pair-reflexivity that §5.4's first block needs and does not state: *"`(a,b,a,b),(b,a,b,a) ∈ δ`
for every `(a,b) ∈ proj_{1,2}(δ)`"*. So the property is in the author's vocabulary; it is
simply missing from the two lemmas that also require it.

### D14 — Case 1 of `LEMPCCongruencePropertyInductiveStep`. **CONFIRMED, no repair found**

Line 1392: `B <_T A` with `|B| > 1`, `δ' = δ ∩ B⁴`, and then

> *"By Lemma \ref{LEMBACenterLinkedness} `RightLinked(proj_{1,2,3}(δ')) = B²`."*

`LEMBACenterLinkedness` (line 194, Barto–Kozik Prop 2.15(i)) is about a **binary** relation:
`R ≤_sd A₁×A₂`, `Bᵢ` absorbing, `R ∩ (B₁×B₂) ≤_sd B₁×B₂`, `R` linked ⟹ `R ∩ (B₁×B₂)`
linked. Two things go wrong.

- *Which relation.* Hypothesis (3) of the lemma is about the split `(1,2)|(3)`, so the
  natural application has `R = proj_{1,2,3}(δ)`, `B₁ = B² ∩ proj_{1,2}(δ)`, `B₂ = B`, and
  yields that `proj_{1,2,3}(δ) ∩ B³` is linked. The induction needs
  `proj_{1,2,3}(δ ∩ B⁴)`, which is contained in it and can be smaller: a tuple of `δ` whose
  first three coordinates lie in `B` need not have its fourth there. Getting `δ ∩ B⁴` out of
  the lemma instead requires linkedness of `δ` in the split `(1,2)|(3,4)` or `(1,2,3)|(4)`,
  and hypothesis (3) does not give either — a path in the coarser bipartite graph does not
  lift, because consecutive edges through a third coordinate `c` may use different fourth
  coordinates.
- *Subdirectness.* The lemma's hypothesis `R ∩ (B₁×B₂) ≤_sd B₁×B₂` is not discharged. It does
  hold, by hypotheses (2) and reflexivity — `(x₁,x₂,x₁) ∈ R` for `(x₁,x₂) ∈ B₁` and
  `(x₃,x₃,x₃) ∈ R` for `x₃ ∈ B` — but that has to be said.

I did not find a repair. Restricting with the absorbing term `t` against
`(x₃,x₄,x₁,x₂) ∈ δ` (symmetry) does land a tuple in `δ ∩ B⁴`, but at moved coordinates, so it
does not identify the two projections. **Open.** Note the contrast with the analogous step in
`LEMPCBridgesAreTrivial` Case 2, which works precisely because a closure property is proved
first (see below); no such property is available here, where `B` is a strong subuniverse
rather than a linkedness block.

The rest of the lemma is **sound**, and I checked it line by line.

- The `|A| = 1` worry does not arise: clause (3) of the bridge definition forces
  `proj_{1,2}(δ) ⊋ 0_A`, hence `|A| ≥ 2`.
- Case 2's two applications of the ternary absorbing operation are correct, and I recomputed
  both coordinatewise. The first gives `(a,a,g(b,b,a),a) ∈ δ`, whence `g(b,b,a) = a` by clause
  (4); the second gives `(a,a,b,a) ∈ δ`, whence `b = a`. The step needs *ternary* absorption
  where `T = C` only supplies centrality, so `LEMCenterImpliesTernaryAbsorption`
  (`main.tex:1350`) is an unstated citation.
- Case 3 is correct: `LEMBAConLeftOrCenterOnRight` is applied to the transpose of
  `proj_{1,2,3}(δ)`, `LEMAbsorbingEquality` to `C <_BA proj_{1,2}(δ)` — and the case
  `C = proj_{1,2}(δ)` needs a word, since `LEMAbsorbingEquality` hypothesises a proper
  containment while the conclusion is immediate when it is an equality.
- The three cases are exhaustive: a proper nonempty BA or central subuniverse either has size
  > 1 (Case 1) or is a singleton (Case 2); otherwise Case 3.

### `LEMPCBridgesAreTrivial` — **sound**, with two steps to write out

Both are in Case 1, which is where the work is.

**The counting step.** Line 1478: *"Since `proj_{1,2}(δ) = proj_{3,4}(δ)`, for any
`(a,b,c,d) ∈ δ` the elements `c/σ` and `d/σ` are also uniquely determined by `a/σ` and
`b/σ`."* What the case hypothesis gives is uniqueness in the *other* direction — it is a
statement about `ξ = δ ∘ δ^{-1}`, and the claim is about `δ^{-1} ∘ δ`. The bridge between them
is pigeonhole, and the cited equality of projections is exactly what powers it: on
`σ*/σ`, which is finite, `δ` induces a bipartite relation whose left neighbourhoods are
nonempty (`proj_{1,2}(δ) = σ*`), pairwise disjoint (that is what Case 1 says), and cover the
right side (`proj_{3,4}(δ) = σ*`). Equal finite cardinalities force every neighbourhood to be
a singleton, so the induced relation is a bijection and uniqueness holds both ways. One line,
but it is the hinge of the case.

**The four combinations.** Line 1534 derives `proj_{1,4}(δ) = σ` or `proj_{1,3}(δ) = σ`, and
by the same argument with `x₁, x₂` switched, `proj_{2,4}(δ) = σ` or `proj_{2,3}(δ) = σ`, then
says *"This completes this case"*. Two of the four combinations are the conclusion; the other
two — `proj_{1,3} = proj_{2,3} = σ` and `proj_{1,4} = proj_{2,4} = σ` — must be excluded, and
they are, because either would give `proj_{1,2}(δ) ⊆ σ` against `proj_{1,2}(δ) = σ* ⊋ σ`. And
the containment `⊇` in the conclusion comes from stability under `σ` plus
`proj_{1,2}(δ) = σ*`. Also: the "switching `x₁` and `x₂`" appeal needs `σ*` symmetric, which
holds because `(σ*)^{-1}` is another minimal relation `⊋ σ` stable under `σ`.

Everything else checks: `ζ₁, ζ₂` really are bridges where claimed, `ζ̃₂ = proj_{1,4}(δ)` by
direct computation, `(a,a,c,c) ∈ ζ₁` for every `(a,b,c,d) ∈ δ`, and the trichotomy at line
1470 is exhaustive because each `RightLinked` is a congruence containing `σ`, so minimality of
`σ*` puts it at `σ` or above `σ*`.

**Case 2 is the model for what Case 1 of D14 is missing.** Before applying
`LEMPCCongruencePropertyInductiveStep` to `ξ ∩ B⁴`, the proof establishes (lines 1548–1554)
that *"`a,b,d ∈ B` for any `c ∈ B` and `(a,b,c,d) ∈ ξ`"* — i.e. `ξ ∩ (A²×B×A) ⊆ B⁴`.
**That** is what makes `proj_{1,2,3}(ξ ∩ B⁴) = proj_{1,2,3}(ξ) ∩ (A²×B)` and hence linked,
`B` being a block. One gap remains at this call: hypothesis (3) of the bridge definition for
`ξ ∩ B⁴` requires `σ*∩B² ⊋ σ∩B²`, which is not argued. It is not needed — if it fails, then
by clause (4) every tuple of `ξ ∩ B⁴` has both pairs in `σ`, and linkedness on a `B` that is
not a `σ`-block produces `(x₁,x₁,x₃,x₃) ∈ ξ` with `(x₁,x₃) ∉ σ` directly, which is the
conclusion. But the lemma cannot be *cited* on a non-bridge; the case has to be inlined.

Case 3 is the hedge at line 1560 already on the list, *"This case can be considered in the
same way as Case 2."*
