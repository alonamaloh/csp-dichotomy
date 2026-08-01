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

- **D6** — `LEMConnectedProperties(a)` applying `LEMBridgeFromRelation` without its third
  hypothesis, with the claimed witness in `ℤ₄ × ℤ₂ × ℤ₄`.
- **D7** — two claimed gaps in `THMMainInductiveCSPClaim`: Case 1 proving (1c) relative to the
  wrong reduction, and "linked" not established where (1c) demands it.
- **C1–C10** — the convention list. Cheaper: these are readings to legislate, not claims to
  falsify, so the failure mode is different.

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
