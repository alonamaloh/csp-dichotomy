# Review of `csp-standalone.tex`

Line numbers below refer to the supplied generated file `csp-standalone.tex` (revision `35c8e30`, generated 2026-08-02). I also checked the one explicit theorem citation to Brady's supplied notes, `csp.tex`.

## Overall assessment

This is already a useful and unusually perceptive **formalization blueprint and source audit**. It catches several real defects, identifies many suppressed hypotheses, and often proposes the right repair. But it is **not yet a correct, complete human-readable proof of the CSP dichotomy**, which is what stage (1) of the proposed plan requires.

There are three different kinds of problem:

1. Several displayed arguments are mathematically wrong as written. Most look repairable, but they cannot remain in a reviewed proof.
2. Several central theorems are only stated, outlined, or explicitly called sketches. In particular, the main induction and the bridge-from-instance lemma—the spine of the tractable half—are absent as proofs.
3. The document is internally unsure whether it is stage (1), stage (2), or a project-status report. Its title, abstract, implementation notes, schedules, Lean line counts, and “what has been built” sections make it unmistakably a blueprint rather than a clean proof paper.

My bottom-line recommendation is therefore: **do not send this out as the stage-(1) proof yet**. First repair the blocking mathematical points below, write the omitted spine in full, and split the proof from the formalization/project-management material.

## The highest-priority mathematical issues

### 1. The opening dichotomy theorem needs the core/rigid-core qualification

At lines 220–228 the theorem is stated for an arbitrary finite constraint language:

> If some WNU operation preserves Γ, CSP(Γ) is tractable; otherwise it is NP-complete.

That is not the right invariant formulation for an arbitrary, possibly non-core template. The idempotent Taylor/WNU criterion is applied after passing to a core and adjoining the singleton unary relations (equivalently, to the idempotent reduct associated with a rigid core). The manuscript itself acknowledges this only in the hard-half chain at lines 4061–4063.

Brady's notes explicitly supply the missing reduction in the section **“Cores and Idempotent Reducts”**: finite templates have cores; adjoining all singleton unary relations to a core gives a logspace-equivalent rigid core; and algebraically this corresponds to passing to the idempotent reduct.

A clean formulation would be one of:

- Assume from the outset that Γ is a rigid core containing every singleton unary relation, and state the WNU criterion under that hypothesis; or
- For arbitrary Γ, state the criterion for the rigidification of a core of Γ, followed by the equivalence of the corresponding CSPs.

The tractable argument also fixes a **special** WNU basic operation and works in `V_n`. Lemma 4.7 (`lem:special-wnu`) gives the replacement, but the theorem-to-standing-hypotheses transition should be explicit: the special WNU is a term operation of the original polymorphism algebra and therefore still preserves every relation of Γ.

### 2. The main theorem is not proved

The decisive half of the proof is explicitly introduced as

> “Proof of (1), sketch of the structure”

at lines 3629–3672. It records the case split and names the lemmas that ought to close it, but it does not carry out the argument. The difficult construction of Ω is merely specified by four properties at lines 3698–3710. The manuscript itself says that its nested well-founded construction is the most demanding step.

This alone prevents the document from being stage (1). A human-readable proof need not be formalization-granular, but it must give enough argument to establish:

- existence of Ω;
- termination of the weakening processes;
- derivation of condition 4 from condition 3;
- the two branches following the construction;
- every invocation of the mutual inductive hypothesis; and
- the final derivation of (1b) or (1c).

At present a reader who did not already know Zhuk's proof could not reconstruct this from the manuscript.

### 3. The proposed induction measure does not survive expanded coverings

Lines 3531–3568 propose

\[
\mu(D)=\sum_{x\in\operatorname{Var}(\mathcal I)} |D_x|
\]

and quantify universally over the changing instance. But an expanded covering introduces additional variables, and extending a reduction along the parent map repeats the parent domains. The manuscript even notes that the resulting value of μ is larger (lines 3551–3555), and then nevertheless claims that the induction is on μ alone.

The later observation that the domain at one parent variable is properly cut does not compare the two sums: the reductions live on different variable sets, and arbitrarily many children can outweigh that decrease. Thus the displayed strong induction is not well founded as stated.

A repair has to make the measure insensitive to duplicated covering variables. Plausible approaches are:

- formulate the theorem for an instance equipped with a map to a fixed base instance and measure the reduction on the base variables; or
- carry a parent-domain profile and order those profiles, rather than summing over every child variable.

Merely putting the quantifier over instances inside the induction does not solve the problem.

### 4. `lem:bridge-from-instance` and most of its support are only statements

The bridge-from-instance lemma at lines 3888–3905 is described as an eight-hypothesis, roughly ten-page proof and as the sole bridge source for the main argument. No proof is given. The same supporting subsection merely states, without proof or precise imported reference:

- `lem:minimal-consistent`;
- `lem:crucial-irreducible`;
- `lem:bridge-from-relation`;
- most of `lem:connected`;
- `lem:find-consistent`;
- `lem:parallelogram-crucial`; and
- `cor:same-type`.

Some may be intended as imported results, but then they need exact sources and exact matching hypotheses. As written they are simply gaps in the document's logical dependency chain.

### 5. The proposed repair of maximal multi-type extension repeats the image/intersection error

Lines 3428–3460 begin with

\[
C_1=\bigcap_j C_1^j
\]

and then choose a minimal family of the images `C_1^j/σ` whose intersection avoids `B_2/σ`. The claim that “the whole family works” at line 3433 does not follow. What the hypothesis gives is

\[
(C_1/\sigma)\cap(B_2/\sigma)=\varnothing,
\]

whereas only

\[
(\bigcap_j C_1^j)/\sigma\subseteq\bigcap_j(C_1^j/\sigma)
\]

holds in general. The right-hand intersection can acquire extra σ-classes and meet `B_2/σ`.

This is exactly the phenomenon correctly identified in the manuscript's own Hazard `haz:quotient-rel` at lines 781–793. No saturation hypothesis has been proved here, so the minimal-family repair is invalid.

A valid repair must either establish that every relevant `C_1^j` is σ-saturated inside `B_1`, or avoid taking intersections after quotienting.

### 6. Several bridge arguments are wrong as written

#### 6.1 `lem:perfect-from-linked`: the reason given for reflexivity is false

At lines 2063–2071 the manuscript says that `bcol(δ)` is reflexive because the projection of δ contains σ. That does not follow: `(a,a)` lying in the first projection only gives some tuple `δ(a,a,c,d)`, not `δ(a,a,a,a)`.

The main proof can probably be repaired. Bridge stability and clause (d) show that `bcol(δ)` is left- and right-total: from `δ(a,a,c,d)` one has `c σ d` and may replace `d` by `c`, obtaining `δ(a,a,c,c)`. Consequently

\[
\rho=\widetilde\delta\circ\widetilde\delta^{-1}
\]

is reflexive and symmetric; linkedness gives connectedness, and sufficiently high powers of ρ are full. The manuscript should state and prove this lemma instead of asserting reflexivity of `bcol(δ)` itself.

#### 6.2 The symmetrisation proof silently invokes irreducibility

`lem:symmetrise` (lines 1054–1090) has no irreducibility hypothesis, but its proof invokes `lem:bridge-comp`, whose statement at lines 1026–1029 requires all congruences involved to be irreducible.

This is locally repairable: the collapse identity for `δ*δ^{-1}` can be proved directly by unfolding the existential formula, without invoking the imported bridge-composition theorem. Otherwise irreducibility must be added to the statement.

#### 6.3 `lem:bridge-abelian` is false for the one-element algebra and its converse proof is invalid

At lines 2188–2199 the biconditional omits `|A|>1`. A one-element algebra is Abelian, but no bridge from `0_A` to itself can satisfy the required strict projection clause.

For the nontrivial case, “composing a bridge with itself enough times yields a reflexive, symmetric, transitive relation” is not justified. The appropriate construction is to view δ as a compatible relation on `A²`, take `δ∘δ^{-1}` to obtain a reflexive symmetric compatible relation, and then take a stabilized power/transitive closure. Clause (d) keeps the diagonal as a block. This should be written out.

#### 6.4 `lem:nice-bridge-abelian`: `δ*δ` need not be an equivalence relation

Lines 2688–2699 assert that the square of a reflexive symmetric relation is an equivalence relation. That is false in general. The later assertion that full first projection and full collapse imply full three-coordinate projection is also unsupported.

There is a much cleaner repair. Once `A/σ` is affine, `δ/σ`, viewed as a compatible binary relation on `(A/σ)²`, is reflexive by pair-reflexivity. In a Mal'tsev algebra every reflexive compatible relation is a congruence. Clause (d) makes the diagonal a congruence block, forcing the standard difference congruence. Alternatively, the subgroup/graph-of-an-automorphism argument already described in Remark `rem:phi-twist` can be promoted to the proof; pair-reflexivity forces the automorphism to be the identity.

#### 6.5 `lem:block-good-bridge`: a union of subuniverses need not be a subuniverse

At lines 2731–2735 the relation

\[
(\omega\cup\omega^{-1})\cap D^2
\]

is treated as a subalgebra. The union of two subuniverses is generally not closed, so its transitive closure need not be compatible for the reason given.

A likely repair is to use

\[
\rho=(\omega\circ\omega^{-1})\cap D^2.
\]

This is compatible, reflexive and symmetric. Because ω is reflexive, every undirected ω-edge is a ρ-edge; conversely a ρ-edge is a two-edge undirected ω-path. Thus ρ has exactly the same connected components as the undirected ω-graph, and the transitive closure of ρ is a congruence.

#### 6.6 The reflexivisation used in `lem:linear-equiv` and `lem:linear-on-top` is missing

At lines 2862–2865 and 3379–3382 an arbitrary bridge is said to be one “which we may take reflexive.” No lemma establishes that. `lem:symmetrise` cannot be used as written, because it assumes reflexivity of its input.

This may have a standard repair, but it needs to be stated and proved. It is not a harmless normalization.

#### 6.7 `lem:bridge-between-congruences` has a concrete witness typo

At line 3003, to prove `σ₁ ⊆ proj₁₂(δ)`, the manuscript says to take `z_i=y_i=x_1`. For a general `(x_1,x_2)∈σ₁`, one must take `z_i=y_i=x_i`. The printed choice works only when `x_1=x_2`.

#### 6.8 Key bridge classification lemmas are unproved

`lem:no-cross-bridge` and `lem:bridge-to-pc` (lines 1291–1321) are stated without proof or citation. `lem:pc-bridges-trivial` eventually gets a proof, but that proof invokes auxiliary relations `ζ₁,ζ₂` “of the source” without defining them (lines 2950–2954). These are not optional details: stable intersection and the PC case use exactly these structural claims.

There is also a possible dependency-cycle danger: `block-good-bridge` invokes stable intersection; stable intersection invokes `no-cross-bridge`; and the most natural proof of no-cross appears to route through the linear bridge characterization and the block-good machinery. An explicit acyclic dependency graph is needed.

### 7. The intersection theorem is still an outline

`lem:self-intersection-pc` has only a proof sketch at lines 2505–2517, including an apparent index typo `B_{n-1}/σ_n` in a statement parameterized by `k,m`.

More importantly, `lem:intersection-good`, one of the central technical results, is explicitly left at the case-structure level. Hazard `haz:intersection-draft` says that twelve subcases remain to be expanded (lines 2575–2582). Since much of the later bridge theory depends on this theorem, the document cannot claim a complete proof while this remains.

There is also a statement/proof mismatch in `lem:intersect-all`: the statement at lines 1937–1940 gives only `B∩D dotted-lll A`, whereas the proof gives the stronger and later-needed `B∩D dotted-lll^A D`. The manuscript notices this at lines 3274–3279; the theorem statement itself should be corrected.

### 8. Weakening is not defined in a way that supports the termination argument

Lines 1618–1635 contain several problems.

- The operation is called “infinite” and then correctly counted as finite. It is finite but enormous.
- A proper weakening allows **more** tuples, so the “total number of tuples” increases rather than decreases. The suggested measure has the wrong orientation. A rank in the finite implication order, or the number of forbidden assignments, would have the right direction.
- Replacing a constraint by **all** strict weakenings can have conjunction equal to the original constraint. For example, intersecting all one-tuple extensions of a relation can recover the original relation. Thus the replacement need not make progress at all.

The construction should be recast as choosing one proper weakening (or a finite antichain with a proved rank decrease), with a precise well-founded order. This affects `rem:get-crucial`, the construction of Ω, and every occurrence of “we cannot weaken forever.”

### 9. The main theorem loses the common binary absorption witness

`lem:ba-center-implies` correctly requires a **single binary term** witnessing all coordinate absorptions (lines 1894–1900). The manuscript itself emphasizes that this omitted hypothesis is essential.

But Theorem `thm:main-inductive`(2), lines 3518–3520, records only that every coordinate reduction has type BA; it does not carry a common term. The proof then applies `lem:ba-center-implies` to the relation defining `E₂` from `E₁` at line 3591.

You need either:

- a lemma synthesizing one common binary absorption term for any finite family of coordinate absorptions; or
- reduction data that carries a common witness from the start.

Without one of these, the repaired import cannot be applied at its main call site.

### 10. The codimension-one proof uses false linear-algebra statements

At lines 3784–3791, `L` is a nonempty subuniverse of an idempotent affine algebra. Such a subuniverse is generally an **affine coset**, not necessarily a subgroup. Moreover, a product of prime fields with different primes is not one vector space, so “dimension k” and “one linear equation” are not meaningful without separating the primary components.

A short correct argument is available. Choose a point of `L` and translate, obtaining a subgroup. The kernel of the projection

\[
L\longrightarrow \prod_i \mathbb Z_{q_i}
\]

lies in `0×Z_p`, hence is either trivial or all of `Z_p`. Full kernel would put `(b,0)` in the fibre over every `b`, contradicting the chosen missing point. Thus the projection is bijective and `L` is the graph of an affine homomorphism

\[
f:\prod_i\mathbb Z_{q_i}\to\mathbb Z_p.
\]

Then `Δ=f^{-1}(0)` is empty, full, or an affine hyperplane. The linear part of `f` automatically ignores every `q`-primary factor with `q≠p`.

The manuscript's own Hazard `haz:step2-linear-algebra` notices part of the mixed-prime issue but does not repair the proof.

### 11. `SolveLinear` needs corresponding corrections

At lines 3973–3975, `φ^{-1}(I)` is justified as a subgroup. It is generally an affine coset. The proposed test is nevertheless repairable: test `0` first; if `0` lies in the set, the coset is a subgroup, and membership of the coordinate generators then implies fullness.

At lines 3978–3983, the displayed equation divides coordinates that can lie in different fields. The codimension-one equation has one target prime `p`; only coordinates over `F_p` can have nonzero coefficients. The computation must be organized prime by prime.

The decidability discussion at lines 4021–4029 also claims an unproved arity bound `k≤|A|^{|A|}`. For the strong types used here, a better route is available: BA has a binary witness by definition, and central absorption has a ternary witness by `lem:central-ternary`. Thus only finitely many binary/ternary operations need be checked, plus finitely many congruences and subsets. Do not make the algorithm depend on an uncited general absorption-arity bound.

### 12. Target (T1) does not state correctness of the displayed algorithm

Theorem `thm:t1` at lines 4036–4043 merely says that **there exists** a Boolean-valued function deciding satisfiability. For a fixed finite template that follows immediately by exhaustive search. It is not “strictly stronger than decidability,” and it does not identify the pseudocode of `Solve`.

To state what the prose claims, define a concrete recursive function `Solve_alg` (with its well-founded recursion) and prove

\[
\textsc{Solve}_{alg}(I)=\texttt{true}\iff I\text{ is satisfiable}.
\]

Until the function exists, (T1) is logically the trivial decidability theorem the manuscript says it is not.

### 13. The hard half proves only NP-hardness

Target (H1), lines 4092–4095, concludes NP-hardness. To recover the opening claim of NP-completeness, add the standard theorem that every fixed finite-template CSP lies in NP under the chosen encoding.

The passage at lines 4067–4072 from “the generated variety contains a two-element projection algebra” to “Γ pp-interprets every finite language” also compresses several nontrivial steps: HSP representation in a finite power, translation to a pp-interpretation, and the finite Inv–Pol theorem. It is acceptable as an imported theorem, but not as an unexplained equivalence.

## Definition and typing problems

### 14. The definition of a linear congruence is ill-typed

At lines 1224–1229, `S` is a relation on elements of `A`, while `(B/σ)^4` consists of tuples of σ-classes. The expression

\[
S\cap(B/\sigma)^4
\]

therefore mixes different underlying types. It should be something like

\[
(S\cap B^4)/\sigma
\]

or the restriction of the quotient relation `S/σ` to `(B/σ)^4`.

### 15. Repeated variables are allowed, but the semantic API is mostly positional

Lines 1514–1519 explicitly allow repeated variables in a constraint scope. Once this is allowed, several later definitions become ambiguous or wrong if interpreted as raw coordinate projections:

- `proj_z(C)` in 1-consistency;
- `proj_{z_i,z_{i+1}}(C)` in paths;
- `ConOne(C,x)`;
- adjacency at a common variable;
- weakening by subsets of variable names; and
- projections of constraints in instance irreducibility.

For example, if a constraint is `R(x,x)`, the raw first-coordinate projection of `R` can be full even when `R` contains no diagonal tuple and the constraint admits no value for `x`.

Choose one global policy:

- ordinary scopes have distinct variables, with repeated occurrences normalized using diagonal/equality constraints; or
- a scope is a map from positions to variables, and every semantic relation is pulled back along the equal-variable diagonal before projection.

The current document notices the problem only for `ConOne`, but it is systemic.

### 16. `LeftLinked` and `RightLinked` are never defined

These operators are used throughout the strong-subalgebra proofs, beginning at line 2247, but no definition is given in the manuscript, and Brady's notes do not use those exact names. Since several arguments depend on whether this means `R∘R^{-1}`, its transitive closure, or the corresponding congruence, the omission is substantive.

### 17. The notation `C <_{BA,C} B` is undefined

Expressions such as `C\subte{\TBA,\TC}B` occur repeatedly. It is unclear whether they mean “BA or central,” “both BA and central,” or a new combined type. In context they usually mean a disjunction. State the disjunction or define the notation explicitly; the current notation resembles a two-element type parameter and is misleading.

### 18. `lll` is simultaneously treated as a proposition and as chosen data

Definition `def:lll` makes `C lll B` an existential proposition, then speaks of “the congruences coming from” it, which depend on a chosen witnessing chain. Hazard `haz:lll-chain` correctly says that the chain must be data. But the formalization section later says `lll` is exactly `Relation.ReflTransGen` (lines 4471–4472), losing that data again.

Use two notions:

- a witnessed chain structure carrying intermediate sets, types and congruences; and
- its propositional truncation/reachability relation for consumers that do not inspect witnesses.

### 19. Small boundary conditions should be made explicit

- In `def:absorbing`, require arity `k≥1`.
- In `def:multitypes`, require `t≥1` or define the empty intersection deliberately.
- In `lem:multitype-chain`, equality `C=B` needs an empty chain; the displayed strict chain does not cover it.
- In the motivating `Z_4` bridge example, specify the algebraic structure and compatible operations. The surrounding standing notation `Z_p` is reserved for prime fields in `V_n`, so “on Z₄” is under-specified.
- `lem:pc-on-top` lacks the BA-and-centre-free hypothesis that its own following hazard says the proof uses. Since the lemma is not consumed later, either add the hypothesis and proof or remove it from the main route.

## Further proof gaps and local corrections

### 20. `lem:pp-propagation` needs a dotted conclusion or a nonemptiness hypothesis

Replacing a relation by a proper absorbing/central subrelation can make the pp-defined result empty. Lines 2119–2124 conclude the undotted `R'≤_T R`, which entails nonemptiness under the manuscript's conventions. The generally valid result is the dotted variant, unless nonemptiness of `R'` is separately assumed.

Several downstream call sites already reason in dotted form, so this is mostly a statement repair.

### 21. The proof that affine algebras have no proper absorbing subuniverse is too short

Lines 2074–2083 only discuss whether the last variable is dummy. A complete proof should use that every term operation is affine,

\[
t(x_1,\dots,x_k)=\sum_i c_i x_i,
\qquad \sum_i c_i=1,
\]

and every nonempty subuniverse is an affine coset. Absorption in coordinate `i` forces the coefficient `c_i` to annihilate the quotient direction; doing this for every coordinate forces every coefficient to vanish, contradicting their sum being 1.

### 22. `lem:tot-sym-full` calls the relation subdirect too early

At lines 2429–2431 only the diagonal left tuples `(a,…,a)` have been shown to meet every right value. This does not yet give surjectivity onto all of `A^{k-1}`. The induction at lines 2433–2436 proves the left projection is full; only then may the relation be called subdirect and the absorption theorem applied.

Also state `k≥2` explicitly.

### 23. The multiset-shift lemma needs a precise reachability statement

The phrase at line 2402 “provided that multiset uses at least one of them” is vacuous for a nonempty `k`-multiset drawn from the original values. State the exact count-vector operation and its reachable set. Clarify whether the selected entries `u,v` may have the same value but occupy distinct positions.

### 24. Stable intersection's PC case skips a necessary argument

At lines 3329–3332 the manuscript says that otherwise composing a bridge with its transpose gives a nontrivial self-bridge. This fails if the two congruences are distinct but nested: `σ₁∘σ₂` may still equal `σ₁`.

The intended repair probably uses `lem:bridge-to-pc`: a bridge between PC congruences induces an isomorphism/bijection of the quotient blocks, which rules out proper nesting on the same finite algebra and yields equality. But that lemma is currently unproved.

### 25. Stable intersection's central case needs its imported lemma in the import ledger

The repair at lines 3337–3352 invokes ZhukStrong Lemma 6.11, although the section claims to have listed its black boxes. Nonemptiness and properness of each `E_i` should also be stated explicitly before applying the essential-relation theorem.

### 26. The propagation proof does not match its stated cases

At lines 3283–3288, `lem:factor-by-delta` is said to handle `PC,L,D`, but its statement handles only `PC,L`. The `D` case can probably be obtained by splitting into linear/PC, but it must be written.

The “reverse-homomorphism lemma” used for (bt) is neither stated nor cited. For a general surjective homomorphism, the clean proof should factor it as quotient by its kernel followed by an isomorphism.

In (fm), `δ` appears without being introduced; it should be the kernel congruence of `f` after this factorization.

### 27. `lem:multiply-all-linear` is not yet a proof

Lines 3397–3419 do not specify a coherent induction statement. They rewrite all components as type D even though the theorem tracks a fixed type `PC`, `L`, or `D`; they do not construct the object to which the inductive hypothesis is applied at the “first step”; and the inclusions needed for the final conclusion are only asserted. This needs a full rewrite, not polishing.

### 28. `lem:bacon-left` suppresses several needed steps

At lines 2336–2367:

- handle `|A|=1` separately;
- prove that left-linkedness of `R` implies the required linkedness of `W_k`;
- when applying pp-propagation to `W`, prove both nonemptiness and properness; and
- replace the undefined combined notation `BA,C` by an explicit disjunction.

The argument may be sound after expansion, but it is not currently self-contained.

### 29. “Verified by exhaustion” is not a paper proof

The finite search claims at lines 2662–2666, 2273–2275 and elsewhere can be valuable sanity checks, but they should either come with reproducible code/certificates in an appendix or be replaced by short symbolic proofs/counterexamples. A statement such as “none of the six bijections works” is easy enough to verify directly in the `Z_3` counterexample.

## Source and citation audit

### Brady's Absorption Theorem citation

The citation at lines 2105–2108 to Brady, Theorem 3.11.1, is substantively correct. Brady's theorem says that for a linked subdirect relation between finite idempotent Taylor algebras, either:

1. the relation is the full product;
2. the left algebra has a proper binary-absorbing or centrally-absorbing subalgebra; or
3. the right algebra has a proper subalgebra that is both binary absorbing and centrally absorbing.

Under the manuscript's hypothesis that the relation is proper, the full-product alternative is excluded, and the manuscript's weaker symmetric conclusion follows. It should therefore be labelled **a corollary of Brady's Absorption Theorem**, not presented as though it were Brady's verbatim theorem.

This is the only precise Brady theorem citation in the manuscript. If Brady's notes are intended to be the permitted prerequisite base, add an import ledger listing every fact used from them by section/theorem title. In particular, the opening reduction should cite Brady's “Cores and Idempotent Reducts” section.

### Other citation issues

I did not source-match every citation to Zhuk, Barto–Kozik, Barto–Kazda, Hobby–McKenzie, and Maróti–McKenzie, because those originals were not among the supplied files. The manuscript itself currently imports many results beyond the one Brady citation, so its precise black-box boundary is unclear.

One definite LaTeX/source-reference error is line 1266:

```tex
\cite[Lem.~\ref*{lem:linear-equiv}]{ZhukSimplified}
```

This prints the manuscript's own lemma number as the number in Zhuk's paper. Replace it with the actual source lemma number.

The bibliography entry for `RossSlides` is incomplete enough that a reader cannot identify the source.

## Internal consistency and presentation

### The document does not match stage (1)

The generated title is **“A formalization blueprint”**, and the abstract says the document rewrites the proof “at a granularity a proof assistant can consume.” Large portions discuss Mathlib APIs, Lean modules, line counts, throughput, worktrees, schedules, and implementation status. Those belong to stage (2) or a project plan, not to the human-readable proof in stage (1).

A much cleaner three-document split would be:

1. **Proof paper:** theorem, reductions, definitions, imported results, complete proof.
2. **Source audit/errata appendix:** discrepancies in Zhuk's papers and their repairs.
3. **Formalization blueprint:** Lean representations, dependency DAG, missing Mathlib infrastructure, implementation status and estimates.

At present the proof is harder to assess because claims about its mathematics are interleaved with claims about a development that was not supplied.

### Contradictory completeness/status claims

The manuscript says, variously:

- proofs are deferred and “not reproduced here” (lines 1764–1767), although a later section purports to prove them;
- fourteen defects are all repaired and require no new mathematics (lines 4147–4161);
- nine blocking items remain, including gaps needing new arguments (lines 4324–4331);
- four blocking items require new mathematics (lines 4538–4545);
- the intersection proof still has twelve subcases unwritten;
- the main theorem is a sketch; and
- bridge-from-instance has no proof.

These cannot all be true. Replace the prose with a single status table distinguishing:

- proved in this manuscript;
- imported with exact citation;
- proof sketched but incomplete;
- statement only; and
- unresolved/possibly false.

### Dependency order is stated in both directions

Lines 3916–3919 and 4515–4518 give the sensible order

\[
\text{stable intersection}\to\text{bridge from instance}\to\text{main induction}.
\]

Lines 4540–4543 reverse the first arrow. Correct the latter.

### Claims about the Lean development are uncheckable from the supplied material

Lines 4411–4455 assert that modules are complete and `sorry`-free. Since the Lean repository/source was not supplied, these should not be evidentiary claims inside the proof paper. Give a repository URL and commit hash in the blueprint, or omit the status claims from stage (1).

### Remove promotional and scheduling claims from the proof

Claims such as “the only complete recent proof,” “unformalizable,” “neither formalized anywhere,” throughput in verified lines per hour, and person-time estimates are not part of the mathematical argument and would require independent evidence. They distract from the much stronger contribution here: the actual technical audit.

## LaTeX and production details

The file compiles successfully and the rendered pages are generally clean. The main concrete issues are:

- duplicate label `thm:stable-intersection` at lines 1948 and 3311;
- several overfull boxes, the worst near lines 4426–4430 (about 51 pt) and 4014–4021 (about 23 pt);
- smaller overfull boxes around lines 321–326, 1147–1155, 1427–1429, 3365–3370, and 3999;
- font substitutions for italic small caps; and
- the generated-file header says not to edit this file, so reviews and line references should ultimately target the section source files rather than only the standalone output.

## Recommended revision order

1. **Choose the document's role.** For stage (1), strip out formalization status, Lean design and scheduling material.
2. **Correct the theorem statement** by passing through a core/rigid core, and add NP membership.
3. **Freeze a typed vocabulary:** repeated-variable semantics, `LeftLinked`/`RightLinked`, witnessed `lll` chains, combined-type notation, and the linear-congruence quotient relation.
4. **Repair the bridge layer** before using it: linked-power, symmetrisation, Abelian bridge lemmas, block-good bridge, reflexivisation, no-cross, and bridge-to-PC.
5. **Write the intersection property in full**, then re-audit every theorem that depends on it.
6. **Replace the maximal-mult proof** with one that does not commute images with intersections without saturation.
7. **Fix weakening and the well-founded induction measure**, including coverings.
8. **Write bridge-from-instance and the main induction completely.** Only after these exist is the tractable half a proof.
9. **Repair the affine/mixed-prime linear algebra and define the actual algorithm.**
10. **Run a final dependency and import audit**, with every theorem marked proved or cited—not merely stated.

The encouraging part is that many of the local defects have short repairs, and the manuscript already contains several of the right ideas. The discouraging part is that the unresolved material is not peripheral: it includes the main induction, its bridge generator, its well-foundedness, and one of the central multi-type lemmas. Those have to be settled before review of prose and polish becomes the limiting factor.
