# Mathlib probe: the universal-algebra layer for the CSP dichotomy

Survey item 09. Everything below was read from source, not inferred from names, and the
load-bearing claims were **checked by compiling a probe file** against Mathlib v4.32.2 /
Lean 4.32.2 (see §5; the probe is preserved at
`/tmp/claude-1000/-home-alvaro-claude-zeb/b3d460d7-227a-4a0c-983d-31fbf26d8692/scratchpad/survey/09-mathlib-probe.lean`).

Path conventions in this document:

* `MATHLIB/` = `/home/alvaro/claude/zhuk-lean/.lake/packages/mathlib/Mathlib/`
* `ZL/` = `/home/alvaro/claude/zhuk-lean/ZhukLean/`

Mathlib pin: `leanprover-community/mathlib` rev `v4.32.2`, toolchain `leanprover/lean4:v4.32.2`
(from `/home/alvaro/claude/zhuk-lean/lakefile.toml` and `lean-toolchain`).

---

## 1. Capability table

Legend: **HAVE** = usable as-is; **PARTIAL** = the general machinery exists but not at the
generality/shape we need, or exists only for a different algebraic setting; **MISSING** = must
be built.

### 1.1 Signatures, algebras, terms

| Capability | Status | Where |
|---|---|---|
| Signature / similarity type | **HAVE** | `FirstOrder.Language` — `MATHLIB/ModelTheory/Basic.lean:58`. `structure Language where Functions : ℕ → Type u; Relations : ℕ → Type v`. Arity is a `ℕ` index; no encoding needed. |
| Algebraic signature (no relations) | **HAVE** | `Language.IsAlgebraic` (`Basic.lean:72`) `:= ∀ n, IsEmpty (L.Relations n)`. Also `IsRelational` (`:69`). `HomClass.strongHomClassOfIsAlgebraic` (`:264`) and `Embedding.ofInjective` (`:426`) are gated on it. |
| Algebra (structure) | **HAVE** | `class Language.Structure (L) (M)` — `Basic.lean:159`, fields `funMap : ∀ {n}, L.Functions n → (Fin n → M) → M` and `RelMap : ∀ {n}, L.Relations n → (Fin n → M) → Prop`. Both have `isEmptyElim` autoparam defaults, so a purely algebraic language needs no `RelMap` boilerplate *when declaring `Structure` from scratch* — but a hand-written `where`-instance that supplies `funMap` explicitly still often wants `RelMap` given. |
| Term (syntax) | **HAVE** | `inductive Language.Term (α)` — `MATHLIB/ModelTheory/Syntax.lean:79`, constructors `var : α → Term α` and `func : L.Functions l → (Fin l → Term α) → Term α`. Branching arity is `Fin l → Term α`, so arbitrary-arity signatures are native. |
| Term realization | **HAVE** | `Term.realize (v : α → M) : L.Term α → M` — `MATHLIB/ModelTheory/Semantics.lean:71`. Simp lemmas `realize_var:76`, `realize_func:79`, `realize_function_term:83` (`f.term.realize v = funMap f v`, with `Functions.term` at `Syntax.lean:179`). |
| Term relabelling / substitution | **HAVE** | `Term.relabel` (`Syntax.lean:117`), `Term.relabelEquiv` (`:144`), `Term.subst` (`:246`), `Term.restrictVar` (`:148`). Realize laws: `realize_relabel` (`Semantics.lean:88`), `realize_subst` (`:124`), `realize_restrictVar` (`:138`). |
| Terms are polymorphic in the variable type | **HAVE** | `L.Term α` for arbitrary `α`. This is the feature that let zhuk-lean drop the blueprint's generator enumeration (README finding 3). |
| Homomorphisms preserve term operations | **HAVE** | `HomClass.realize_term` — `Semantics.lean:229`: `t.realize (g ∘ v) = g (t.realize v)`. |
| Idempotence / WNU / Taylor / special-WNU predicates | **MISSING** | Nothing in Mathlib. zhuk-lean has `IsIdempotent` and `TaylorAt`/`IsTaylorOn` (§2). WNU and "special" WNU are new but trivial to state. |

### 1.2 Subuniverses / subalgebras / `Sg`

All in `MATHLIB/ModelTheory/Substructures.lean` (985 lines). This is the richest part.

| Capability | Status | Decl |
|---|---|---|
| "closed under an operation" | **HAVE** | `ClosedUnder (f : L.Functions n) (s : Set M)` — `:66`, with `.inter :78`, `.inf :81`, `.sInf :86`. |
| Subuniverse | **HAVE** | `structure Substructure` — `:96` (`carrier : Set M`, `fun_mem : ∀ {n} (f : L.Functions n), ClosedUnder f carrier`); `SetLike` instance `:107`. |
| Subuniverse lattice | **HAVE** | `instCompleteLattice : CompleteLattice (L.Substructure M)` — `:213`; `coe_inf :177`, `coe_sInf :197`, `coe_iInf :208`, `coe_top :167`, `mem_iSup_of_directed :388`. |
| `Sg` (generated subuniverse) | **HAVE** | `Substructure.closure : LowerAdjoint (↑)` — `:231`. `mem_closure :237`, `subset_closure :242`, `closure_le :256`, `closure_mono :262`, `closure_induction :333`, `dense_induction :341`, `gi : GaloisInsertion :349`, `closure_eq :359`, `closure_union :370`, `closure_iUnion :373`, `closure_insert :376`, `iSup_eq_closure :384`. |
| `Sg(S)` = image of terms over `S` | **HAVE** | `coe_closure_eq_range_term_realize :268` and `mem_closure_iff_exists_term :284` — `x ∈ closure L s ↔ ∃ t : L.Term ↥s, t.realize (↑) = x`. **The variable type is the generating set itself**, which is exactly the ergonomic win zhuk-lean exploited. |
| Terms stay in a subuniverse | **HAVE** | `Term.realize_mem :136`. |
| Preimage / image of a subuniverse | **HAVE** | `Substructure.comap :429`, `Substructure.map :449`, `gc_map_comap :476`, `map_closure :533`, `map_sup :506`, `comap_inf :513`, plus the injective/surjective Galois (co)insertions `:547`, `:590`. |
| Induced algebra on a subuniverse | **HAVE** | `inducedStructure : L.Structure ↥S` — `:628`; `Substructure.subtype : S ↪[L] M` `:633`; `topEquiv :649`; `inclusion :959`. |
| Image / range of a hom | **HAVE** | `Hom.range :794`, `range_eq_map :804`, `Hom.eqLocus :831`, `eqOn_closure :844`. |
| Embedding ≅ its range | **HAVE** | `Embedding.equivRange` (`Substructures.lean` ~`:930`), `Embedding.substructureEquivMap :903`. |
| Finitely generated | **HAVE** | `Substructure.FG :47`, `fg_iff_exists_fin_generating_family :56`, `FG.map :82` — `MATHLIB/ModelTheory/FinitelyGenerated.lean`. |
| Adding constants (for polynomial ops) | **HAVE** | `Language.withConstants` / notation `L[[α]]` — `MATHLIB/ModelTheory/LanguageMap.lean:381,385`; `Substructure.withConstants` — `Substructures.lean:719`; `closure_withConstants_eq :750`; `LHom.substructureReduct :690`. Directly relevant to defining **PC (polynomially complete) algebras**. |
| Subuniverse lattice is finite / co-well-founded for finite `M` | **HAVE (verified)** | `SetLike` instances in `MATHLIB/Data/SetLike/Fintype.lean` (`Finite A` from `[SetLike A B] [Finite B]`, line 29) chained with `Finite.to_wellFoundedLT` (`MATHLIB/Data/Fintype/Card.lean:454`, `@[to_dual]` so `Finite.to_wellFoundedGT` also exists). Probe: `example : WellFoundedGT (L.Substructure M) := inferInstance` typechecks for `[Finite M]`. |

### 1.3 Homomorphisms

| Capability | Status | Decl |
|---|---|---|
| Hom / Embedding / Equiv | **HAVE** | `Language.Hom` (`→[L]`) `Basic.lean:182`, `Embedding` (`↪[L]`) `:203`, `Equiv` (`≃[L]`) `:216`, with `HomClass`/`StrongHomClass` `:246,:253`, `id/comp` `:320,:334`. |
| Kernel of a hom | **MISSING** | There is `Setoid.ker` (`MATHLIB/Data/Setoid/Basic.lean:79`) for bare functions, but nothing saying the kernel of an `L`-hom is a congruence (there being no congruence type). |
| First isomorphism theorem | **MISSING** | No `M / ker f ≅ range f` for structures. Only `Setoid.quotientKerEquivRange` (`Data/Setoid/Basic.lean:383`) at the level of bare sets. |

### 1.4 Congruences, quotients, correspondence

| Capability | Status | Detail |
|---|---|---|
| General congruence on an arbitrary structure | **MISSING** | Grep over all of `MATHLIB/ModelTheory/` for `Con`/`congruence` returns only `Prestructure`, `equivSetoid` (isomorphism of bundled structures), `DirectLimit.setoid`, `Equivalence.iffSetoid`. There is **no** `Con`-like type for `L.Structure`. |
| `Con` for `Mul` | **PARTIAL — template only** | `structure Con [Mul M] extends Setoid M` — `MATHLIB/GroupTheory/Congruence/Defs.lean:69`. It is `Mul`-specific and cannot be reused. But it is the *right blueprint*: `FunLike :126`, `LE :310`, `InfSet :321`, `CompleteLattice :360`, `conGen :104` with `conGen_eq :404`, `conGen_le :420`, `gi :428`, `Con.Quotient :192`, `comap :511`; and in `GroupTheory/Congruence/Basic.lean`: `Con.prod :56`, `Con.pi :62`, `Con.submonoid :125` / `ofSubmonoid :136` (the congruence ↔ subalgebra-of-`M×M` dictionary!), `quotientKerEquivRange :190`, `quotientQuotientEquivQuotient :259`. `RingCon` is the same story in `MATHLIB/RingTheory/Congruence/`. |
| Quotient of a structure | **PARTIAL** | `Language.Prestructure (s : Setoid M)` — `MATHLIB/ModelTheory/Quotients.lean:39` — is *literally a congruence plus relation-compatibility*: `fun_equiv : ∀ {n} {f} (x y : Fin n → M), x ≈ y → funMap f x ≈ funMap f y` (using the `Quotient.piSetoid` instance from `MATHLIB/Data/Quot.lean:408`). `instance quotientStructure : L.Structure (Quotient s)` at `:48` (built with `Quotient.finChoice`, `MATHLIB/Data/Fintype/Quotient.lean:105`), plus `funMap_quotient_mk' :56`, `relMap_quotient_mk' :63`, and `Term.realize_quotient_mk' :70` (`t.realize (⟦x ·⟧) = ⟦t.realize x⟧`). **Verified**: for `[L.IsAlgebraic]` a hand-rolled congruence produces a `Prestructure` (the `rel_equiv` obligation is discharged by `IsEmpty`), and `quotientStructure` then gives the quotient algebra for free. **Caveat, also verified**: `Prestructure` bundles `toStructure : L.Structure M` as a *field*, and `quotientStructure` needs the `Prestructure` in scope *when the statement is elaborated*. A `letI := c.pre` inside a tactic block is too late — `L.Structure (Quotient c.toSetoid)` fails to synthesize in the goal. So `Prestructure` is unusable for stating theorems about a varying congruence; we need our own `Congruence.Quotient` with a global `instance`. The *construction* can be copied verbatim. |
| Congruence lattice | **MISSING** | Follows from the congruence type; the `Con` complete-lattice recipe transfers verbatim. |
| Correspondence theorem | **PARTIAL** | `Setoid.correspondence (r : Setoid α) : { s // r ≤ s } ≃o Setoid (Quotient r)` — `MATHLIB/Data/Setoid/Basic.lean:516` (verified to typecheck). This is the set-level statement; the algebra-level one (congruences of `A/σ` ↔ congruences of `A` above `σ`) is new, but `Setoid.correspondence` plus `Setoid.comap :443` / `Setoid.map :409` / `comap_map_of_ker_le :471` do most of the work. Also `Setoid.quotientQuotientEquivQuotient :497` (third iso theorem, set level). |
| Blocks / partitions | **HAVE** | `Setoid.classes` (`MATHLIB/Data/Setoid/Partition.lean:60`), `mkClasses :51`, `IsPartition :193`, `isPartition_classes :200`, `classes_mkClasses :232`, `IndexedPartition :318`, `Partitions.completeLattice :285`. Useful for `a/σ`, `B/σ`, `R/σ`. |
| Setoid lattice | **HAVE** | `Setoid.completeLattice` — `Data/Setoid/Basic.lean:185`, `Setoid.ker :79`, `ker_def :91`, `inf_iff_and :159`, `sup_eq_eqvGen :263`, `sSup_eq_eqvGen :276`, `gi :312` (Galois insertion `Relation.EqvGen.setoid ⊣ coe`), `eq_top_iff :211`, `ker_eq_bot_iff :216`. `Relation.EqvGen` at `MATHLIB/Logic/Relation.lean:355`. |

### 1.5 Products, powers, subdirect products, relations

| Capability | Status | Detail |
|---|---|---|
| Product of structures `∀ i, M i` | **MISSING in Mathlib** | Confirmed by grep: the only `Structure` instance on anything product-shaped is `Ultraproducts.«structure»` (`MATHLIB/ModelTheory/Ultraproducts.lean:74`), which is the structure on the *quotient* `Filter.Product M`, built via `Prestructure` — `∀ i, M i` never gets a `Structure`. zhuk-lean supplies it (§2). |
| Binary product `A × B` | **MISSING in Mathlib** | Same; zhuk-lean supplies `prodStructure`. |
| Relations as subalgebras of products | **HAVE, once the product exists** | `L.Substructure (∀ i, M i)` with zhuk-lean's `piStructure`. |
| Projections, reindexing | **HAVE via zhuk-lean** | `evalHom`, `reindexHom` (§2). `proj_{i…}(R) = R.map (reindexHom g)`; `R ∩ {x : x u ∈ S} = R ⊓ S.comap (evalHom u)`. Both idioms already appear in `ZL/Essential.lean`, `ZL/Regrouping.lean`, `ZL/Doubling.lean`. |
| Subdirect product | **MISSING** | Grep for `subdirect` over all of Mathlib: **zero hits** (the one match is the word "subdirectory"). zhuk-lean has `Subdirect` for the binary case only (`ZL/Center.lean:36`). |
| Binary-relation algebra (`δ₁ ∘ δ₂`, `δ⁻¹`, linked, bijective) | **MISSING** | `MATHLIB/Data/Rel.lean` has `Rel.comp`/`Rel.inv` for bare relations, but nothing about compatibility with subalgebras. |
| Parallelogram property / rectangularity | **MISSING** | Nothing. |
| `σ^{[n]}`, stability of a coordinate under `σ` | **MISSING** | Nothing. |

### 1.6 Lattice theory for the congruence lattice

| Capability | Status | Decl |
|---|---|---|
| Complete lattices | **HAVE** | `MATHLIB/Order/CompleteLattice/`. |
| Meet-irreducible | **HAVE (but see the warning)** | `InfIrred a : Prop := ¬IsMax a ∧ ∀ ⦃b c⦄, b ⊓ c = a → b = a ∨ c = a` — `MATHLIB/Order/Irreducible.lean:139`. Also `InfPrime :144`, `InfPrime.infIrred`, `InfIrred.ne_top :175`, `InfIrred.finset_inf_eq :179`. |
| Decomposition into meet-irreducibles | **HAVE** | `exists_infIrred_decomposition (a : α) : ∃ s : Finset α, s.inf id = a ∧ ∀ ⦃b⦄, b ∈ s → InfIrred b` — `Order/Irreducible.lean:189`, hypotheses `[SemilatticeInf α] [OrderTop α] [WellFoundedGT α]`. Verified to apply to `L.Substructure M` for finite `M`. |
| Covers | **HAVE** | `CovBy` (`⋖`) and `WCovBy` (`⩿`) — `MATHLIB/Order/Cover.lean`; `covBy_top_iff` / `bot_covBy_iff` ↔ `IsCoatom`/`IsAtom` (`MATHLIB/Order/Atoms.lean:219,:122`); `IsStronglyCoatomic` `:428`, `exists_covBy_le_of_lt :420`. |
| Atoms / coatoms / simple orders | **HAVE** | `IsAtom :74`, `IsCoatom :158`, `IsSimpleOrder`, `IsAtomic :333`, `IsCoatomic :339` — `MATHLIB/Order/Atoms.lean`. |
| Modular lattice, Jordan–Hölder | **HAVE** | `IsModularLattice` `MATHLIB/Order/ModularLattice.lean:91`; `JordanHolderLattice`, `CompositionSeries` `MATHLIB/Order/JordanHolder.lean:88,:144`. (Not obviously needed, but available.) |
| Finite ⇒ well-founded both ways | **HAVE (verified)** | `Finite.to_wellFoundedLT` `MATHLIB/Data/Fintype/Card.lean:454` + `@[to_dual]`. |

> **⚠ Warning about "irreducible".** Zhuk's notion (`main.tex:1237–1248`) is **not** `InfIrred` in
> `Con(A)`: *"a congruence σ on **A** is irreducible if it cannot be represented as an
> intersection of other **binary subalgebras of A × A that are stable under σ**"*, equivalently
> "there are no `S₁,…,S_k ≤ A/σ × A/σ` with `0 = ⋂ Sᵢ` and `Sᵢ ≠ 0` for all `i`". The meet is
> taken in the lattice of **σ-stable binary subalgebras**, which strictly contains the congruence
> lattice interval `[σ, 1]`. And it is a *finitary but unbounded* intersection, not a binary one —
> in a finite lattice these coincide, but the equivalence has to be proved.
> Correspondingly `σ*` is defined as *the minimal `δ ≤ A × A` with `δ ⊋ σ` and `δ` stable under
> `σ`* — again a subalgebra, **not** a priori a congruence (indeed "σ* is a congruence" is
> condition (2) in the definition of a *linear* congruence, `main.tex:1370`, so Zhuk is explicit
> that it can fail). Mathlib's `InfIrred`/`CovBy` therefore apply only after we have set up the
> right ambient lattice, and are not a drop-in.

### 1.7 `Z_p` and linear algebras

| Capability | Status | Decl |
|---|---|---|
| `ZMod n` | **HAVE** | `def ZMod : ℕ → Type` `MATHLIB/Data/ZMod/Defs.lean:142`; `commRing :175`, `fintype :158`, `ZMod.card :166`, `decidableEq :146`. |
| `ZMod p` is a field | **HAVE** | `instance : Field (ZMod p)` — `MATHLIB/Algebra/Field/ZMod.lean:30` (under `[Fact p.Prime]`). |
| `Z_p` as an algebra `(ZMod p; x₁+⋯+x_n)` | **MISSING (but easy)** | Verified constructible: `funMap f x := ∑ i, x i`. |
| Affine subspaces over `ZMod p` | **HAVE** (as linear algebra) | `Submodule`, `AffineSubspace`, `AffineSubspace.mk'`, `Module (ZMod p) V`. Identifying *subuniverses of `Z_p^k`* with affine subspaces is new work. |

> **⚠ Hidden hypothesis.** `Z_p ∈ 𝒱_n` requires `w(x,…,x) = n·x = x` in `ZMod p`, i.e.
> `p ∣ n - 1`, i.e. `n ≡ 1 (mod p)`. Zhuk states only *"In the paper every algebra `Z_p` belongs
> to `𝒱_n` for a fixed `n`, hence the algebra `Z_p` is uniquely defined"* (`main.tex:1119–1121`)
> — the divisibility constraint is never written down. Every statement that produces a `Z_p`
> (e.g. Lemma `LEMLInearOnTheTopIsEasy`, `main.tex:1459`: *"Then `A/σ ≅ Z_p` for some prime `p`"*)
> is implicitly asserting `p ∣ n − 1` as part of the conclusion. Note that *special*-ness of
> `w^{Z_p}` (`w(x,…,x,y) = w(x,…,x,w(x,…,x,y))`, `main.tex:1080`) is then automatic, and
> WNU-ness is automatic from symmetry. **This must be made explicit in the blueprint.**

### 1.8 CSP, clones, polymorphisms, Taylor terms

| Capability | Status | Detail |
|---|---|---|
| Clone `Clo(A)` | **MISSING in Mathlib; HAVE in zhuk-lean** | `ZL/Relational.lean:28` `termOps L M m : L.Substructure ((Fin m → M) → M)`, carrier `Set.range fun t : L.Term (Fin m) => t.realize`, with `proj_mem_termOps :43`. This *is* `Clo_m(A)` and it is a subuniverse of a power, which is the form Barto–Kazda needs. |
| Polynomial clone / PC algebras | **MISSING (but well-supported)** | `L[[A]]` + `Substructure.withConstants` (§1.2) gives polynomial operations essentially for free. |
| Polymorphisms, `Pol(Γ)`, `Inv` | **MISSING** | Nothing. |
| CSP instances, pp-definability | **MISSING** | The *only* CSP content in Mathlib is `MATHLIB/Combinatorics/Optimization/ValuedCSP.lean` (Martin Dvořák): `ValuedCSP D C := Set (Σ n, (Fin n → D) → C)` (`:43`), `ValuedCSP.Term :50`, `Instance :64`, `IsOptimumSolution :74`, `FractionalOperation :90`, `FractionalOperation.IsFractionalPolymorphismFor :119`, `IsSymmetric :127`, `Function.HasMaxCutProperty :86`. This is the *valued* CSP with fractional polymorphisms over an ordered `AddCommMonoid` of costs. **It shares no definitions with what we need** — no crisp relations, no `Pol`, no algebras, no clone. Treat it as unrelated prior art, not a foundation. |
| Taylor / WNU / cyclic / Siggers terms | **MISSING** | zhuk-lean has `TaylorAt`/`IsTaylorOn` (`ZL/Absorption.lean:120,134`) as a *predicate on a term of a generic language*, which is the right pattern for WNU too. |
| Absorption | **MISSING in Mathlib; HAVE in zhuk-lean** | See §2. |
| Definable sets (first-order) | **HAVE but wrong fragment** | `Set.Definable` `MATHLIB/ModelTheory/Definability.lean` (full FO with parameters, Boolean algebra of definable sets, `Definable.image_comp` for projections); `BoundedFormula.IsExistential` `MATHLIB/ModelTheory/Complexity.lean:343`. There is **no** positive-primitive (conjunctive-existential) fragment. pp-definability should be built semantically (as projections of intersections), not syntactically. |

---

## 2. What zhuk-lean already gives us

`/home/alvaro/claude/zhuk-lean` — 12 files, 1591 lines, `sorry`-free, builds warm in ~2 s
(1178 jobs). Every declaration is generic in `L : Language` and `[L.Structure M]`; nothing is
specialised to a fixed signature. Reuse potential is high.

### 2.1 `ZL/Product.lean` (143 lines) — the missing Mathlib file

* `instance piStructure : L.Structure (∀ i, M i)` (`:29`) — coordinatewise `funMap`, and
  `RelMap r x := ∀ i, RelMap r (x · i)` (a choice: the *product* reading, not the "some
  coordinate" reading; irrelevant for algebraic languages but worth fixing in a docstring).
* `funMap_pi :34` (simp), `realize_pi :47` (simp) — `t.realize v i = t.realize (v · i)`.
* `instance prodStructure : L.Structure (A × B)` (`:60`), `fst_funMap_prod :65`,
  `snd_funMap_prod :69`, `realize_prod :74` (simp).
* `fstHom :83`, `sndHom :89` — projections as `→[L]`.
* `snoc_funMap :106` — `Fin.snoc` commutes with `funMap` (needed for "append a coordinate"
  arguments; used by the doubling trick).
* `reindexHom (g : I' → I) : (I → M) →[L] (I' → M)` (`:123`) — precomposition; packages
  projection *and* reindexing of powers in one map.
* `evalHom (i : I) : (I → M) →[L] M` (`:133`).

This is exactly what Mathlib lacks, and it is the load-bearing infrastructure for
"relations = subalgebras of products". **Reuse verbatim.** Two gaps to fill later:
heterogeneous *binary* `A × B` is there, heterogeneous *finite* products (`Fin n` with
different algebras per coordinate) are covered by `piStructure` with `M : I → Type*`; but there
is no `Substructure.prod`/`Substructure.pi` (a product of subuniverses as a subuniverse of the
product), and no `Subdirect` for arbitrary index types.

### 2.2 `ZL/Absorption.lean` (178 lines)

* `IsIdempotent L M : Prop` (`:44`) `:= ∀ {n} (f : L.Functions n) (a : M), funMap f (fun _ => a) = a`.
* `IsIdempotent.realize_const :48` (every term operation is idempotent),
  `IsIdempotent.closedUnder_singleton :58`.
* `Witnesses (E D : Set M) (t : L.Term V) : Prop` (`:70`) —
  `∀ (i : V) (z : V → M), z i ∈ D → (∀ j ≠ i, z j ∈ E) → t.realize z ∈ E`.
  **The tuple/coordinatewise shape**, chosen deliberately over "a list from `E` with one entry
  overwritten"; the two differ exactly when `E = ∅`, `|V| = 1`, `D ≠ ∅`, and only this one makes
  the Barto–Kazda relational description a biconditional. Note `V` is an *arbitrary* type, which
  is what lets star powers (indexed by `Fin ℓ → Fin k`) feed the definition.
* `Absorbs L E D :=  ∃ m, ∃ t : L.Term (Fin m), Witnesses E D t` (`:74`);
  `BinAbsorbs :78`; `Absorbs.of_finite :101` (transport from any `Finite` variable type);
  `Witnesses.relabelEquiv :85`.
* `TaylorAt (D : Set M) (t : L.Term (Fin k)) (i : Fin k)` (`:120`) — a *structure* carrying
  `u v : Fin k → Fin 2`, `u i = 0`, `v i = 1`, and `∀ w, (∀ b, w b ∈ D) → (t.relabel u).realize w
  = (t.relabel v).realize w`. `IsTaylorOn D t := ∀ i, TaylorAt D t i` (`:134`, a `Type`, not a
  `Prop` — data). **This is the model to copy for WNU**: state the identity as an equation
  between `t.relabel u` and `t.relabel v`, so substitution arguments are `Term.realize_relabel`
  rewrites rather than index arithmetic.
* `binAbsorbs_of_oneSided :145` — a one-sided closure condition plus one Taylor identity gives
  two-sided binary absorption; needs only `E ⊆ D`, not that `E`, `D` are subuniverses.

### 2.3 `ZL/StarPower.lean` (54 lines)

`starPower (t : L.Term (Fin k)) : (ℓ : ℕ) → L.Term (Fin ℓ → Fin k)` (`:28`) with
`realize_starPower_succ :43`. The convention — index `t^{*ℓ}`'s variables by `Fin ℓ → Fin k`
rather than `Fin (k^ℓ)` — turns "block `j`, position `q`" into `Fin.cons j q` and eliminates
Euclidean division entirely. **Generalises directly to any iterated-substitution construction.**

### 2.4 `ZL/Essential.lean` (112 lines) and `ZL/Regrouping.lean` (135 lines)

* `IsEssential (S : Set M) (R : L.Substructure (Fin m → M))` (`Essential.lean:36`) — `witness`
  (E1) + `no_full` (E2).
* `not_isEssential_of_witnesses :59` (absorption at arity `m` kills `m`-ary essential relations);
  `HasEssential :67`; `hasEssential_of_succ :74` and `hasEssential_of_le :92` (arity reduction, via
  `R ⊓ S.comap (evalHom (Fin.last m))` then `.map (reindexHom Fin.castSucc)`);
  `not_hasEssential_of_witnesses :105`.
* `IsEssentialOn (S) (J : Finset I) (block : I → Fin m) (R : L.Substructure (I → M))`
  (`Regrouping.lean:38`) and `hasEssential_of_essentialOn :60`.
  **The "live set" convention** — fix an ambient index *type* `I`, a block function
  `block : I → Fin m`, and a live `Finset I` — instead of shrinking the index type. This keeps the
  relation fixed under the induction and makes deletion `J.erase u`. It also doubles as the
  *transport/reindexing* lemma: the base case of `hasEssential_of_essentialOn` **is** a
  reindexing along a chosen system of block representatives. This convention is a strong asset:
  the CSP proof reindexes and regroups constantly.

### 2.5 `ZL/Relational.lean` (95 lines)

* `termOps L M m : L.Substructure ((Fin m → M) → M)` (`:28`) — the algebra of `m`-ary term
  operations, i.e. `Clo_m(A)`, as a subuniverse of a power. `mem_termOps :40`,
  `proj_mem_termOps :43`.
* `exists_witnesses_of_not_hasEssential :50` — **Barto–Kazda**: for finite `M`, `0 < m`, no
  `S`-essential relation of arity `m` ⟹ some `m`-ary term witnesses `S ⊴ A`. Proof runs `termOps`
  against the regrouping lemma with the "live" tuples = tuples with exactly one coordinate
  outside `S`, blocked by *which* coordinate that is.

This is the single most reusable non-trivial theorem in the repo, and it is exactly the
"relational description of absorption" the CSP proof leans on.

### 2.6 `ZL/Center.lean`, `Step.lean`, `Absorbs.lean`, `Central.lean`, `Doubling.lean`, `Ternary.lean`

* `Subdirect (R : L.Substructure (A × B))` (`Center.lean:36`), `nbhd :43`, `leftCenter :46`,
  `nbhdSub :109`, `leftCenterSub :118`, `realize_mem_nbhd_realize :101`.
* `center_step` (`Step.lean:52`), `center_star` / `leftCenter_witnesses` (`Absorbs.lean:32,81`).
* `centralGens` / `centralPairs` / `CentrallyAbsorbs` / `center_central` / `zhuk_center`
  (`Central.lean:36,149,159,114,169`) — **`CentrallyAbsorbs` is exactly Zhuk's "central
  subuniverse"** (`main.tex:1344–1352`): `Absorbs C ⊤` plus `∀ a ∉ C, (a,a) ∉ Sg((a×C) ∪ (C×a))`.
* `betaSet`/`betaSub`, `betaSet_subset_closure`, `linking_disjoint`, `doubled`,
  `hasEssential_doubled` (`Doubling.lean:33,37,79,141,195,213`).
* `exists_ternary_witnesses` (`Ternary.lean:26`) — **Zhuk's `LEMCenterImpliesTernaryAbsorption`
  (`main.tex:1356`, cited there as [zhuk2021strong, Cor 6.11.1])**, fully proved.
* `zhuk_main` (`Ternary.lean:61`).

So the CSP blueprint's "central subuniverse ⟹ ternary absorbing" and the whole left-centre
theorem are already done, generically in `L`.

### 2.7 Conventions — will they scale to congruences and quotients?

**Yes, with two named caveats.**

*Scales well:*

1. **Generic `L`.** Nothing is tied to a one-operation signature. When we move to `𝒱_n` we can
   either instantiate `L` to a one-symbol algebraic language or (cheaper, and recommended) keep
   `L` generic and add `IsWNU (t : L.Term (Fin n))` as a predicate, mirroring `IsTaylorOn`.
2. **Sets, not bundled subuniverses, in the *statements* of `Witnesses`/`Absorbs`.** `E D : Set M`
   with a bundled `L.Substructure` produced only where needed (`nbhdSub`, `leftCenterSub`,
   `betaSub`, `singletonSub`). This avoids constant coercion friction and is the right call.
3. **Relations live in `L.Substructure (I → M)` and are manipulated only with
   `⊓`, `.map (reindexHom g)`, `.comap (evalHom i)`.** Every relational operation the CSP proof
   needs (projection, intersection, fibre, adding/deleting coordinates) is one of these.
   Congruences fit: `Con(A) ↪ L.Substructure (M × M)` and `σ` is manipulated the same way.
4. **The live-set/block-function encoding** (`IsEssentialOn`) is exactly the discipline that
   makes reindexing cheap, and the CSP proof reindexes far more than the centre theorem did.
5. **Data-carrying identity structures** (`TaylorAt` is a `structure`, not `∃`) — lets you *use*
   the selectors `u`, `v` later. Same for WNU.

*Caveats:*

1. **`piStructure` and `prodStructure` are global instances on `∀ i, M i` and `A × B`.** They
   fire on *any* pi/product type. In 1600 lines this was fine (build is 2.6 s). At CSP scale
   (plausibly 20–50 k lines with towers `A`, `↥S`, `A/σ`, `∏ (A_i/σ_i)`, `((Fin m → M) → M)`)
   this deserves a watch: instance search will consider `piStructure` for every function type in
   sight. Mitigation: keep them, but consider `@[instance]`-priority tuning and avoid stating
   lemmas at types where the pi-instance is unintended.
2. **`Structure` bundles `RelMap`.** Every new instance (product, quotient, `Z_p`) must supply a
   `RelMap` even though `𝒱_n` is purely algebraic. The README flags this. Cheap fix: work under
   `[L.IsAlgebraic]` and give `RelMap := fun {_} => isEmptyElim` (the autoparam default already
   does this when you omit the field). **Choosing an algebraic language is not cosmetic**: it is
   what makes `Prestructure`'s `rel_equiv` obligation vacuous, i.e. what makes "congruence" and
   "Mathlib prestructure" coincide.
3. **No congruence anywhere in zhuk-lean.** It never needed one. So the convention question for
   congruences is genuinely open — see §4.

---

## 3. The missing layer, ranked by size

Rough line estimates assume Mathlib-quality API (simp lemmas, `SetLike` boilerplate, order
instances), not just the bare definitions.

| # | Item | Est. lines | Notes / what Mathlib gives |
|---|---|---|---|
| 1 | **Congruences**: `Congruence L M` as `SetLike … (M × M)` extending `Setoid M`; `CompleteLattice`; `conGen`; `ker` of an `L.Hom`; `comap`/`map`; `Congruence.Quotient` + `L.Structure` instance + `mk : M →[L] c.Quotient`; universal property / lift; first iso theorem; correspondence theorem; `Con.pi`/`Con.prod` analogues. | **700–1200** | Copy the shape of `MATHLIB/GroupTheory/Congruence/Defs.lean` (~700 lines) + `Basic.lean` (~320). Quotient construction copies `MATHLIB/ModelTheory/Quotients.lean` (`Quotient.finChoice`). `Setoid.correspondence` does the order-iso. `Con.submonoid`/`ofSubmonoid` is the model for the congruence ↔ subalgebra-of-`M×M` dictionary, which Zhuk uses constantly. |
| 2 | **Relations toolkit**: `Subdirect` for arbitrary index types; `proj_{i₁…i_s}`; binary-relation composition `δ₁ ∘ δ₂`, `δ⁻¹`, linked, bijective; `σ^{[n]}`; stability of a coordinate under `σ`; `R/σ`; rectangularity; parallelogram property; rectangular closure; `Substructure.pi`/`prod`. | **800–1500** | Nothing in Mathlib. `Rel.comp`/`Rel.inv` exist but carry no algebra. zhuk-lean's `reindexHom`/`evalHom`/`⊓`/`.map`/`.comap` idioms are the right primitives. |
| 3 | **`Z_p`, linear algebras, affine subspaces**: the `L.Structure (ZMod p)` instance under `p ∣ n−1`; subuniverses of `Z_p^k` = affine subspaces; congruences of `Z_p^k`; `A/σ ≅ Z_p` transport; `(Z_p^n; x₁−x₂ = x₃−x₄)` as a relation. | **400–700** | `Field (ZMod p)` (`MATHLIB/Algebra/Field/ZMod.lean:30`), `Submodule`, `AffineSubspace` do the linear algebra; the *bridge* from "subuniverse of the `n`-ary-sum algebra" to "affine subspace" is the real work. Flag the `p ∣ n−1` hypothesis. |
| 4 | **Irreducible congruences and `σ*`**: the lattice of σ-stable binary subalgebras of `A²`; Zhuk's `irreducible`; `σ*`; equivalence with "0 is irreducible in `A/σ`"; unique-cover characterisation; `Con(A)` is co-well-founded for finite `A`. | **300–500** | Mathlib's `InfIrred` / `exists_infIrred_decomposition` / `CovBy` / `IsCoatom` supply the lattice vocabulary but **not** the statement (see the ⚠ in §1.6). Finiteness/well-foundedness is free (`SetLike` + `Finite.to_wellFoundedGT`). |
| 5 | **Clones and polynomial clones**: `Clo_m(A)` (have, `termOps`); `Clo` closed under composition/permutation; `Pol(Γ)`/`Inv` Galois connection if needed; polynomial clone via `L[[A]]`; **PC algebras** (`clone(F ∪ constants) = all operations`). | **200–400** | `termOps` is already the hard part. `MATHLIB/Order/GaloisConnection` and `L[[A]]`/`Substructure.withConstants` cover the rest. |
| 6 | **WNU / special WNU apparatus**: `IsWNU`; "every idempotent WNU on a finite set has a special WNU in its clone" (Zhuk's `LEMExistenceOfSpesialWNULemma`, `main.tex:1078–1082`); the `𝒱_n` setting. | **150–300** | New, but the `TaylorAt` pattern transfers. The special-WNU lemma is a real (if short) finite-semigroup-flavoured argument. |
| 7 | **Products of structures + subdirect** (already in zhuk-lean, needs extension to `Substructure.pi`, `Subdirect` at arbitrary arity, projections onto coordinate subsets). | **100–200** | zhuk-lean `Product.lean` is 143 lines and covers the core. |
| 8 | **Homomorphism plumbing that Mathlib lacks**: `ker` of an `L.Hom` as a congruence; hom induced on subalgebras; hom on quotients; iso theorems. | folded into #1 | |

**Total new universal-algebra foundation: roughly 2 700 – 4 800 lines**, of which item 1
(congruences) and item 2 (relations toolkit) are ~60 %. This is the *infrastructure*, before any
Zhuk-specific mathematics (strong/linear subuniverses, bridges, the `⋘` order, the algorithm's
correctness) — that is a separate and much larger budget.

Reality check: `Mathlib/GroupTheory/Congruence/` is ~1000 lines for `Con` on `Mul`, and
`Mathlib/ModelTheory/Substructures.lean` is 985 lines for the subuniverse lattice. Those are the
right calibration points; the congruence estimate is not padded.

---

## 4. Design recommendation

### The question

Build on `Mathlib.ModelTheory` (as zhuk-lean did), or define a bespoke
`FiniteWNUAlgebra`-style type?

### 4.1 Case for a bespoke type

* Zhuk works in `𝒱_n`: **one** basic operation `w`, arity `n`, idempotent, special, WNU
  (`main.tex:1108–1113`). A bespoke `structure` could carry `w`, `idem`, `wnu`, `special`,
  `[Fintype A]` as *fields*, so they are never hypotheses to thread. In zhuk-lean, `hA : IsIdempotent L A`
  and `hB : IsIdempotent L B` are threaded through **every single theorem** (see `zhuk_main`'s
  signature: `[Finite A] [Finite B] [Nonempty B] (hA) (hB) (hsd) {k} {t} (T) (hbaf)` — eight
  arguments). Bundling would cut that noticeably.
* No `RelMap`, no `Language` parameter, no universe juggling (`Language.{u,v}` × `Type w`).
* Term operations could be defined **semantically** — `Clo A m : Set ((Fin m → A) → A)` as the
  least set containing projections and closed under `w` — rather than syntactically. Many
  arguments in Zhuk say "there is a term such that…", and semantic clones avoid all
  `relabel`/`subst` bookkeeping. `MATHLIB/Order/Closure.lean` (`ClosureOperator`, `LowerAdjoint`)
  gives the closure API for free.
* Zhuk *changes the basic operation* early (replace `w` by a special `w' ∈ Clo(w)`,
  `main.tex:1078`). With a bespoke bundled algebra this is "construct a new algebra on the same
  carrier"; with `Structure` it is a new instance on the same type, which is a diamond hazard.

### 4.2 Case for `Mathlib.ModelTheory`

* **The 1591 lines of zhuk-lean are all generic in `L` and would be thrown away.** That includes
  the two hardest results — `exists_witnesses_of_not_hasEssential` (Barto–Kazda) and
  `exists_ternary_witnesses` (Zhuk's Cor 6.11.1, cited *without proof* in `main.tex:1356`) — both
  of which the CSP blueprint needs and neither of which is short.
* `Substructures.lean` is 985 lines of exactly what a `Sg`-based development wants: complete
  lattice, Galois insertion, `map`/`comap` with both (co)insertions, `closure_induction`,
  induced structure on a subalgebra, `Hom.range`/`eqLocus`, finite generation. Rebuilding this
  around a bespoke type is ~600–900 lines of pure duplication, and it is *dull* duplication that
  will be less polished than Mathlib's.
* `mem_closure_iff_exists_term` with the **variable type = generating set** is a genuinely
  better interface than any hand-rolled clone would give; zhuk-lean's README finding 3 records
  that it deleted an entire piece of blueprint apparatus (Lemma 1.20, block-respecting
  enumeration). A semantic clone loses this: to say "`x ∈ Sg(S)`" you would still have to
  produce an arity and a tuple, which is exactly the bookkeeping the syntactic version removes.
* `L[[A]]` / `Substructure.withConstants` / `LHom.substructureReduct` give **polynomial
  operations and PC algebras** almost for free (§1.2). With a bespoke type, PC algebras require
  a second, parallel clone construction.
* **Congruences and quotients are *cheaper*, not dearer, in ModelTheory** — verified: for an
  algebraic language, a congruence *is* a `Language.Prestructure`, and `quotientStructure`
  + `funMap_quotient_mk'` + `Term.realize_quotient_mk'` come free from
  `MATHLIB/ModelTheory/Quotients.lean`. A bespoke type would have to redo `Quotient.finChoice`
  plumbing from scratch.
* Multi-sorted heterogeneity (`∏ D_x` with different `D_x`, plus external `Z_p` factors) is
  native: `piStructure` takes `M : I → Type*`.
* The generic-`L` statements are *stronger* and cost nothing: `zhuk_center` holds for any
  language, so re-deriving it inside `𝒱_n` is instantiation, not reproof.

### 4.3 Recommendation

**Build on `Mathlib.ModelTheory`, keeping `L` generic in the foundational layer, and introduce
`𝒱_n` as a thin instantiation layer on top.** Concretely:

1. **Keep zhuk-lean's `Product.lean` as the base module**, extended with `Substructure.pi`,
   `Substructure.prod`, `Subdirect` at arbitrary arity, and coordinate-subset projections.
2. **Add `Congruence L M`** as our own type:
   ```
   structure Congruence (L : Language) (M : Type*) [L.Structure M] extends Setoid M where
     funMap' : ∀ {n} (f : L.Functions n) (x y : Fin n → M),
       (∀ i, r (x i) (y i)) → r (funMap f x) (funMap f y)
   ```
   with `SetLike (Congruence L M) (M × M)` (so Zhuk's habit of treating congruences as binary
   subalgebras is literal — provide `Congruence.toSubstructure : L.Substructure (M × M)` and
   `Congruence.ofSubstructure`, both verified constructible using zhuk-lean's `prodStructure`),
   a `CompleteLattice` copied from `Con`, `congGen`, `Congruence.ker` of an `L.Hom`, and
   `Congruence.Quotient` with a **global** `L.Structure` instance.
   *Do not* route the quotient through `Language.Prestructure`: it works mathematically (verified)
   but the instance is only available under a `letI`, so it cannot appear in theorem statements
   about a varying congruence. Copy the *construction* from `Quotients.lean`, not the interface.
3. **Assume `[L.IsAlgebraic]` in the CSP development.** It makes `Prestructure.rel_equiv`
   vacuous, makes `HomClass.strongHomClassOfIsAlgebraic` and `Embedding.ofInjective` available,
   and kills the `RelMap` boilerplate. `𝒱_n` is algebraic.
4. **Do not instantiate `L` to a one-symbol language.** Instead follow zhuk-lean's `IsTaylorOn`
   pattern: a `structure IsWNU (t : L.Term (Fin n))` (data, so the witnesses are usable), and a
   `𝒱_n` context `variable [L.IsAlgebraic] [Finite A] (hA : IsIdempotent L A) (w : L.Term (Fin n))
   (hw : IsSpecialWNU w)`. This keeps every existing zhuk-lean theorem applicable verbatim and
   avoids a language-instantiation refactor. Bundle the context into a
   `class`/`structure` (e.g. `VnAlgebra L n A`) purely to shorten signatures — that recovers most
   of the bespoke-type ergonomics without the duplication.
5. **Clones stay semantic-on-top-of-syntactic**: `termOps` (`Set.range Term.realize`) is already
   the right object; add `polyOps` via `L[[A]]` for PC algebras.

The one thing I would *not* do is the middle road of "keep everything inside one ambient finite
set `A`, with subuniverses as `Set A` and quotients as sets of blocks". It looks attractive
(no new types, no transport) but it breaks immediately: `Z_p` is not a subalgebra of `A`, and
Zhuk's `A/σ ≅ Z_p` (`main.tex:1459`), `A₁/σ₁ ≅ A₂/σ₂` (`LEMBridgeTOPCCongruence`(2),
`main.tex:1437`) and `ζ ≤ A × A × Z_p` (`main.tex:1297`) all require genuinely external
algebras. A category of algebras is unavoidable; `[L.Structure M]` is the cheapest one available.

---

## 5. What was verified by compilation

The following all typecheck against Mathlib v4.32.2 on top of `ZhukLean.Product`
(probe saved at `.../scratchpad/survey/09-mathlib-probe.lean`):

* `example [Finite M] : Finite (L.Substructure M) := inferInstance`
* `example [Finite M] : WellFoundedGT (L.Substructure M) := inferInstance` (and `WellFoundedLT`)
* `exists_infIrred_decomposition (S : L.Substructure M)` applies for finite `M`
* a hand-rolled `Cong L M` (Setoid + `funMap'`) yields `L.Prestructure c.toSetoid` when
  `[L.IsAlgebraic]`, and `quotientStructure` then produces `L.Structure (Quotient c.toSetoid)`
* `Term.realize_quotient_mk'` gives `t.realize (⟦v ·⟧) = ⟦t.realize v⟧` — **but only if the
  `Prestructure` is an instance binder on the statement**; a `letI` in the proof fails with
  `failed to synthesize L.Structure (Quotient c.toSetoid)`
* a congruence can be built from an `L.Substructure (M × M)` that is an equivalence relation,
  using zhuk-lean's `prodStructure` (Mathlib alone cannot even state this)
* `Setoid.correspondence r : { s // r ≤ s } ≃o Setoid (Quotient r)`
* `L.Structure (ZMod p)` with `funMap f x := ∑ i, x i` is constructible

---

## 6. Risks and things that will bite a formalization

1. **Zhuk's "irreducible congruence" ≠ Mathlib's `InfIrred`.** The intersection ranges over
   σ-stable *binary subalgebras of `A²`*, not over congruences, and is finitary-unbounded rather
   than binary (`main.tex:1237–1244`). `σ*` is likewise defined as a minimal *subalgebra*, and
   "σ* is a congruence" is an explicit extra hypothesis in the definition of a linear congruence
   (`main.tex:1370`). Getting this wrong would silently change the theorem.
2. **`Z_p ∈ 𝒱_n` silently requires `p ∣ n − 1`.** Never stated (`main.tex:1119–1121`). Every
   conclusion of the form "`A/σ ≅ Z_p` for some prime `p`" carries it.
3. **`Prestructure` is a trap.** It is *exactly* a congruence for algebraic languages, which
   makes it tempting; but its typeclass shape (structure bundled as a field, keyed on a `Setoid`)
   makes the quotient's `Structure` instance unavailable at statement-elaboration time. Verified
   failure mode. Budget for our own `Congruence.Quotient`.
4. **`piStructure`/`prodStructure` are aggressive global instances.** Fine at 1600 lines; needs
   monitoring at 20–50 k with towers of quotients and powers.
5. **Mathlib's `ValuedCSP` is a false friend.** It is the *valued* CSP with fractional
   polymorphisms; it shares no definitions with the crisp CSP dichotomy and should not be
   imported or extended.
6. **No pp-definability fragment.** `Set.Definable` is full first-order; `IsExistential` exists
   but there is no positive-conjunctive class. pp-definitions should be modelled semantically
   (projections of intersections of relations), not as syntax — otherwise a large syntactic
   fragment must be built and its semantics proved.
7. **`Nat.find` usage in `ZL/Doubling.lean:223`** (`obtain ⟨R, hR, hRk⟩ := Nat.find_spec hex`)
   requires a `DecidablePred` instance that is being supplied classically; it works, but the
   pattern "minimise over all essential relations" recurs constantly in Zhuk and deserves a
   packaged `argmin`-over-a-finite-lattice lemma rather than ad-hoc `Nat.find`.
8. **Zhuk's `⟨cover⟩` notation and "stable under σ" are used before their interaction with
   quotients is pinned down.** In particular `σ` irreducible on `A` iff `0` irreducible on `A/σ`
   (`main.tex:1387`) is asserted with "Notice that…" — it is the correspondence theorem plus the
   fact that σ-stable subalgebras of `A²` correspond to subalgebras of `(A/σ)²`. That is a real
   lemma and needs the congruence layer of §3 item 1 before it can even be stated.
