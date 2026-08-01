# Mathlib probe: non-algebraic layers for the CSP Dichotomy formalization

**Mathlib checked:** `/home/alvaro/claude/zhuk-lean/.lake/packages/mathlib`, commit `905b95818eb32af7874a58b427f50c1711a5e96c` (2026-07-28, "chore: bump toolchain to v4.32.2"), toolchain `leanprover/lean4:v4.32.2`, 8264 `.lean` files.
All decl names and paths below were read out of the source, not recalled.

---

## 0. Executive verdict (read this first)

Four of the five requested layers are in good shape. One is a wall.

| Layer | Verdict |
|---|---|
| 1. Computability / complexity | **The complexity half of the dichotomy is not formalizable on top of Mathlib.** There is no P, no NP, no NP-completeness, no polynomial-time reduction, and no SAT. What little exists (`Turing.TM2ComputableInPolyTime`) is not even closed under composition — that is an open `proof_wanted` in Mathlib itself. |
| 2. Finite combinatorics | **HAVE**, essentially everything, with no glue needed. |
| 3. Graph theory / connectivity / linkedness | **HAVE**, with ~20 lines of glue. `Relation.reflTransGen_symmGen` is the exact lemma you want. |
| 4. Abelian groups / `ZMod` | **PARTIAL → mostly HAVE.** All the heavy structural results exist. Missing: a *notion of dimension for a product of `ZMod q_i` with mixed primes*, and the "codimension 1 ⟺ kernel of a single linear equation" bridge. Both small-to-medium. |
| 5. Free / term algebras, clones, `m`-ary term operations | **MISSING as such, but the substrate exists.** `FirstOrder.Language.Term` + `Substructure.closure` + `Setoid.completeLattice` cover ~60% of what is needed. There is **zero** universal-algebra-for-CSP content (no WNU, Taylor, Maltsev, majority, clone, polymorphism). |

---

## 1. Capability table

Legend: **HAVE** = usable directly; **PARTIAL** = core exists, named glue missing; **MISSING** = nothing.

### 1.1 Computability and complexity

| Item | Status | Where |
|---|---|---|
| Turing machines TM0 / TM1 / TM2 | HAVE | `Mathlib/Computability/TuringMachine/PostTuringMachine.lean` (`Turing.TM0`, `Turing.TM1`), `.../StackTuringMachine.lean` (`Turing.TM2`), `.../Tape.lean`, `.../Config.lean`. (Top-level `Mathlib/Computability/TuringMachine.lean`, `TMComputable.lean`, `TMConfig.lean`, `TMToPartrec.lean`, `PostTuringMachine.lean`, `Tape.lean`, `Primrec.lean` are all 10-line `deprecated_module` shims as of 2026-02/03; import the `TuringMachine/` subdirectory.) |
| `Partrec`, `Computable`, `Primrec`, `Nat.Partrec.Code` | HAVE | `Mathlib/Computability/Partrec.lean`, `Mathlib/Computability/Primrec/Basic.lean`, `Mathlib/Computability/PartrecCode.lean`, `Mathlib/Computability/Halting.lean` |
| `Encodable`, `Denumerable`, `Primcodable` | HAVE | `Mathlib/Logic/Encodable/Basic.lean:52`, `Mathlib/Logic/Denumerable.lean:33`, `Mathlib/Computability/Primrec/Basic.lean:132` |
| Binary encodings of types (`Encoding`, `FinEncoding`) | HAVE | `Mathlib/Computability/Encoding.lean:40` (`Computability.Encoding`), `:214` (`FinEncoding`), `:133` `encodingNatBool`, `:191` `encodingList`, `:202` `encodingProd` |
| Simulation TM2 ⟶ `Partrec` | HAVE | `Mathlib/Computability/TuringMachine/ToPartrec.lean` (1285 lines) |
| Recursion-theoretic many-one / one-one reductions and degrees | HAVE | `Mathlib/Computability/Reduce.lean`: `ManyOneReducible` (`≤₀`, `:41`), `OneOneReducible` (`≤₁`, `:76`), `ManyOneDegree` (`:309`), `ManyOneEquiv` (`:139`). **These are computable-in-the-limit reductions, not polytime.** |
| Turing degrees, relative computability | HAVE | `Mathlib/Computability/TuringDegree.lean`, `Mathlib/Computability/RecursiveIn.lean` |
| **"runs in time `t(n)`"** | PARTIAL | `Turing.TM2OutputsInTime` (`Mathlib/Computability/TuringMachine/Computable.lean:135`), `Turing.TM2ComputableInTime` (`:166`). Time = number of `TM2.step` applications. |
| **"runs in polynomial time"** | PARTIAL / unusable | `Turing.TM2ComputableInPolyTime` (`Mathlib/Computability/TuringMachine/Computable.lean:179`). Fields: `tm : FinTM2`, `inputAlphabet`, `outputAlphabet`, `time : Polynomial ℕ`, `outputsFun : ∀ a, TM2OutputsInTime tm (…ea a…) (some (…eb (f a)…)) (time.eval (ea a).length)`. Applies only to **total functions `α → β`**, never to languages/decision problems. |
| **Composition of two polytime TM2s** | **MISSING (`proof_wanted`)** | `Mathlib/Computability/TuringMachine/Computable.lean:284` — `proof_wanted TM2ComputableInPolyTime.comp … : Nonempty (TM2ComputableInPolyTime eα eγ (g ∘ f))`. Stated, never proved. |
| **Complexity class as a first-class object** | **MISSING** | grep over all of `Mathlib/` for `complexityClass`, `PolyTime`, `polyTime`: only the `TM2ComputableInPolyTime` hits above and one false positive in `Mathlib/Analysis/Polynomial/MahlerMeasure.lean:350` ("sup norm of the polynomial times the square…"). |
| **P** | **MISSING** | Only reference: a comment, `Mathlib/Computability/TuringMachine/ToPartrec.lean:48`: *"but in anticipation of the complexity class P, the simulation is actually polynomial-time as well."* No definition anywhere. |
| **NP** | **MISSING** | grep -w for `NP`, `coNP`, `NPComplete`, `NPHard`, `PSPACE` over `Mathlib/`: the only hits are variable names `NP` in `Mathlib/ModelTheory/Bundled.lean:66`, `Mathlib/ModelTheory/Fraisse.lean:332-343`, `Mathlib/ModelTheory/Semantics.lean:1122`. |
| **NP-completeness / NP-hardness** | **MISSING** | — |
| **Polynomial-time many-one reduction (`≤_p`)** | **MISSING** | — |
| **SAT / 3-SAT / NAE-3-SAT as decision problems** | **MISSING** | `Mathlib/Tactic/Sat/FromLRAT.lean` is an LRAT-certificate *importer* (a macro turning a SAT-solver proof into a Lean term), not complexity theory. `Mathlib/ModelTheory/Satisfiability.lean` is first-order satisfiability/compactness, unrelated. `Mathlib/Tactic/ITauto.lean:710` mentions "classical SAT solver" in a docstring. |
| **Cook–Levin** | **MISSING** | — |
| CSP as a formal object | PARTIAL, and not the one we need | `Mathlib/Combinatorics/Optimization/ValuedCSP.lean` (185 lines) — **Valued** CSP only. `ValuedCSP D C := Set (Σ n, (Fin n → D) → C)` (`:44`), `ValuedCSP.Term` (`:50`), `ValuedCSP.Instance` (`:66`), `evalSolution` (`:70`), `IsOptimumSolution` (`:75`), `FractionalOperation` (`:90`), `FractionalOperation.IsFractionalPolymorphismFor` (`:119`), `IsSymmetric` (`:124`), and one real theorem `Function.HasMaxCutProperty.forbids_commutativeFractionalPolymorphism` (`:155`). **No decision CSP, no `Pol`/`Inv`, no ordinary polymorphism, no complexity.** Not a useful base for us — the arity bookkeeping is `Fin n → D`, which we would want anyway, but that is 3 lines. |

### 1.2 Finite combinatorics

Everything requested is HAVE. Nothing needs building.

| Item | Status | Decl / path |
|---|---|---|
| `Finset`, `Fintype`, `Finite` | HAVE | `Mathlib/Data/Finset/*` (49 files), `Mathlib/Data/Fintype/*` |
| Decidable equality on finite types, decidable ∀/∃ over `Fintype` | HAVE | `Fintype.decidablePiFintype` (`Mathlib/Data/Fintype/Defs.lean:204`), `Fintype.decidableForallFintype` (`:209`), `Fintype.decidableExistsFintype` (`:213`) |
| `Finset.sup` / `Finset.inf` over `SemilatticeSup`+`OrderBot` | HAVE | `Finset.sup` (`Mathlib/Data/Finset/Lattice/Fold.lean:44`), plus `sup_insert`, `sup_union`, `sup_mono`, `sup_induction` (`:216`), `sup_eq_iSup` (`:288`), `sup_id_eq_sSup` (`:294`), `sup_set_eq_biUnion` (`:304`) |
| `Finset.sup'` / `inf'` (nonempty, no `⊥` needed) | HAVE | `Finset.sup'` (`Mathlib/Data/Finset/Lattice/Fold.lean:515`), `sup'_le_iff` (`:541`), `le_sup'` (`:547`) |
| Well-founded recursion on `Finset` cardinality | HAVE | `Finset.strongInduction` (`Mathlib/Data/Finset/Card.lean:838`, `termination_by s => #s`), `strongInductionOn` (`:852`, `@[elab_as_elim]`), `strongInduction_eq` (`:846`), `Finset.case_strong_induction_on` (`:862`), `Finset.Nonempty.strong_induction` (`:876`), `Finset.lt_wf` (`:921`) |
| Downward induction on `Finset` (needed for "maximal reduction" arguments) | HAVE | `Finset.strongDownwardInduction` (`Mathlib/Data/Finset/Card.lean:892`, `termination_by s => n - #s`), `strongDownwardInductionOn` (`:910`) |
| Strong induction on a finite lattice / poset | HAVE | `Finite.wellFounded_of_trans_of_irrefl` (used e.g. `Mathlib/RingTheory/Artinian/Module.lean:126`, `Mathlib/Topology/NoetherianSpace.lean:150`); `WellFoundedLT` / `WellFoundedGT` API in `Mathlib/Order/WellFounded.lean` |
| Meet/join-irreducible elements, coatoms | HAVE | `InfIrred` (`Mathlib/Order/Irreducible.lean:139`), `InfPrime` (`:144`), `SupIrred` (`:49`), `exists_infIrred_decomposition` (`:189`), `InfIrred.finset_inf_eq` (`:179`); `IsCoatom` (`Mathlib/Order/Atoms.lean`), `IsCoatomic (Submodule R M)` for `[Module.Finite R M]` (`Mathlib/RingTheory/Finiteness/Basic.lean:237`) |
| Complete lattice of equivalence relations | HAVE | `Setoid.completeLattice` (`Mathlib/Data/Setoid/Basic.lean:185`), `Setoid.ker` (`:79`), `Setoid.sup_eq_eqvGen` (`:263`), `Setoid.sSup_eq_eqvGen` (`:276`), `Setoid.gi` (`:312`, Galois insertion `EqvGen.setoid ⊣ (⇑)`), `Setoid.eqvGen_eq` (`:253`), `Setoid.map_of_le` (`:230`) |
| `Finset.piInduction`, `Finset.powerset`, `Finset.filter`, `Finset.image` | HAVE | `Mathlib/Data/Finset/PiInduction.lean`, `Powerset.lean`, `Filter.lean`, `Image.lean` |

**Not found: `Fintype (Setoid α)` / `Finite (Setoid α)` instance for finite `α`.** This is a MISSING trivial item (grep for `Fintype (Setoid`, `Finite (Setoid`, `instFintypeSetoid` returns nothing). If we want the congruence lattice of a finite algebra to be a `Fintype`, we build it (`Setoid α ↪ (α → α → Prop)` + `Finite.of_injective`). ~5 lines.

### 1.3 Graph theory / connectivity / "linked"

| Item | Status | Decl / path |
|---|---|---|
| `SimpleGraph` | HAVE | `Mathlib/Combinatorics/SimpleGraph/Basic.lean` |
| Build a graph from an arbitrary relation | HAVE | `SimpleGraph.fromRel` (`Mathlib/Combinatorics/SimpleGraph/Basic.lean:133`), `fromRel_adj` (`:137`): `Adj v w ↔ v ≠ w ∧ (r v w ∨ r w v)` — **note it silently deletes self-loops**, harmless for reachability but the `v ≠ w` shows up in every proof. |
| `Walk`, `IsPath`, `IsTrail`, `IsCycle` | HAVE | `Mathlib/Combinatorics/SimpleGraph/Walk/*` (Basic, Decomp, Maps, Operations, Subwalks, Traversal, Counting), `Paths.lean` |
| `Reachable` | HAVE | `SimpleGraph.Reachable` (`Mathlib/Combinatorics/SimpleGraph/Connectivity/Connected.lean:52`) `:= Nonempty (G.Walk u v)`; `Reachable.refl/symm/trans` (`:80/:85/:92`); `reachable_is_equivalence` (`:164`); `reachableSetoid` (`:225`) |
| `Reachable = ReflTransGen Adj` | HAVE | `SimpleGraph.reachable_iff_reflTransGen` (`:96`), `reachable_eq_reflTransGen` (`:108`), `reachable_fromEdgeSet_fromRel_eq_reflTransGen` (`:119`, hypothesis `Std.Symm r`) |
| `Preconnected` / `Connected` | HAVE | `:228` / `:314` (`Connected` is a structure: `preconnected` + `[Nonempty V]`), `connected_iff_exists_forall_reachable` (`:318`) |
| `ConnectedComponent` | HAVE | `:390` `:= Quot G.Reachable`; `connectedComponentMk` (`:393`); `ConnectedComponent.supp` (`:548`) with `SetLike` instance (`:563`); `supp_injective` (`:552`); `pairwise_disjoint_supp_connectedComponent` (`:722`); `iUnion_connectedComponentSupp` (`:731`); `ConnectedComponent.map` (`:475`); `toSimpleGraph` (`:643`), `connected_toSimpleGraph` (`:685`) |
| **Decidable** reachability / connectedness, `Fintype` of components | HAVE | `Mathlib/Combinatorics/SimpleGraph/Connectivity/Finite.lean:56` `instance : DecidableRel G.Reachable` (needs `[DecidableEq V] [Fintype V] [DecidableRel G.Adj]`), `:60` `instance : Fintype G.ConnectedComponent`, `:63` `Decidable G.Preconnected`, `Decidable G.Connected`, `instDecidableMemSupp` |
| `Relation.ReflTransGen` on an arbitrary relation | HAVE | `Mathlib/Logic/Relation.lean:332` (inductive), with `.trans` (`:440`), `.single` (`:445`), `.head` (`:451`), `head_induction_on` (`:468`), `trans_induction_on` (`:480`), `cases_head_iff` (`:492`), `Std.Symm` instance when `r` is symmetric (`:456`) |
| `Relation.EqvGen`, `Relation.SymmGen`, `Relation.ReflGen`, `Relation.TransGen` | HAVE | `Mathlib/Logic/Relation.lean:353/:349/:340/(TransGen in core)`; `EqvGen.setoid` (`:809`); `EqvGen.is_equivalence` (`:798`) |
| **`ReflTransGen (SymmGen r) = EqvGen r`** | HAVE — *this is the lemma for "linked"* | `Relation.reflTransGen_symmGen` (`Mathlib/Logic/Relation.lean:878`). Companion: `EqvGen.eqvGen_eq_reflTransGen` for symmetric `r` (`:874`), `reflTransGen_le_eqvGen` (`:846`) |
| `DecidableRel (Relation.ReflTransGen r)` for finite types | **MISSING** | grep returns nothing. Trivial to obtain by transporting through `SimpleGraph.fromRel` + the `DecidableRel G.Reachable` instance above, or `Classical.dec` if we don't care about computation. **Small.** |

**Assessment for our "linked" instance.** Zhuk's graph is on `Σ x : Var, D x` (pairs `(variable, value)`) with `(x,a) ~ (y,b)` iff some constraint's projection onto `(x,y)` contains `(a,b)`. That relation is symmetric by construction. Two clean routes:

* **Route A (recommended):** define `Linked` directly as `Relation.ReflTransGen R` on `Σ x, D x` and use `Relation.reflTransGen_symmGen` / `eqvGen_eq_reflTransGen` for the equivalence-relation view. Zero graph-theory imports; the `v ≠ w` in `fromRel` never bites; decidability by transport when needed.
* **Route B:** `SimpleGraph.fromRel R` and use `Connected` / `ConnectedComponent` / `DecidableRel Reachable`. Buys the connected-component machinery for free (useful for the *not-linked ⟹ split into linked subinstances* step, `main.tex:660-665`).

Suggest Route A as the definition and a one-lemma bridge to Route B (`(SimpleGraph.fromRel R).Reachable = Relation.EqvGen R` for symmetric `R`) to import the component API. That bridge lemma is **not** in Mathlib (`reachable_fromEdgeSet_fromRel_eq_reflTransGen` is about `fromEdgeSet (Sym2.fromRel _)`, a different graph); ~15 lines.

### 1.4 Abelian groups, `ZMod`, affine subspaces

| Item | Status | Decl / path |
|---|---|---|
| `ZMod n`, `DecidableEq`, `Fintype`, cardinality | HAVE | `Mathlib/Data/ZMod/Defs.lean:146` `ZMod.decidableEq`, `:158` `ZMod.fintype`, `:166` `ZMod.card` |
| `Field (ZMod p)` for `[Fact p.Prime]` | HAVE | `Mathlib/Algebra/Field/ZMod.lean:30` |
| Products `∀ i, ZMod (q i)` as `AddCommGroup` | HAVE | `Pi.addCommGroup` |
| **`AddSubgroup M ≃o Submodule (ZMod n) M`** | HAVE — *load-bearing* | `AddSubgroup.toZModSubmodule` (`Mathlib/Algebra/Module/ZMod.lean:102`), an **order isomorphism**. Plus `coe_toZModSubmodule` (`:112`), `mem_toZModSubmodule` (`:113`), round-trip simp lemmas (`:116`, `:121`). This is exactly "subgroups of an elementary abelian `p`-group = `𝔽_p`-subspaces". |
| `Module (ZMod n)` from `∀ x, n • x = 0` | HAVE | `AddCommGroup.zmodModule` (`Mathlib/Algebra/Module/ZMod.lean:44`), `AddCommMonoid.zmodModule` (`:25`), `QuotientAddGroup.zmodModule` (`:53`) |
| Additive homs are `ZMod n`-linear automatically | HAVE | `AddMonoidHom.toZModLinearMap` (`Mathlib/Algebra/Module/ZMod.lean:81`), `toZModLinearMapEquiv` (`:90`), `ZMod.map_smul` (`:63`), `ZMod.smul_mem` (`:67`) |
| Structure theorem for finite abelian groups | HAVE | `AddCommGroup.equiv_directSum_zmod_of_finite` (`Mathlib/GroupTheory/FiniteAbelian/Basic.lean:135`), `equiv_directSum_zmod_of_finite'` (`:151`), `equiv_free_prod_directSum_zmod` (`:119`), multiplicative versions `:174`, `:184` |
| Primary (Sylow / `p`-primary) decomposition | HAVE | `CommGroup.primaryComponent` (`Mathlib/GroupTheory/Torsion.lean:376`), `primaryComponent.disjoint` (`:251`), `primaryComponent.isPGroup` (`:397`); module version `Submodule.primaryComponent` (`Mathlib/Algebra/Module/Torsion/PrimaryComponent.lean:50`) with `iSup_primaryComponent_eq_top` (`:140`) and `iSupIndep_primaryComponent` (`:175`) |
| Subgroup index / Lagrange | HAVE | `Subgroup.card_mul_index` (`Mathlib/GroupTheory/Index.lean:290`) |
| Group of prime order is cyclic; cyclic `≃+ ZMod n` | HAVE | `isCyclic_of_prime_card` (`Mathlib/GroupTheory/SpecificGroups/Cyclic/Basic.lean:169`), `zmodAddEquivOfGenerator : ZMod n ≃+ G` (`Mathlib/GroupTheory/SpecificGroups/Cyclic.lean:407`), `IsAddCyclic` ↔ `IsCyclic` transfer (`Cyclic/Basic.lean:59-69`) |
| Goursat's lemma (subdirect subgroups of `A × B`) | HAVE | `Subgroup.goursat` (`Mathlib/GroupTheory/Goursat.lean:128`), `goursat_surjective` (`:104`), `goursatFst/Snd` (`:43/:56`); submodule version `Mathlib/LinearAlgebra/Goursat.lean:103`, `:75` |
| `finrank`, rank-nullity, codimension of a submodule | HAVE | `Module.finrank` (`Mathlib/LinearAlgebra/Dimension/Finrank.lean:62`), `Submodule.finrank_quotient_add_finrank` (`Mathlib/LinearAlgebra/Dimension/RankNullity.lean:247`), `Module.finrank_quotient_add_finrank_le` (`Mathlib/LinearAlgebra/Dimension/Finite.lean:413`) |
| `IsCoatom` kernel of a surjection onto a simple module | HAVE | `LinearMap.isCoatom_ker_of_surjective` (`Mathlib/RingTheory/SimpleModule/Basic.lean:517`), `Submodule.isCoatom_comap_or_eq_top` (`Mathlib/LinearAlgebra/Span/Basic.lean:574`) |
| `AffineSubspace k P` (affine subspaces over a **ring**) | HAVE but **wrong shape for us** | `Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Defs.lean:149` `structure AffineSubspace (k) (P)` with `[Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]`; `direction` (`:236`), `mk' p direction` (`:388`), `vectorSpan` (`:63`), `spanPoints` (`:107`), `CompleteLattice` and `SetLike` instances. **Requires a single base ring `k`.** Zhuk's ambient object is `∏ ZMod q_i` with *distinct* primes `q_i`, which is not a module over any single `ZMod p`. |
| **"affine subspace of `∏ ZMod q_i`" (mixed primes)** | **MISSING** | Must be stated as "a coset of an `AddSubgroup`": `∃ (H : AddSubgroup G) (c : G), S = c +ᵥ (H : Set G)`. **Small.** |
| **"dimension" of `∏ ZMod q_i` and of its subgroups** | **MISSING**, and *undefined in the source too* — see §4 | Best bespoke definition: `dim G := Ω(Nat.card G)` (`(Nat.card G).factorization.sum fun _ k => k`, i.e. `Nat.primeFactorsList` length). Additivity `dim H + dim (G ⧸ H) = dim G` follows immediately from `Subgroup.card_mul_index` + `Nat.factorization_mul`. **Small–medium.** |
| **"codimension 1 ⟺ solution set of a single linear equation"** | **MISSING** | For `G` a finite abelian group of squarefree exponent and `H ≤ G` with `G.index H = p` prime: `G ⧸ H` has order `p` ⟹ cyclic (`isCyclic_of_prime_card`) ⟹ `≃+ ZMod p` (`zmodAddEquivOfGenerator`) ⟹ `H = ker φ` for a surjective `φ : G →+ ZMod p`. All ingredients present. **Small–medium** (est. 100–200 lines with the coset/affine version). |
| Solving a linear system over `ZMod p` | HAVE (the math) | `Mathlib/LinearAlgebra/Matrix/*`, `Mathlib/Data/Matrix/Rank.lean`; Gaussian elimination as an *algorithm with a complexity bound*: MISSING (see §2). |

### 1.5 Free algebras, term algebras, `m`-ary term operations, clones

| Item | Status | Decl / path |
|---|---|---|
| First-order languages with function symbols of each arity | HAVE | `FirstOrder.Language` (`Mathlib/ModelTheory/Basic.lean`), fields `Functions : ℕ → Type u`, `Relations : ℕ → Type v` |
| **Absolutely free / term algebra** | HAVE (this *is* it) | `FirstOrder.Language.Term α` (`Mathlib/ModelTheory/Syntax.lean:79`), inductive with `var : α → Term α` and `func : L.Functions n → (Fin n → Term α) → Term α`. `DecidableEq` instance (`:88`); `varFinset` (`:104`); `relabel` (`:117`); `subst` (`:246`, term substitution — this is the free-algebra universal property in disguise); `Functions.term` (`:179`) |
| Interpretation of terms in an algebra | HAVE | `Language.Structure` class (`Mathlib/ModelTheory/Basic.lean`) with `funMap : L.Functions n → (Fin n → M) → M`; `Term.realize` (`Mathlib/ModelTheory/Semantics.lean:71`), `realize_var` (`:76`), `realize_func` (`:79`), `realize_subst` (`:124`) |
| Subalgebra generated by a set (`Sg_A(R)` in Zhuk) | HAVE | `Language.Substructure` (`Mathlib/ModelTheory/Substructures.lean:96`), `SetLike` (`:107`), `CompleteLattice` (`:213`), `Substructure.closure` as a `LowerAdjoint` (`:231`), `closure_le` (`:256`), `Term.realize_mem` (`:136`), and crucially **`coe_closure_eq_range_term_realize`** (`:268`) — "generated subalgebra = image of all terms". `mem_closure_iff_exists_term` (`:284`) |
| Homomorphisms / embeddings / isos of structures | HAVE | `Language.Hom` (`→[L]`), `Embedding` (`↪[L]`), `Equiv` (`≃[L]`) in `Mathlib/ModelTheory/Basic.lean` |
| Quotient of a structure by a congruence | PARTIAL | `Language.Prestructure` (`Mathlib/ModelTheory/Quotients.lean:39`) — a `Setoid M` plus `fun_equiv : ∀ {n} {f} (x y), x ≈ y → funMap f x ≈ funMap f y`. That *is* the congruence condition, but it is packaged as a `class` on a fixed `Setoid`, **not as a bundled `Con` type with a lattice structure**. `quotientStructure` (`:48`), `funMap_quotient_mk'` (`:56`), `Term.realize_quotient_mk'` (`:70`). |
| **Bundled congruence lattice `Con A` of an algebra** | **MISSING** | `Mathlib/GroupTheory/Congruence/*` is monoid/group-specific. Build a bespoke `structure AlgCon` (a `Setoid A` + compatibility with the single basic operation), `SetLike`, `CompleteLattice` via `Setoid.completeLattice` restricted. **Small–medium.** |
| **`L.Structure` on a product `∀ i, M i`** | **MISSING** | grep for `L.Structure (∀`, `Pi.*Structure` in `Mathlib/ModelTheory/` returns only `Ultraproducts.lean:74`. **~5 lines** to add (`funMap f x i := funMap f (fun k => x k i)`). Needed for every `A^n`, `A_1 × … × A_m`, `A^(A^m)` in the paper. |
| **Clone of an algebra / `Clo(A)` / composition law** | **MISSING** | grep for `clone`, `Post's lattice`, `term operation`, `varieties of algebras`: nothing. |
| **Polymorphism / `Pol` / `Inv` / Galois connection** | **MISSING** | Only `FractionalOperation.IsFractionalPolymorphismFor` (`Mathlib/Combinatorics/Optimization/ValuedCSP.lean:119`), which is about *fractional* polymorphisms of *valued* CSPs. |
| **WNU / Taylor / Maltsev / majority / minority / idempotent operation** | **MISSING** | grep -i over all of `Mathlib/` for `\bWNU\b`, `weak near-unanimity`, `Taylor operation`, `Siggers`, `Maltsev`/`Mal'cev`/`Malcev`, `majority operation`, `minority operation`, `idempotent operation`: **zero hits.** |
| **Free algebra in a variety `F_V(x_1,…,x_m)`** | **MISSING** | Nothing. `Mathlib/Algebra/FreeAlgebra.lean` is the free *associative unital `R`-algebra*; `FreeMonoid`, `FreeGroup`, `FreeMagma`, `FreeAbelianGroup` are all specific varieties. |
| **"the algebra of `m`-ary term operations"** | **MISSING** | The construction (Brady, `csp.tex:631-648`) is: view each `m`-ary term operation `t^A : A^m → A` as an element of `A^{A^m}`; then `F_{V(A)}(x_1,…,x_m) ≅` the subalgebra of `A^{A^m}` generated by the `m` projections. Given the missing Pi-structure instance above, this is `Substructure.closure L (Set.range (fun i : Fin m => (· i : (Fin m → A) → A)))`. **~1 day once the Pi instance exists.** |

---

## 2. The P/NP situation, stated bluntly

**Mathlib contains no complexity theory.** Not "an incomplete version" — none. Specifically:

1. **There is no definition of P, of NP, of any complexity class, or of NP-completeness.** The only mention of the letter "P" as a class is a *comment* in `Mathlib/Computability/TuringMachine/ToPartrec.lean:48`.

2. **There is no polynomial-time reduction.** `Mathlib/Computability/Reduce.lean` has `ManyOneReducible` (`≤₀`) and `OneOneReducible` (`≤₁`), which are *computable* reductions with no resource bound. They are useless for hardness statements: under `≤₀`, every decidable problem reduces to every other nontrivial decidable one, so every finite-domain CSP is `≤₀`-equivalent to every other. Using them would make the dichotomy vacuous.

3. **The one polytime notion that exists is broken for our purposes.**
   `Turing.TM2ComputableInPolyTime` (`Mathlib/Computability/TuringMachine/Computable.lean:179`) is a *structure* attached to a **total function `f : α → β`** and a specific `FinTM2` machine. Two fatal problems:
   - It is not a predicate on languages, so "the decision problem CSP(Γ) is in P" is not expressible without wrapping (that wrapping is easy: `f : Instance → Bool`).
   - **It is not known (in Mathlib) to be closed under composition.** `Mathlib/Computability/TuringMachine/Computable.lean:284` is literally
     ```
     proof_wanted TM2ComputableInPolyTime.comp … : Nonempty (TM2ComputableInPolyTime eα eγ (g ∘ f))
     ```
     with a prose sketch. A "complexity class" that isn't closed under composition supports no reduction argument at all. Everything downstream (transitivity of `≤_p`, "NP-hard + in P ⟹ P = NP", padding, gadget composition) needs this.

4. **NAE-3-SAT's NP-hardness, which Zhuk's hardness proof uses as its only complexity input, does not exist and is far away.**
   `2005.00593.txt:838-846`: *"Let NAE3 be the ternary relation on {0,1} containing all tuples except for (0,0,0) and (1,1,1). Consider an instance I of CSP({NAE3}), which is known to be an NP-hard problem [27]."* Reference [27] is Schaefer. Getting that in Lean requires **Cook–Levin** plus a chain of gadget reductions. Cook–Levin has been formalized once, in Coq (Gäher–Kunze), at a scale of several person-years and tens of thousands of lines. Nothing comparable exists in Lean.

5. **The tractability half is equally out of reach in the standard model.** "CSP(Γ) is solvable in polynomial time" requires an executable algorithm, a machine model, and a runtime analysis. Zhuk's algorithm (`main.tex:684-716`, `SolveLinear`, plus `Solve`, `ForceConsistency`, `CheckCC`, …) is recursive on domain size with an inner loop over constraints and a `SolveLinear` loop that decrements a dimension. A runtime proof for it against a TM2 model is not a project; it is several projects.

**Consequence for the route decision.** Any plan whose top-level statement is

> `∀ Γ, (∃ w, IsWNU w ∧ w preserves Γ) → CSP(Γ) ∈ P` ∧ `(¬∃ …) → NPComplete (CSP Γ)`

is, on today's Mathlib, a research programme in complexity theory *bolted onto* a research programme in universal algebra. **The two must be decoupled.** See §3.1 for the three viable framings.

---

## 3. Build-vs-avoid recommendation, item by item

### 3.1 Complexity theory — **AVOID. Do not build P/NP.**

Cost if built: **research-project** (multi-person-year), and it is *entirely orthogonal* to the mathematics of Zhuk's proof. Recommendation: state the theorem in a complexity-free form and, optionally, add a thin *axiomatic* complexity interface on top.

Three framings, in increasing ambition. **Pick (A) for the blueprint; leave (B) as a documented, optional extension; do not attempt (C).**

**(A) Complexity-free core (recommended).**
Formalize the mathematical content, which is what the paper actually proves:

- *Tractable side (the real theorem):* for `Γ` preserved by an idempotent special WNU `w`, **every cycle-consistent, irreducible, non-fragmented instance of CSP(Γ) has a solution**, plus the reduction machinery (strong subuniverses, linear congruences, bridges, `THMCodimensionOneTheorem`). This is 100% of `main.tex` §2–§3, `StrongSubalgebras.tex`, `XYSymmetric.tex`, and `necessaryClaims.tex`. **No complexity appears anywhere in it.**
- *Hard side:* `Γ` without a WNU polymorphism admits a pp-definition of a "WNU-blocker" relation (`2005.00593.txt:828-846`, Theorem 4.14 + Theorem 5.5), i.e. **a pp-interpretation of NAE3 in Γ**. That statement is purely algebraic and fully formalizable.
- Then the dichotomy is a *corollary in prose*: "combined with the (unformalized) facts that NAE-3-SAT is NP-hard and pp-definitions give polytime reductions". Blueprint should say this in exactly those words.

Cost: **zero extra**; it is just honest scoping.

**(B) Abstract complexity interface (optional, cheap, and worth it).**
Introduce opaque parameters and the axioms actually used, so the top-level statement *looks* like the dichotomy and the debt is explicit and auditable:

```
variable (InP NPHard : (∀ {D : Type} [Fintype D], Set (Instance D)) → Prop)
variable (h_nae : NPHard (CSP nae3))
variable (h_ppred : ∀ Γ Δ, PPInterprets Γ Δ → NPHard (CSP Δ) → NPHard (CSP Γ))
```

Then `Theorem dichotomy : ... → NPHard (CSP Γ)` is a real theorem about the abstract interface, with all complexity content isolated in two named hypotheses. Cost: **small** (a day). Value: the blueprint's top-level statement is recognizable, and the gap is one paragraph rather than diffuse.

Warning to record in the blueprint: this is *not* a proof of the dichotomy conjecture. It is a proof modulo two clearly named imports.

**(C) Bespoke cost model (do not attempt now; mention as future work).**
Define the algorithm as a Lean function over an explicit `Instance` representation, thread an explicit step counter (or fuel), prove termination and correctness, and prove `steps ≤ p(size)` for an explicit polynomial `p` — a unit-cost structural-recursion model, no Turing machines. This is *feasible in principle* (Mathlib gives `Polynomial ℕ`, `Nat` arithmetic, `Finset.card` for sizes) and would let one honestly say "polynomial in this cost model". Cost: **large** (comparable to the whole algebraic development), and it still would not connect to `Turing.TM2ComputableInPolyTime` without `TM2ComputableInPolyTime.comp`.

**Do not build:** `P`, `NP`, `NPComplete`, `≤_p`, `Cook–Levin`, or `TM2ComputableInPolyTime.comp`. Each is at least "large"; the chain is "research project".

### 3.2 Finite combinatorics — **use Mathlib as-is.**

Nothing to build. Two ~5-line additions:
- `Finite (Setoid α)` for `[Finite α]` (**small**, ~5 lines).
- Anything about `Finset.strongDownwardInduction` ergonomics — Mathlib's version has an awkward `#t₂ ≤ n` side condition; for "maximal 1-consistent reduction" arguments (`2005.00593.txt:911-933`) it may be cleaner to use `Finite.wellFounded_of_trans_of_irrefl` on the reduction order directly. **Small.**

### 3.3 Graph theory / linkedness — **use Mathlib, add ~20 lines of glue.**

Build (all **small**):
1. `def Linked (R : α → α → Prop) := Relation.ReflTransGen R` specialized to `Σ x, D x`, plus the symmetric-relation lemma set (mostly `Relation.reflTransGen_symmGen`, `EqvGen.eqvGen_eq_reflTransGen` do it).
2. `(SimpleGraph.fromRel R).Reachable = Relation.EqvGen R` for symmetric `R` — **not in Mathlib** (`reachable_fromEdgeSet_fromRel_eq_reflTransGen` is a different graph). ~15 lines. Buys `ConnectedComponent`, `Fintype ConnectedComponent`, `DecidableRel Reachable`.
3. `DecidableRel (Relation.ReflTransGen R)` for `[Fintype α] [DecidableRel R]` via (2). ~5 lines.

**Do not build:** anything about walks, paths, bridges, cycles — Mathlib has more than we need. Note the paper's "path" (`2005.00593.txt`, §5.4) is a *walk* in Mathlib's sense (repeats allowed), so use `Reachable`/`ReflTransGen`, never `IsPath`.

### 3.4 Abelian groups / `ZMod` — **use Mathlib, build a thin "mixed-prime linear algebra" layer.**

Build:
1. **`AffineCoset` predicate** for subsets of an arbitrary finite abelian `G`: `IsCoset S ↔ ∃ (H : AddSubgroup G) (c : G), S = c +ᵥ (H : Set G)`, closed under intersection (nonempty case), image, preimage. **Small**, ~150 lines. *Avoid `AffineSubspace`*: it needs a single base ring and does not apply to `∏ ZMod q_i` with mixed primes.
2. **`dim` for finite abelian groups of squarefree exponent.** Define `dim G := (Nat.card G).primeFactorsList.length` (= `Ω(|G|)`). Prove `dim H + dim (G ⧸ H) = dim G` from `Subgroup.card_mul_index` + `Nat.factorization` multiplicativity; prove `dim (∏ ZMod q_i) = k` for primes `q_i`; prove `dim H < dim G ↔ H < G`. **Small–medium**, ~200 lines. See §4 for why this needs a *definition* — the paper does not give one.
3. **Codimension-1 ⟺ one linear equation.** For `H ≤ G` with `H.index = p` prime: `∃ φ : G →+ ZMod p`, `Function.Surjective φ`, `H = φ.ker`. Ingredients all present (`isCyclic_of_prime_card`, `zmodAddEquivOfGenerator`, `QuotientAddGroup.ker_mk'`). Plus the affine version. **Small–medium**, ~200 lines.
4. **`p`-part decomposition of `∏ ZMod q_i`** to justify "the equation only involves coordinates with `q_i = p`" (Zhuk's footnote at `main.tex:678-680`). `CommGroup.primaryComponent` + `primaryComponent.disjoint` + `AddSubgroup.toZModSubmodule` give it. **Medium**, ~300 lines.

**Do not build:** the structure theorem for finite abelian groups (HAVE), Goursat (HAVE), rank-nullity (HAVE), `ZMod` field structure (HAVE), primary decomposition (HAVE).

### 3.5 Free / term algebras and `m`-ary term operations — **bespoke, on top of `ModelTheory`.**

The single most important architectural observation from this probe:

> **The whole of Zhuk 2404 works in a signature with exactly one operation.** `main.tex:1110-1121`: *"By `V_n` we denote the class of finite algebras `A = (A; w^A)` whose basic operation `w^A` is an idempotent special WNU operation."* And `Z_p` is the algebra `({0,…,p-1}; x_1+⋯+x_n mod p)`.

So we never need general many-sorted universal algebra. Two options:

**Option 1 (recommended): reuse `FirstOrder.Language` with a one-symbol language.**
```
def wnuLang (n : ℕ) : Language := ⟨fun k => PLift (PLift (k = n)), fun _ => Empty⟩
```
Then for free: `Term` (`Syntax.lean:79`) with `DecidableEq`, `Term.realize` (`Semantics.lean:71`), `Term.subst` (`Syntax.lean:246`), `Substructure` + `CompleteLattice` + `closure` (`Substructures.lean:96/213/231`), and — the payoff — **`Substructure.coe_closure_eq_range_term_realize` (`Substructures.lean:268`)**, which is exactly Zhuk's "`Sg_A(R)` = everything obtainable by applying terms to `R`".

Must add (all **small**):
- `instance : L.Structure (∀ i, M i)` — **~5 lines**, genuinely missing from Mathlib.
- `instance : L.Structure (M × N)` — ~5 lines.
- `structure AlgCon` (bundled congruence) + `SetLike` + `CompleteLattice`, on top of `Setoid.completeLattice` (`Mathlib/Data/Setoid/Basic.lean:185`) and `Language.Prestructure` (`Quotients.lean:39`). **Small–medium**, ~300 lines.
- `σ*` (the unique cover of a meet-irreducible congruence): `sInf {τ | σ < τ}`, well-defined by `InfIrred` (`Mathlib/Order/Irreducible.lean:139`) + finiteness. **Small**, ~80 lines.
- The `m`-ary term-operation algebra: `Substructure.closure (wnuLang n) (Set.range proj)` inside `A^(Fin m → A)`, plus its universal property. **Medium**, ~400 lines.

Risk of Option 1: `ModelTheory` carries relations, formulas, and a `u`/`v`/`u'` universe apparatus that we do not want; `Fin n → M` argument order can be noisy; there is no `Finite`/`Fintype` support at all for structures.

**Option 2: a bespoke `class NAlgebra (n : ℕ) (A : Type*) where op : (Fin n → A) → A`** and a hand-rolled nested inductive `Tm`. Cleaner statements, but you re-prove `closure`, the `CompleteLattice`, `coe_closure_eq_range_term_realize`, `DecidableEq` on terms, and the substitution lemmas. **Medium**, ~1000 lines, all of it duplicating Mathlib.

**Recommendation: Option 1, with a thin bespoke `abbrev` layer** (`A.op : (Fin n → A) → A := funMap …`) so downstream statements read like the paper. Cost of the whole layer: **medium**, est. 1500–2500 lines.

**Do not build:** general clones, the `Pol`/`Inv` Galois connection, or varieties/free algebras in general. `Pol`/`Inv` is needed only in the *hardness* half (`2005.00593.txt:838`, "By the Galois connection we know that `R` is pp-definable over `Γ'`") — and that half is being scoped out anyway (§3.1). If it is kept, `Pol`/`Inv` for a *finite* domain is **medium** (~600 lines; the Baker–Pixley/Geiger argument is a finite `Sg` computation over `A^{|A|^k}`), not research-scale.

---

## 4. Gaps, abuses of notation, and quantifier hazards found while probing

These are the items most likely to break a formalization. Flagged with source line numbers.

1. **"Dimension" of `∏ Z_{p_1} × ⋯ × Z_{p_m}` is never defined, and the `p_i` are distinct primes.** `main.tex:564` ("affine subspace … of dimension `m-1`"), `main.tex:689`, `:708`, `:723`, `:741`, `:748`, `:750`, `:4113`, `:4120`. There is no field over which this is a vector space. The intended meaning must be *composition length* = `Ω(|G|)` = number of cyclic factors. That is well-defined and additive, but it is a definition we must supply. **This must be pinned down in the blueprint before anything downstream is stated.**

2. **"Affine subspace of codimension 1 (the solution set of a single linear equation)"** — `main.tex:4026`. Over a mixed-prime product, a "linear equation" is only meaningful over a single `Z_p` and can only involve the coordinates `i` with `q_i = p`. Zhuk knows this and says so, but only in a **footnote to the algorithm**, not in the theorem: `main.tex:678-680`, *"The fact that different variables `y_i` take on values from different fields `Z_{p_i}` is not a problem as `J` may contain only variables on the same field."* The theorem statement `THMCodimensionOneTheorem` (`main.tex:4004-4027`) does **not** carry this qualification. **Formalization must state it explicitly**: `∃ p prime, ∃ φ : (∀ i, ZMod (q i)) →+ ZMod p, Surjective φ ∧ ∃ b, Δ = φ ⁻¹' {b}`.

3. **Two inequivalent definitions of "linked instance" in the same paper.**
   - `main.tex:551-554` (Informal Claim `ICCodimensionOne`, condition 4): *"the following graph is connected: the vertices are all pairs `(x_i,a)`… adjacent whenever there is a constraint whose projection onto `x_i,x_j` contains `(a,b)`."* — a **global connectivity** condition on the whole `Σ x, D x`.
   - `main.tex:2089-2091` (the formal definition): *"An instance `I` is called linked if for every variable `z ∈ Var(I)` and every `a,b ∈ D_z` there exists a path starting and ending with `z` in `I` that connects `a` and `b`."* — a **per-variable** condition that says nothing across variables.

   The second does **not** imply the first (take two variables with no constraint between them and singleton-connected domains; per-variable linkedness holds, global connectivity fails). The gap is patched elsewhere by the separate `fragmented` hypothesis (`main.tex:2098-2102`), but the informal claim conflates them. **The blueprint must use the `main.tex:2089` definition and carry `¬Fragmented` as a separate hypothesis.**

4. **Typo in the definition of `fragmented`,** `main.tex:2100-2102`: *"`Var(C) ⊆ X_1` or `Var(C) ⊆ X_1` for any `C ∈ I`"* — the second must be `X_2`. As written the condition is "every constraint lives in `X_1`", which is not what is meant.

5. **`THMCodimensionOneTheorem` (`main.tex:4004`) mixes `I` and `Θ`.** Conditions (1),(3),(7) are stated about `I` (and about "`Θ`" in (3) and in the conclusion) with no prior binding of `Θ` in the theorem statement. Reading the proof, `Θ` appears to be `I` (or a designated subinstance). **Quantifier/naming hazard — must be resolved from context before formalizing.** Similarly the conclusion set is `{(a_1,…,a_k) | Θ has a solution in φ(a_1,…,a_k)}` while `Δ` in the proof is defined the same way; but condition (7) is about `I`, so the two must be identified.

6. **`main.tex:4109-4114`: "`L` has dimension `k` and can be defined by one linear equation."** The inference is: `L ≤ Z_{q_1}×⋯×Z_{q_k}×Z_p`, `proj_{1..k} L` is full, and `(b_1,…,b_k,0) ∉ L`. From "full projection" one gets `dim L ≥ k`; from `(b,0) ∉ L` one gets `L ≠` everything, so `dim L ≤ k`. Hence `dim L = k = dim(ambient) − 1`, so `L` is a coatom, hence a kernel. **The step "codimension 1 subgroup ⟹ kernel of a single surjective hom onto some `Z_p`" is used silently.** It is true (see §3.4 item 3) but is exactly the lemma Mathlib does not have, and it is where the mixed-prime subtlety lives.

7. **`Turing.TM2ComputableInPolyTime.comp` is an open `proof_wanted` in Mathlib** (`Mathlib/Computability/TuringMachine/Computable.lean:284`). Any plan that reaches for Mathlib's polytime notion inherits this hole. Record it in the blueprint as a hard blocker, not a detail.

8. **`SimpleGraph.fromRel` deletes the diagonal** (`Mathlib/Combinatorics/SimpleGraph/Basic.lean:133`, `Adj v w ↔ v ≠ w ∧ (r v w ∨ r w v)`). Harmless for reachability but it means `(fromRel R).Reachable = Relation.EqvGen R` needs its own (easy) proof; the nearby Mathlib lemma `reachable_fromEdgeSet_fromRel_eq_reflTransGen` (`Connectivity/Connected.lean:119`) is about `fromEdgeSet (Sym2.fromRel sym)`, **a different graph**, and additionally requires `Std.Symm r`. Do not assume it applies.

9. **`Relation.ReflTransGen` has no decidability instance in Mathlib.** Fine if the development is classical, but if any part of the blueprint claims computability/decidability of linkedness, that instance must be built (via `SimpleGraph`). Currently no such instance exists anywhere in Mathlib.

10. **`FirstOrder.Language.Structure` has no product instance.** Every statement in Zhuk of the form `R ≤ A_1 × ⋯ × A_m` or `Sg_A(R) ≤ A^n` needs one. It is 5 lines, but its absence means "subalgebra of a product" is not currently expressible in Mathlib's model-theory API at all. If the blueprint's module graph assumes `ModelTheory` gives us powers of algebras, it is wrong until we add this.
