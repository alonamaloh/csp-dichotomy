# Prior art: `zeb/zhuk_centers.tex` + `zhuk-lean`

What the successful small project did, stated precisely enough to be re-executed at
scale. Sources read in full: `/home/alvaro/claude/zeb/zhuk_centers.tex` (1831 lines,
27 PDF pages, 20 of body + 7 of appendices), `/home/alvaro/claude/zeb/README.md`,
`/home/alvaro/claude/zeb/regen_appendix.py`, and every file of
`/home/alvaro/claude/zhuk-lean` (1603 lines of Lean across 12 modules + root).

Hard numbers used throughout:

| Quantity | Value |
|---|---|
| Blueprint LaTeX | 1831 lines, 98 KB, 27 pages (body pp. 1–20, appendices pp. 20–27) |
| Labelled statements | 60 = 5 thm + 16 lem + 2 prop + 4 cor + 15 def + 16 rem + 2 conv |
| Proof-carrying statements | 27 (thm/lem/prop/cor) |
| Lean | 1603 lines, 12 modules, `sorry`-free, Lean 4.32.2 / Mathlib v4.32.2 |
| Source material formalized | Brady's notes §3.8 (Def 3.8.1–Lem 3.8.6) + §3.10 (Def 3.10.3–Cor 3.10.10) ≈ 7–8 printed pages, 12 numbered statements |
| Drafts | 9 blueprint commits (8 numbered drafts + a post-formalization note), 5 Lean commits |
| Review | 6 rounds, 2 independent reviewers; then 2 independent formalizations |

Derived rates (all used in §4):

* **8 source pages → 20 blueprint body pages** (≈ 2.5× page expansion)
* **12 source statements → 60 blueprint statements** (5× statement expansion)
* **1603 Lean lines / 27 blueprint pages = 59 lines per page**; / 20 body pages = 80
* **1603 / 27 proof-carrying statements = 59 Lean lines per proved statement**
* **1603 / 12 source statements = 134 Lean lines per source statement**
* **1603 / 8 source pages ≈ 200 Lean lines per source page**

---

## 1. The blueprint's house style

### 1.1 Physical setup

`article`, 11pt, a4paper/28mm margins, `lmodern`, `amsmath/amssymb/amsthm`,
`longtable`, `fancyhdr`, `hyperref[hidelinks]`. No `microtype`, no BibTeX — a
hand-written `thebibliography` with 4 entries. Two custom theorem styles:

```latex
\newtheoremstyle{mainplain}{9pt}{9pt}{\itshape}{}{\bfseries}{.}{0.55em}{}
\newtheoremstyle{mainroman}{9pt}{9pt}{\normalfont}{}{\bfseries}{.}{0.55em}{}
```

`mainplain` carries `theorem/lemma/proposition/corollary`; `mainroman` carries
`longtheorem/longlemma/longproposition` (declared for statements too long to set in
italic — **declared but never used** in this document; keep them, they will be used at
2404 scale, where statements have enumerated cases). `definition` style carries
`definition/remark/convention`.

Notation macros are tiny and mnemonic: `\bA \bB \bC \bD \bM` for boldface algebras,
`\ab` = `\lhd` (absorbs), `\abin` = `\lhd_{\mathrm{bin}}`, `\aZ` = `\lhd_Z` (central),
`\Tm` = `T_\sigma` (terms), `\Sg`, `\Clo`.

### 1.2 Numbering and labelling

* **One shared counter**, `\newtheorem{theorem}{Theorem}[section]` with everything else
  `[theorem]`. So Definition 1.9 and Lemma 1.10 are adjacent numbers; there is exactly
  one numbering sequence per section and no ambiguity about "1.10".
* **Sections number continuously across `\part`s** (Parts I/II/III contain §§1–2, §3,
  §§4–8). Parts are organizational, not numbering scopes.
* **The main theorem is stated before §1**, so it is *Theorem 0.1* — a deliberate trick
  that gives the top-level statement a stable, obviously-distinguished number, and lets
  the document open with what it proves.
* Equations are `\numberwithin{equation}{section}`; the two conditions of essentiality
  get *named* tags `\label{eq:E1}`/`\label{eq:E2}` and `\label{eq:B1}`/`\label{eq:B2}`
  and are cited by number throughout the proofs ("\eqref{eq:E1} at index $i$").
  Locally reusable claims inside a proof get manual tags: `(\dagger)`, `(\ddagger)`,
  `(\ast_\ell)`.
* **Label scheme**: `type:kebab-case-description`, with `type ∈ {thm, lem, prop, cor,
  def, rem, conv}` and the description naming the *content*, not the position:
  `lem:taylor-binary`, `thm:relational-absorption`, `rem:absorption-quantifier`,
  `conv:standing`. This is machine-load-bearing: `regen_appendix.py` recognizes exactly
  `\\ref\{(?:lem|thm|prop|cor|def|rem|conv):[^}]+\}`.
* **Every environment has a bracketed title and an immediately following `\label`**:
  `\begin{lemma}[Regrouping]\label{lem:essential-groups}`. The regex in the tool
  requires the label to follow the optional title with only whitespace between; the
  title becomes the italic second line of the citation-index row. No exceptions.

### 1.3 Hypothesis management — the single most transferable habit

Three layers, all explicit:

1. **`Convention 1.2` (standing hypotheses)** — a *numbered, labelled, citable*
   environment, not prose. It states the two ambient assumptions (fixed signature with
   no nullary symbols; all algebras have nonempty universe) **and audits where each is
   consumed**, by cross-reference: "(b) is consumed in three places:
   Remark 2.2 …; Theorem 3.10 …; Remark 4.4(b) …". It closes with an instruction to the
   formalizer: "A formalization should carry both as explicit hypotheses or instance
   arguments rather than as ambient prose."
2. **`Convention 1.5` (subalgebra means nonempty)** — legislates a word whose informal
   use is ambiguous. "*Subalgebra*" = nonempty subuniverse; "has no proper subalgebra
   with property P" therefore excludes only nonempty ones; objects introduced as
   "subuniverses" may be empty. Every downstream statement that says "no proper binary
   absorbing subalgebra" then cites `Convention~\ref{conv:subalgebra}` **at the point of
   use inside the proof**, not just once at the front.
3. **Restated hypotheses in every theorem.** Despite the standing convention, each
   theorem in Part III repeats "Let $\bA,\bB$ be finite idempotent algebras, let
   $R\le\bA\times\bB$ be subdirect with left center $C$" in full. The section-opening
   prose ("Throughout this part …") duplicates rather than replaces them. Nothing is
   inherited silently across a `\section` boundary.

### 1.4 Statement granularity

Everything a proof step needs is a numbered statement with a name:

* Facts a human would inline are separate lemmas: `lem:singleton` (singletons are
  subuniverses in an idempotent algebra, 1-line proof), `lem:term-idempotent`,
  `lem:preservation`, `lem:block-enumeration`.
* A single big source theorem is **split** where the formal proof splits.
  Brady's Thm 3.10.5 becomes `thm:center-step` (the enlargement inequality) plus
  `thm:center-absorbs` (the induction over star powers) — the concordance records the
  split explicitly.
* Closure facts are **bundled by kind, enumerated (a)–(e)**, with the enumeration used
  as a citation surface: `Lemma~\ref{lem:pp}(b),(c)` appears ~8 times. Bundle when the
  proofs are one line each and the consumers cite individual parts.
* Definitions are numbered and cited like theorems: `Definition~\ref{def:absorption}`
  appears in proofs at the exact step where the definition is unfolded.
* **Remarks are first-class and carry formalization content.** 16 of 60 statements are
  remarks. They fall into recognizable types:
  * *quantifier-form warnings* (`rem:absorption-quantifier`, `rem:induction-shape`):
    state the wrong reading, the right reading, and the exact instance where they part
    company ("$E=\varnothing$, $m=1$, $D\ne\varnothing$");
  * *design-justifications* (`rem:star-indexing`, `rem:fixed-list`, `rem:pp-usage`):
    why an indexing was chosen and what it saves;
  * *degenerate-case audits* (`rem:degenerate-center`, `rem:absorption-degenerate`):
    enumerate the degenerate cases and show each is either trivial or true, so that the
    main proofs never need a case split;
  * *proof-shape warnings* (`rem:step3-shape`): "Step 3 is the only argument in this
    document that doubles back on itself … a formalization should package (‡) as a
    standalone, universally quantified lemma, proved before the element $b$ is fixed";
  * *scope limits* (`rem:not-proved`, `rem:regrouping-weaker`): what the source proves
    that this document does not, and why that is enough;
  * *post-formalization findings* (`rem:blocks-nonempty-free`,
    `rem:enumeration-avoidable`, `rem:doubling-specialized`): added after both
    formalizations agreed a hypothesis/lemma was unnecessary. The text is deliberately
    left as it stands and the simplification recorded next to it.

### 1.5 How much detail a proof gets

Proofs run 3–45 LaTeX lines. Rules visible in every one:

* **Every non-trivial step names the statement it uses.** "a subuniverse by
  Lemma~\ref{lem:pp}(b),(c)", "by Lemma~\ref{lem:substitution-eval} and hypothesis (a)".
  There is no "clearly", no "it is easy to see", no "similarly" without a stated
  symmetry ("symmetric, exchanging the roles of $\vec x$ and $\vec y$ and using
  $\{b\}\times C'\subseteq S$" — the *witness* for the symmetric case is named).
* **Long proofs are cut into labelled Steps/Claims** (`\emph{Step 0: choose $R$
  minimizing $|\beta(R)|$.}`, `\emph{Claim 1.}`), and the Steps are referred to by
  number later ("this contradicts Step~3", "applying its own Step 1 twice").
* **Reusable intermediate assertions are displayed and tagged.** `(\ddagger)` in
  Lemma 7.1 is a displayed, explicitly universally quantified statement
  ("for all $b_1,b_2\in B'$: $b_2\in\Sg(C'\cup\{b_1\})$") — precisely so that its two
  later instantiations can be *named* rather than re-derived.
* **Multi-case constructions are given normal forms.** Lemma 7.1 opens by renaming the
  hypothesis' designated subuniverses $D_0,\dots,D_{n+1}$ so the box at index $i$ is
  $\prod_{r\ne i}D_r$: "This avoids the schematic ellipsis
  $C\times\cdots\times A_i\times\cdots\times C'$, which is ambiguous at $i=0$ and
  $i=n+1$." Ellipsis notation is treated as a defect to be removed.
* **Choice and minimization are justified in words.** Step 0: "the set of values … is a
  nonempty set of naturals bounded by $|A_{n+1}|$, and therefore has a least element…
  no choice principle is involved, since a single attaining relation is named by
  existential instantiation."
* **Arithmetic side conditions are cited to the background appendix.**
  "$\min(N,\min(N,x)+1)=\min(N,x+1)$, both recorded in Appendix C."

### 1.6 The appendices (four, each with a distinct job)

* **Appendix A — statement-level citation index.** A `longtable`, one row per labelled
  statement, generated by `regen_appendix.py`. Left column: type, number, italic title.
  Right column: the labelled statements cited in the statement *and its proof*, or the
  sentinel "Definitions and imported background (Appendix C) only." A final row
  aggregates references occurring in narrative prose outside any environment.
  The appendix **carries its own health warning**: it is a *syntactic cross-reference
  index, not a dependency graph*; expository forward references exist and are listed
  (the only forward *proof* dependency is Theorem 0.1, stated first and proved last).
  This honesty is what stops the table from being trusted as an import graph.
* **Appendix B — suggested module order.** 8 numbered coarse modules, hand-maintained,
  each a phrase-list of contents. Plus two paragraphs of design advice: which modules
  are reusable infrastructure (1–3), which is the only place an exponentially large
  index set appears (6: $\bA^{A^m}$), and what the convenient object type is there.
* **Appendix C — imported background.** 6 numbered items, each stating the facts **in
  the form used**: finite cardinality facts; the two `min` identities *in the order they
  are applied*; structural + strong induction; products/restriction/images; finite
  enumeration and finite choice with the exact use site; index inequalities for the
  block bookkeeping. Two closing paragraphs say what is deliberately *not* imported
  (term substitution — it is developed in Part I) and what stopped being imported
  between drafts (Euclidean division, killed by the star-power reindexing). Ends with:
  "The list is intended to cover the imported inferences, without a claim of
  demonstrated exhaustiveness; reviewers are invited to report any use of background not
  covered by an item above."
* **Appendix D — concordance with the source.** Three columns: source number, this
  document's number, **difference**. The difference column is where the document is
  honest: "*Weaker.* The source also records the specific form …, only the existence
  assertion is proved here"; "Split, and *stronger* in hypotheses"; "The source assumes
  $\bA$ finite and idempotent; idempotence is not used here and is dropped"; "Not
  covered; see Remark 8.3". A closing note pins the source's label names
  (`prop-essential-down`, `absorption-essential`, …) so the concordance survives
  renumbering of the source.

### 1.7 Front matter

Abstract (states the theorem, what is proved from what, and "written to serve as the
human-readable blueprint for a formal development"), then **Theorem 0.1 in full before
the TOC**, then TOC, then an unnumbered Introduction with four labelled paragraphs:
*What is proved, and from what* (bulleted); *Route* (one paragraph per Part);
*Divergences from the source* (three numbered points); *What the formalizations found*
(added in the last commit; three pointers to remarks). Attribution is separated by
ingredient — Zhuk / Zhuk–Kozik / Barto–Kazda — in both the intro and the README.

### 1.8 Tooling

`regen_appendix.py` (117 lines, stdlib only) rewrites Appendix A in place:

1. Truncate the source at `\appendix`.
2. Regex-match `\begin{(long)?(theorem|lemma|…)}(\[title\])?\s*\label{…}` and find the
   matching `\end{…}` by string search → statement spans, in document order.
3. Attach proofs: for each `\begin{proof}[opt]`, if `opt` contains a `\ref{}` to a known
   label, attach there (this is how "Proof of Theorem 0.1" is attached across 20 pages);
   otherwise attach to the nearest preceding statement whose body ends before the proof.
4. Collect `\ref{}`s of known label-prefix in (statement ∪ proofs), dedupe, drop self.
5. Emit rows between `\endlastfoot` and `\end{longtable}`; last row is the narrative
   row, computed by deleting all statement/proof spans from the body text.

Idempotent, deterministic, no dependencies. **The regex is the style guide**: any
statement without a bracketed title, or with a blank line between title and `\label`, or
with an unrecognized label prefix, silently vanishes from the index. At 2404 scale this
script wants: a `--check` mode that fails on unlabelled/untitled environments, a
`\usesexternal{…}` marker for imported facts, and per-section grouping of the table.

---

## 2. The Lean development's conventions

Layout: `ZhukLean.lean` (12 imports, nothing else) + `ZhukLean/*.lean`, one module per
blueprint chunk, in dependency order: `Product`, `Absorption`, `StarPower`, `Essential`,
`Regrouping`, `Relational`, `Center`, `Step`, `Absorbs`, `Central`, `Doubling`,
`Ternary`. Sizes 54–289 lines; median ~120. Everything in `namespace ZhukLean`, with
`open FirstOrder Language`.

`lakefile.toml`: Mathlib pinned by `rev = "v4.32.2"` matching `lean-toolchain`
`leanprover/lean4:v4.32.2`; `leanOptions` set `relaxedAutoImplicit = false` (important —
it turns a typo'd identifier into an error rather than a fresh universe-polymorphic
variable), `weak.linter.mathlibStandardSet = true`, `maxSynthPendingDepth = 3`.
Warm builds ~2 s. Apache 2.0 for the Lean, CC BY 4.0 for the prose.

### 2.1 What represents what

| Blueprint object | Lean |
|---|---|
| signature $\sigma$ | `L : FirstOrder.Language` (Mathlib) |
| algebra $\bA$ | a type `M` with `[L.Structure M]` — **no bundling**; algebras are types+instances |
| universe $A$ | the type itself; "all of $A$" is `(Set.univ : Set M)` |
| subuniverse $S\le\bA$ | *two* forms: `S : Set M` for statements, `S : L.Substructure M` when closure/`fun_mem` is needed; converted by `(S : Set M)` |
| generated subuniverse $\Sg(X)$ | `Substructure.closure L X` |
| term $t\in\Tm(V)$ | `L.Term V` (Mathlib) — polymorphic in the variable type |
| $t\in\Tm(n)$ | `L.Term (Fin n)` |
| $t^{\bA}(\vec a)$ | `t.realize v` with `v : V → M` |
| substitution $t[u]$ | `Term.subst` (Mathlib); renaming along a map is `Term.relabel` |
| product $\prod_{i\in I}\bA_i$ | `∀ i, M i` with the local `piStructure` instance |
| $\bA\times\bB$ | `A × B` with the local `prodStructure` instance |
| $\bA^m$ / $\bA^X$ | `Fin m → M` / `X → M` (special case of `piStructure`) |
| relation $R\le\bA_1\times\cdots$ | `L.Substructure (Fin m → M)` — a bundled substructure of the power |
| projection / reindexing | `evalHom i`, `reindexHom g` (local `→[L]` homs), `fstHom`, `sndHom` |
| $\pi_J(R)$ | `R.map (reindexHom g)` |
| $R\cap$ box, cylinder | `R ⊓ S.comap (evalHom i)` |
| $a+R$ | `nbhd R a : Set B`, bundled as `nbhdSub hA R a : L.Substructure B` |
| left center $C$ | `leftCenter R : Set A`, bundled as `leftCenterSub hB R` |

### 2.2 Naming

Mathlib conventions, followed strictly:

* `def`s producing data/props: lowerCamelCase (`starPower`, `betaSet`, `betaSub`,
  `termOps`, `doubled`, `centralGens`, `centralPairs`, `nbhd`, `leftCenter`,
  `gensFst`, `singletonSub`, `reindexHom`, `evalHom`).
* Predicates as `Is…`/verb: `IsIdempotent`, `IsTaylorOn`, `IsEssential`,
  `IsEssentialOn`, `Witnesses`, `Absorbs`, `BinAbsorbs`, `CentrallyAbsorbs`,
  `Subdirect`, `HasEssential`.
* Theorems: snake_case describing the conclusion, `_of_` for hypotheses:
  `binAbsorbs_of_oneSided`, `not_isEssential_of_witnesses`,
  `exists_witnesses_of_not_hasEssential`, `hasEssential_of_essentialOn`,
  `hasEssential_of_succ`, `hasEssential_of_le`, `betaSet_subset_closure`,
  `realize_mem_nbhd_realize`, `notMem_of_mem_betaSet`.
* Blueprint headline results keep the paper's name: `center_step`,
  `leftCenter_witnesses`, `center_central`, `zhuk_center`, `hasEssential_doubled`,
  `exists_ternary_witnesses`, `zhuk_main`.
* **Every module has a `/-! # … -/` header** naming the blueprint statements it covers,
  a "## Main definitions"/"## Main results" list, and — crucially — a paragraph
  explaining *where the encoding deviates from the blueprint and why* (see
  `Regrouping.lean`'s "The encoding", `StarPower.lean`, `Central.lean`'s "The generator
  blocks, without sorting them", `Doubling.lean`'s header).
* **Every docstring cites the blueprint number**: `/-- Blueprint Definition 4.2: the
  neighborhood `a + R`. -/`, `/-- **Blueprint Theorem 5.1** (the enlargement step). -/`.
  Headline results are bolded. The README carries a full blueprint↔Lean concordance
  table (30 rows) — the mirror image of blueprint Appendix D.

### 2.3 Props vs structures vs data

* Multi-condition predicates are **structures with named, documented fields**, not
  conjunctions: `IsEssential` has `witness`/`no_full` (= (E1)/(E2)); `IsEssentialOn` the
  same; `Subdirect` has `fst`/`snd`; `CentrallyAbsorbs` has `absorbs`/`central`. This
  makes `⟨h1, h2⟩` construction and `h.witness` projection read like the blueprint's
  labelled equations.
* **A Taylor identity is data, not a Prop**: `structure TaylorAt (D) (t) (i)` in `Type`
  with fields `u v : Fin k → Fin 2`, `u_at : u i = 0`, `v_at : v i = 1`, `realize_eq`,
  and `IsTaylorOn D t : Type _ := ∀ i, TaylorAt D t i`. So the witnessing maps are
  available for `Term.relabel` without `Classical.choice`. Consequence for the new
  project: WNU/Taylor/cyclic-term hypotheses should likewise be carried as data.
* `Absorbs L E D := ∃ (m : ℕ) (t : L.Term (Fin m)), Witnesses E D t` — existential over
  arity *and* term, but the witnessing predicate is separate and reusable
  (`Witnesses E D t` is what the strong theorems produce).

### 2.4 Absorption: tuple form, and generic in `D`

```lean
def Witnesses (E D : Set M) {V : Type*} (t : L.Term V) : Prop :=
  ∀ (i : V) (z : V → M), z i ∈ D → (∀ j, j ≠ i → z j ∈ E) → t.realize z ∈ E
```

Three deliberate features, all load-bearing:

1. **Tuple form** — the tuple `z` is constrained coordinatewise; there is no separate
   list `e : V → E` with one entry overwritten. The two readings differ exactly at
   `E = ∅, |V| = 1, D ≠ ∅`, and only the tuple form makes
   `exists_witnesses_of_not_hasEssential` a true biconditional.
2. **Polymorphic variable type `V`** — the star powers have variables `Fin ℓ → Fin k`
   and feed `Witnesses` directly; `Absorbs.of_finite` transports to `Fin m` via
   `Fintype.equivFin` + `Witnesses.relabelEquiv`. This is blueprint Lemma 2.2 and it is
   used exactly once, at the very end.
3. **Generic `D`** — even though every application in Part III takes `D = Set.univ`, the
   definition keeps the relative form `E ⊆ D ⊆ M`. **This is the right call for 2404**,
   where `C <_T B <_T A` (absorption relative to a subalgebra, using ambient terms) is
   everywhere. The blueprint's remark that "the ambient algebra is suppressed … the
   condition mentions $t^{\bA}$ only at arguments lying in $D$" is exactly the
   justification for never forming "the algebra on $D$".

Binary absorption is `∃ t : L.Term (Fin 2), Witnesses E D t` — same predicate, arity
pinned. Blueprint Lemma 2.6 is `binAbsorbs_of_oneSided`, whose Lean statement dropped
the blueprint's hypothesis that `E`, `D` are subuniverses (only `E ⊆ D` is used).

### 2.5 Finiteness and decidability

* Finiteness enters as **typeclass hypotheses on the algebra type**: `[Finite B]`,
  `[Nonempty B]`, `[Finite A]`. `Fintype` is materialized inside proofs when needed
  (`have : Fintype M := Fintype.ofFinite M`). Blueprint Convention 1.2(b) (nonempty
  universe) becomes `[Nonempty B]` — an instance argument, exactly as the convention
  instructed.
* **Cardinality is `Set.ncard`** (+ `Nat.card` for the type), with finiteness supplied
  at each use by `Set.toFinite _`. Key idioms: `Set.ncard_lt_ncard hss (Set.toFinite E)`
  for strict growth; `Set.eq_of_subset_of_ncard_le` for "full-size subset is everything"
  (used twice: saturation of the neighbourhood, and minimality in the doubling trick).
* **`classical` at the top of proofs that need decidability** (`Regrouping`,
  `Relational`, `Doubling`, `Central`). No `DecidableEq` hypotheses anywhere; no
  computable content is claimed. `Finset.filter` with a classical decidability instance
  is used for the live set `X` in `Relational.lean`.
* **All arithmetic obligations went to `omega`**, including `min`/`max` on ℕ — the
  blueprint's Appendix C item 2 (`min (N) (min N x + 1) = min N (x+1)`) is a one-line
  `by omega`. The README records that `fin_cases`, `ring`, `norm_num` are *not*
  transitively imported by `Mathlib.ModelTheory` and must be imported explicitly
  (`import Mathlib.Tactic.FinCases`), but `omega` is.
* **Minimization** (blueprint Step 0) is `Nat.find` over `∃ k, ∃ R, IsEssential C R ∧
  (betaSet C R).ncard = k`, then `Nat.find_spec` / `Nat.find_le`. No well-ordering
  argument written by hand.
* **Finite choice** is `choose … using` on a `∀ i, ∃ x, …` (blueprint Appendix C item 5),
  e.g. `choose r hrR hrS using hw`, `choose x hxR hxC using fun i => hR.witness i.castSucc`.

### 2.6 What Mathlib supplied, and what it did not

Supplied (essentially all of blueprint Part I §1):
`Language`, `Term` (with `func : L.Functions l → (Fin l → Term α) → Term α`, so
arbitrary branching arity needs no encoding), `Term.subst`, `Term.relabel` and their
`realize` laws, `Structure`, `ClosedUnder`, `Substructure`, `Substructure.closure` with
`closure_le`, `closure_mono`, `closure_induction`, `Term.realize_mem` (preservation),
`Substructure.mem_closure_iff_exists_term` (generation by terms over the generating set
*as the variable type*), `Substructure.map`/`comap`/`⊓`, `Hom` (`→[L]`),
`Substructure.inducedStructure`, and `ModelTheory.Quotients` (`Prestructure` →
`quotientStructure`, `Term.realize_quotient_mk'`).

Not supplied, and written locally in `Product.lean` (143 lines — the whole gap):
* `piStructure : L.Structure (∀ i, M i)` and `prodStructure : L.Structure (A × B)`
  (Mathlib's `Ultraproducts` goes straight to the quotient via `Prestructure` and never
  exposes the product);
* coordinatewise realization `realize_pi`, `realize_prod` (both `@[simp]`);
* `fstHom`, `sndHom`, `reindexHom g` (= projection **and** reindexing in one map, i.e.
  blueprint Lemma 1.19(c) and (e)), `evalHom i`;
* `snoc_funMap` — that `Fin.snoc` commutes with `funMap`, needed to see the doubled
  relation is a subuniverse.

Mathlib has **no universal algebra and no CSP content**: no `Clo`, no term clones, no
congruence lattice for a `Language`, no subdirect products, no Taylor/WNU/cyclic terms,
no absorption. Blueprint Parts II and III are 100% new code.

Recorded frictions worth carrying forward: `Structure` bundles `funMap` and `RelMap`, so
every product instance must supply a `RelMap` even for a purely algebraic signature;
binder-type inference on subtype coercions fails for `fun g => (g : A × A).1`, hence the
named `gensFst`/`gensSnd`.

### 2.7 Encodings that beat the blueprint's

The seven README findings, condensed to the four that are architectural:

* **Star powers indexed by `Fin ℓ → Fin k`** rather than `Fin (k ^ ℓ)`: block+position is
  `Fin.cons j q`, and the evaluation law is a two-line proof. Euclidean division leaves
  the imported background entirely. (The blueprint was then *rewritten* to match —
  eighth draft.)
* **Regrouping over a fixed index type + a live `Finset`**, not a shrinking index set.
  `IsEssentialOn S (J : Finset I) (block : I → Fin m) R` quantifies conditions over
  `i ∈ J` only; deleting a coordinate is `J.erase u`; the induction is
  `Nat.strong_induction_on` on `J.card`. Only the base case transports (along a choice
  of block representatives `g : Fin m → I`), once. This makes regrouping double as the
  generic **reindexing/transport lemma** — used later to move the doubled relation from
  `Fin (n+1) ⊕ Fin (n+1)` to `Fin (2n+2)` for free.
* **Generating sets as variable types.** `mem_closure_iff_exists_term` gives a term whose
  variable type *is* the generating set, so every variable already records which
  generator block it came from. The blueprint's sorted enumeration (Lemma 1.20) and its
  `p ≤ q` index bookkeeping evaporate; the selector becomes
  `fun g => if g.2 = a then 1 else 0`.
* **Sum types instead of reversed concatenations.** The doubled relation is indexed by
  `Fin (n+1) ⊕ Fin (n+1)`; the blueprint's coordinate reversal is not modelled at all.

### 2.8 A verified defect: the blueprint↔Lean numbering has already drifted

The Lean docstrings and the README concordance cite the blueprint by **number**. Two
later blueprint commits inserted statements in the middle of sections:

* `ab0fada` ("Eighth draft") inserted `\begin{lemma}[Renaming the variable set]
  \label{lem:absorption-rename}` after Definition 2.1;
* `035390b` (the last commit) inserted `\begin{remark}[The blocks need not be assumed
  nonempty]\label{rem:blocks-nonempty-free}` after Definition 3.2 (and two more remarks
  elsewhere).

Because everything shares one counter, every number after each insertion moved by one.
Checking the current `.tex` against the Lean:

| Lean cites | Current blueprint number | Status |
|---|---|---|
| Def 2.4 Taylor identities | **2.5** | stale |
| Lemma 2.6 one-sided ⟹ binary | **2.7** | stale |
| Def 2.7 star powers | **2.8** | stale |
| Prop 3.4 arity reduction | **3.5** | stale |
| Prop 3.5 absorption forbids essential | **3.6** | stale |
| Lemma 3.7 regrouping | **3.8** | stale |
| Lemma 3.9 term operations | **3.10** | stale |
| Thm 3.10 relational description | **3.11** | stale |
| everything in §§1, 4–8 | unchanged | correct |

Nine stale cross-references in a 1600-line project after two edits. At 400 blueprint
pages this failure mode is fatal. **Rule: the Lean must cite blueprint *labels*
(`lem:absorption-rename`), not numbers**, and the blueprint must expose them — either by
printing the label next to the statement, or by generating a `label → number` table, or
(best) by adopting a `leanblueprint`-style `\lean{}`/`\uses{}` markup so the linkage is
machine-checked in both directions.

### 2.9 The hypothesis-bundle smell (a scaling warning)

The hypothesis "B has no nonempty proper binary absorbing subuniverse" is spelled out
verbatim at six use sites:

```lean
(hbaf : ∀ N : L.Substructure B, (N : Set B).Nonempty → (N : Set B) ≠ Set.univ →
  ¬ BinAbsorbs L (N : Set B) Set.univ)
```

and "central" likewise as `hZ : ∀ a ∉ (C : Set A), ((a,a) : A × A) ∉ Substructure.closure
L (centralPairs (C : Set A) a)`. At 1600 lines this is tolerable; at 2404 scale, where
"BA and center free", "B ≤_T A for T ∈ {BA,C,S,PC,L,D}", and "in the variety V_n" recur
hundreds of times, these must be **named predicates/classes from day one** (blueprint
convention → Lean definition, 1:1).

---

## 3. LESSONS → checklist for the new blueprint

The README's five defects generalize into a checklist. I group them by the failure mode,
give the concrete prior instance, and state the rule and the audit that catches it.

### A. Foundations must be built, not gestured at

*Instance*: the first draft defined only variable renaming along a bijection. Three
constructions need genuine simultaneous substitution — `t(x_{u(1)},…,x_{u(k)})` (variable
identification, `u` not injective), the star powers (terms into terms), and
`t(x₁,…,x₁,x₂,…,x₂)`. Repaired as Definition 1.9 + evaluation law Lemma 1.10.

* **A1.** For every syntactic operation the document performs on terms/formulas/relations,
  there is a *definition* and an *evaluation/semantics law* stated as a lemma. Candidate
  list for 2404: substitution, relabelling, pp-formula formation and its semantics,
  conjunction/existential quantification of pp-formulas, composition of relations,
  quotient of a term operation, restriction to a subalgebra, the $\sigma^*$ and bridge
  constructions, "$\Omega$-instance" syntax.
* **A2.** Never define a construction "up to obvious bijection". If two index sets are
  isomorphic, either use one of them everywhere, or state the transport lemma and cite it.
* **A3.** Audit at the end of drafting: grep the document for each construction and check
  a definition number is cited at first use. The Appendix-C paragraph "X is deliberately
  *not* in this list; it is part of the development" is the artefact that records this.

### B. Quantifier form decides truth in degenerate cases

*Instance*: "for all $c_1,\dots,c_k\in C$, replace $c_i$ by $a\in A$" leaves $c_i$
unused, so the statement is vacuous when $C=\varnothing$ — *including at arity 1, where
the intended content is not vacuous*. Theorems 5.1/5.2 restated over tuples constrained
coordinatewise.

* **B1.** State every "one coordinate free, the rest in $S$" condition by **constraining
  one tuple**, never by quantifying over a tuple from $S$ and overwriting.
* **B2.** For each definition, ask: *what does it say when the set is empty / a singleton
  / everything / the arity is 1 or 0?* Record the answer in a Remark. If two readings
  agree except in one corner, name the corner exactly ("$E=\varnothing$, $m=1$,
  $D\ne\varnothing$") and say which reading downstream theorems require and why.
* **B3.** Any induction must be stated in *the same quantifier shape as its consumer*
  (blueprint `(∗_ℓ)` matches Definition 2.1 verbatim), so no bridging step is needed at
  the end. Bridging steps between a vacuous inductive statement and a non-vacuous
  conclusion are where formalizations stall.
* **B4.** 2404-specific: essentiality, absorption, "$\proj_1(R\cap(C_1\times\cdots))$",
  linkedness, and the strong-subalgebra relations $\le_T$ all have this shape. Also the
  paper's implicit convention that $\varnothing$ is or is not a subuniverse must be
  legislated once and cited at use.

### C. Index sets, not ordered lists

*Instance*: Theorem 3.10 forms $\bA^{A^m}$ and projects onto a subset $X\subseteq A^m$;
an ordered-product formulation does not cover this. Products and essentiality were
redefined over arbitrary **finite** index sets, which also deleted the "WLOG reorder the
blocks" step from the regrouping induction (an oversized block is now shrunk in place).

* **C1.** Products, relations, and partitions are indexed by an arbitrary finite set (in
  Lean: an arbitrary type + a `Finset`, or a `Fintype`), never by `[m]` unless the
  numeric arity is genuinely used.
* **C2.** Keep index sets **finite** explicitly, and say why: it holds the foundational
  boundary at finite choice.
* **C3.** Delete every "WLOG reorder / relabel / assume the blocks are consecutive". Each
  such phrase is either a transport lemma you must state, or a sign the indexing is
  wrong. Prefer indexing that makes the property *invariant* (essentiality does not
  depend on coordinate order — so never reverse a coordinate block).
* **C4.** When the natural index set is a set of functions, or a sum, or a set of
  generators, **use it**; do not encode into `Fin n`. Convert once, at the boundary, with
  a named lemma.

### D. Standing hypotheses are a labelled convention with a consumption audit

*Instance*: Convention 1.2 + the audit of where each clause is used; Convention 1.5
legislating "subalgebra means nonempty".

* **D1.** Every ambient assumption is a numbered `Convention`, citable by `\ref`, with a
  list of the statements that actually consume it.
* **D2.** Every word whose informal usage is ambiguous (proper, nontrivial, subalgebra,
  center, absorbing, "the" WNU, trivial algebra) is legislated in a Convention, and the
  Convention is **cited at the point of use inside proofs**, not just declared.
* **D3.** Theorems restate their hypotheses in full; nothing is inherited across a
  section boundary except what a Convention says.
* **D4.** 2404-specific and **serious**: the paper's standing hypotheses are prose —
  "In this paper we assume that every algebra is a finite idempotent algebra having a WNU
  term operation" (main.tex:1123) — and there is a *second* prose convention that an
  unspecified type variable `T` ranges over `{BA,C,S,PC,L,D}` and `MT` over
  `{MPC,ML,MD}` (main.tex:1644). That convention makes dozens of lemmas implicitly
  universally quantified over a type parameter, and some clauses are true only for some
  `T` (see `LEMBACenterSImplyFactor`, whose proof says "for T=C see Lemma 6.8 in [.]; for
  T=S it is just a combination"). **Each `T`-polymorphic statement must be expanded, or
  the type made a first-class indexed definition with the per-`T` proofs separated.**
  This is the single largest quantifier-discipline hazard in the new project.
* **D5.** Hypothesis bundles that recur become named predicates in both documents
  (blueprint definition ↔ Lean definition), never re-spelled.

### E. Proofs that double back must be refactored into standalone lemmas

*Instance*: Step 3 of the doubling lemma applies its own Step 1 twice, the second time to
an element the first application produced. Step 1's conclusion is now an explicitly
quantified statement (‡) about ordered pairs, proved before the element `b` of Step 2 is
fixed; the Lean development confirms that "written in the source's order it does not
typecheck".

* **E1.** Any sub-claim used more than once, or used at an element produced later in the
  same proof, is **displayed, tagged, and universally quantified over everything it will
  ever be instantiated at**, and is established before any of those elements is named.
* **E2.** Write a Remark identifying every such doubling-back and stating the dependency
  order explicitly ("A formalization should prove (‡) before fixing the element it is
  later instantiated at").
* **E3.** Detection heuristic: search proofs for "again", "similarly", "as before",
  "repeating the argument", "by the same token", "applying this once more". In 2404 this
  pattern is pervasive (the whole Lemma 6.11 chain in Zhuk's 2005.00593 is
  "then by Lemma 6.11 …, then again by Lemma 6.11 …").
* **E4.** A "minimal counterexample" or "choose R minimizing |β(R)|" step must state the
  minimization set, why it is a nonempty set of naturals bounded above, and that the
  competitor constructed later lies in **the same** family (the blueprint says: "so `R''`
  is a legitimate competitor in the very minimization of Step 0 — the designated
  subuniverses are the same ones, and only the relation varies").

### F. Additional rules the prior art demonstrates but the README did not enumerate

* **F1. Ellipsis is a defect.** Replace `C × ⋯ × A_i × ⋯ × C'` with an explicit family
  `D_0,…,D_{n+1}` and `∏_{r≠i} D_r`, because the ellipsis form is ambiguous at the ends.
* **F2. Prove the imported result if the conclusion rests on it.** Barto–Kazda was proved
  rather than cited "precisely because the ternary conclusion rests on it". Decide,
  per import, whether it is a black box (Appendix C) or a proof obligation, and say so.
* **F3. State only what the consumer needs, and say so.** Regrouping proves existence,
  not the sharper "of the form $\pi_I(R\cap\prod D_i)$" — with a Remark saying the proof
  already produces relations of that shape if someone later wants it.
* **F4. Track differences from the source in a table** (Appendix D), with a *Difference*
  column that admits "weaker" as well as "stronger". At 2404 scale, keep one concordance
  row per source statement of every paper in the transitive closure.
* **F5. Record what the formalization found, next to the statement it affects**, and
  leave the prose intact if it is not wrong. Three such remarks exist; all three came
  from *two independent formalizations agreeing*, not from either alone.
* **F6. Keep the imported-background appendix in "the form used"** — including the order
  in which two arithmetic facts are applied. Re-audit it every draft; the prior art
  deleted Euclidean division from it when the indexing changed.
* **F7. Statement-level citation index must disclaim being a dependency graph** unless it
  actually is one. (For 2404 I would build the *real* dependency graph, since it will
  drive module order and parallel work assignment — but then forward references must be
  eliminated, not merely disclosed.)
* **F8. Number the top-level theorem 0.1** (state it before §1) and prove it in one
  paragraph at the end from named corollaries.

### G. Cross-document references must be by label, and machine-checked

*Instance*: §2.8 above — nine of the Lean development's blueprint citations are already
stale, because two later drafts inserted statements into a shared counter.

* **G1.** Blueprint→Lean and Lean→blueprint links are by **label**, never by number.
* **G2.** Adopt `leanblueprint` (`\lean{Namespace.name}`, `\uses{lab1,lab2}`,
  `\leanok`) from the first draft. It gives: a machine-checked name↔statement link, a
  real dependency graph (replacing the syntactic index of Appendix A), and a
  per-statement formalization-status dashboard — all three of which the prior art had to
  approximate by hand and one of which (the dependency graph) it explicitly disclaimed.
* **G3.** Extend `regen_appendix.py` (or replace it) with a `--check` mode run in CI that
  fails on: an environment without a bracketed title; a label not matching
  `type:kebab-case`; a `\ref` to a nonexistent label; a statement not mentioned by any
  `\uses`; a `\lean{}` naming a declaration absent from the Lean build.
* **G4.** Keep the appendix generator's contract stable and documented, because it *is*
  the style guide: at 400 pages, anything the regex silently drops will be dropped.

---

## 4. Scaling assessment

### 4.1 What the observed rate actually measures

The 65 Lean-lines-per-blueprint-page figure is a **lower bound produced under
best-possible conditions**:

* the target is a *leaf* theorem — a shallow dependency tree, 12 source statements, one
  algebraic gadget (star powers), and no interaction with congruences, quotients, or
  varieties;
* Mathlib supplied the entire syntactic layer (terms, substitution, substructures,
  closure-by-terms) — the 143-line `Product.lean` is the *whole* infrastructure gap;
* the blueprint went through 8 drafts and 6 review rounds **before** the Lean was
  written, and was then revised again by what the Lean found;
* it was formalized twice, independently, which is how the three simplifications were
  detected;
* nothing computable, no complexity claim, no algorithm.

The more transferable rates are per-statement and per-*source*-page:
**134 Lean lines per source statement**, **≈ 200 Lean lines per source page of Brady**,
and **2.5× page expansion source → blueprint**.

### 4.2 The size of the target

Zhuk 2404 (`main.tex` 4132 + `StrongSubalgebras.tex` 3144 + `XYSymmetric.tex` 1640 +
`necessaryClaims.tex` 82 = 8998 LaTeX lines; 54 PDF pages; 140 `\label`s):

| File | lem | thm | cor | total |
|---|---|---|---|---|
| main.tex (§§1–3) | 35 | 7 | 10 | 52 |
| StrongSubalgebras.tex (§5) | 46 | — | 4 | 50 |
| XYSymmetric.tex (§4) | 10 | 9 | 1 | 20 |
| necessaryClaims.tex (§2.4) | 5 | — | — | 5 |
| **total** | 96 | 16 | 15 | **127** |

Of these, **18 are attributed to external sources** in the statement header (see the list
in §4.4) — i.e. Zhuk imports them. Definitions are mostly *unlabelled prose*
(`\textbf{Central subuniverse.}` + a paragraph), so add ~40–60 definitional items that a
blueprint must number. Zhuk's page is roughly 2× as dense as Brady's page.

Transitive closure that a self-contained blueprint must absorb or explicitly import:
`zhuk2021strong` = 2005.00593 (52 pp — §6 is the BA/central/strong-subalgebra theory that
2404 cites at least 8 times), `zhuk2020proof` = 1704.01914 (83 pp — Lemmas 6.1, 6.3, 7.2,
8.19, Cor 8.17.1 at minimum, plus the algorithm if the algorithm is in scope),
`DecidingAbsorption` (Barto–Kazda — **already formalized**), `barto2012absorbing`
(Prop 2.15(i)), `hobby1988structure` (Hobby–McKenzie: abelian ⟺ affine for WNU — a
genuine tame-congruence-theory import), `miklos` (Maróti, Lemma 4.7), `ZebsNotes`
(Brady, Thm 3.11.1 and Lemmas 3.11.2–3).

### 4.3 Extrapolation, honestly

Four independent estimates:

1. **Per source page.** 55 dense Zhuk pages ≈ 110 Brady-equivalent pages, plus ~20
   effective pages of transitive closure ≈ 130. At 200 Lean lines/page → **26 000 lines**.
2. **Per source statement.** ~127 statements in 2404 (109 to prove) + ~60 from the
   closure ≈ 170 to prove, at 134 lines each → **23 000 lines**. But the prior-art
   average includes several 3-line lemmas; Zhuk's average statement is heavier, so read
   this as a floor.
3. **Per blueprint page at the observed rate.** 130 source pages × 2.5 → ~325 blueprint
   pages × 65 → **21 000 lines**. (Note that 2.5× expansion may be optimistic: Zhuk's
   prose is terser and has more implicit conventions than Brady's, so 3–4× is likelier,
   pushing the blueprint to 400–500 pages.)
4. **Comparables.** Large Mathlib-adjacent projects with a comparable "one 50-page paper
   plus prerequisites" shape land at 20k–60k lines of Lean, with the low end applying
   only when the ambient library already has the objects. Mathlib has **no** universal
   algebra, so we are not at the low end.

**Estimate: 25 000 – 45 000 lines of Lean for the mathematics of 2404**, of which
5 000 – 9 000 is universal-algebra infrastructure that Mathlib does not have and that
`zhuk-lean` only scratched (congruences and quotient algebras of a `Language`-structure,
the congruence lattice, subdirect products of `n` algebras, pp-definability and its
closure properties, $\Sg$ over arbitrary index sets, $\mathbb{Z}_p$-modules as algebras,
Taylor/WNU/cyclic term machinery, the abelian/affine dictionary). Blueprint: **300–450
pages**. If the *algorithm* of §3 (the CSP solver, its termination and correctness, and
the reduction from the general to the idempotent case) is in scope, add a comparable
amount again — that layer is a different discipline (executable definitions, invariants,
complexity), and 1704.01914 is 83 pages of which a large fraction is the algorithm.

Schedule shape, taking the prior art's ratio at face value (blueprint drafted, reviewed
6×, then formalized): the blueprint is ~25% of the effort and ~100% of the risk. The
prior art's ordering — *blueprint first, formalize second, then revise the blueprint from
what formalizing found* — is the single most important process finding, and it should be
run **per module**, not once for the whole document, because a 400-page blueprint cannot
be reviewed 6 times end-to-end.

### 4.4 What can be reused literally

**Direct reuse of `zhuk-lean` source (≈ 900 of its 1603 lines, essentially unchanged):**

| `zhuk-lean` | Status for the new project |
|---|---|
| `Product.lean` (143 ln) | Reuse verbatim. Products/powers of `L.Structure`, coordinatewise realize, `reindexHom`/`evalHom`/`fstHom`/`sndHom`, `snoc_funMap`. Needed by everything. |
| `Absorption.lean` (178 ln) | Reuse verbatim. `IsIdempotent`, `Witnesses`/`Absorbs`/`BinAbsorbs` (already relative: `E ⊆ D`), `TaylorAt`/`IsTaylorOn` as **data**, `binAbsorbs_of_oneSided`. Extend with ternary absorption as a named notion and with WNU. |
| `Essential.lean` (112 ln) | Reuse. `IsEssential` = Zhuk's essential relation (single-algebra case); `hasEssential_of_succ`/`_of_le` = the projection step Zhuk uses inside Lemma 6.11; `not_isEssential_of_witnesses` = 2404's `LemAbsorptionImpliesEssential` (⇐ direction). |
| `Regrouping.lean` (135 ln) | Reuse. Also doubles as the generic reindexing/transport lemma for relations. |
| `Relational.lean` (95 ln) | Reuse. `exists_witnesses_of_not_hasEssential` **is** 2404's `LemAbsorptionImpliesEssential` = `[DecidingAbsorption, Prop 2.14] = [zhuk2021strong, Lemma 3.2]` (StrongSubalgebras.tex:159), one of the paper's imported black boxes. Caveat: 2404 states it for `n ≥ 2`; the Lean version needs `0 < m` and handles the degenerate cases. |
| `Center.lean`, `Step.lean`, `Absorbs.lean`, `Central.lean` (~510 ln) | Reuse. `zhuk_center` **is** 2404's `LEMCentralRelationImplies` = `[zhuk2021strong, Thm 6.15]` (StrongSubalgebras.tex:208), modulo restating it in the paper's dichotomy form ("either C is central, or B has a nontrivial binary absorbing subuniverse"). `CentrallyAbsorbs` is verbatim 2404's definition of *central subuniverse* (main.tex:1345–1351). |
| `Doubling.lean`, `Ternary.lean` (360 ln) | Reuse for `exists_ternary_witnesses`, which **is** `LEMCenterImpliesTernaryAbsorption` = `[zhuk2021strong, Cor 6.11.1]` (main.tex:1355). **Caveat below.** |

So **three of 2404's eighteen imported-with-citation lemmas are already
`sorry`-free in Lean**: `LEMCenterImpliesTernaryAbsorption` (main.tex:1355),
`LemAbsorptionImpliesEssential` (StrongSubalgebras.tex:159), and
`LEMCentralRelationImplies` (StrongSubalgebras.tex:208). A fourth,
`LEMBACenterSImplyPPDefinition` (StrongSubalgebras.tex:95, = Barto–Kazda Lemma 2.9 +
zhuk2021strong Lemma 6.1/Thm 6.9), is adjacent: it needs the pp-definability closure of
BA/central subuniverses, for which `Lemma 1.19`/`lem:pp` (already in Lean as
`map`/`comap`/`⊓` idioms) is the substrate.

**Caveat on the doubling lemma — the one place the Lean is too special.** `zhuk-lean`
proves only the all-equal specialization (`hasEssential_doubled`: `C`-essential of arity
`n+2` → `C`-essential of arity `2n+2`), because that is all the ternary corollary needs.
Zhuk's Lemma 6.11 in 2005.00593 is genuinely **mixed** — its proof passes from a
`(C₁,C₂,C₃)`-essential relation to a `(C₁,C₂,C₁,C₂)`-essential relation to a
`(C₁,C₁,C₂)`-essential relation — and other consumers (e.g. `LEMBACenterSPossibleIntersections`,
`THMMainStableIntersection`) work with distinct `C_i` on distinct algebras. **The blueprint's
Lemma 7.1 is already stated in the mixed form**; only the Lean specialized it (blueprint
Remark 7.3 records this). Restoring the mixed version means indexing relations by a
family of algebras `(A_i)` rather than a power — i.e. exercising `piStructure` where
`zhuk-lean` only used `Fin m → M`. Budget ~200–300 extra Lean lines and expect it to
propagate into `Essential.lean` (an `IsEssential` over a dependent product).

**Also directly reusable, though not code:** the *process*. Blueprint first; 6 review
rounds by 2 independent reviewers; formalize; feed findings back as Remarks without
rewriting correct prose; keep a concordance with the source that admits weakenings. And
the observation that all three simplifications were found by **two formalizations
agreeing**, not by either alone — at 2404 scale, a second independent formalization of
the whole thing is unaffordable, but a second formalization of the two or three riskiest
lemmas per part is not, and is the cheapest available substitute for a reviewer.

**Architectural things `zhuk-lean` never did, and which dominate the new project:**
it never forms a quotient algebra, never uses a congruence, never treats a subuniverse as
an algebra in its own right (deliberately — see Definition 2.1's "the ambient algebra is
suppressed"), never forms a product of *distinct* algebras (only powers and one binary
product), has no pp-definitions, no varieties/`V_n`, no linked/central relation theory
beyond the left centre, and nothing executable. Mathlib does offer
`ModelTheory.Quotients` (`Prestructure` → `quotientStructure`) and
`Substructure.inducedStructure`, but `Prestructure` is a *class bundling the structure
with one setoid*, which is awkward when a proof handles several congruences on the same
algebra at once — expect to write a bespoke `Congruence L M` structure with a
`Structure` instance on `Quotient`, early, and to pay for it in every statement that
mixes an algebra with its quotient.

---

## 5. What this implies for the route decision and module architecture

1. **The bottom of the tower already exists and should be lifted verbatim.**
   `Product.lean` + `Absorption.lean` + `Essential.lean` + `Regrouping.lean` +
   `Relational.lean` (663 lines) is a working universal-algebra-over-`ModelTheory`
   substrate with the right absorption definition (relative, tuple-form, polymorphic
   variable type). Start the new repo by importing it as modules 1–5, not by rewriting.
2. **Module order, generalizing blueprint Appendix B.** (1) structures, products over
   arbitrary index types, homs, substructures, closure — *reuse*; (2) terms,
   substitution, preservation, generation — *Mathlib + reuse*; (3) absorption (relative),
   binary/ternary absorption, Taylor/WNU/cyclic terms as data — *reuse + extend*;
   (4) essential relations over dependent products, regrouping, Barto–Kazda — *reuse +
   generalize to mixed families*; (5) **new**: congruences, quotient algebras, the
   congruence lattice, subdirect products, pp-definability; (6) **new**: central and
   binary-absorbing subuniverses in the paper's `≤_T` family (this is where `zhuk_center`
   and `exists_ternary_witnesses` plug in as leaves); (7) **new**: linear/PC congruences,
   bridges, `σ*`, the abelian/affine dictionary; (8) **new**: strong subalgebras
   (2404 §2/§5); (9) **new**: XY-symmetric operations (§4); (10) **new**: the dichotomy
   proof (§3), and, if in scope, the algorithm.
   Modules 1–4 are reusable infrastructure with no CSP content; modules 5–7 are the
   infrastructure gap that determines the schedule.
3. **Decide early, and legislate in a Convention, three things `zhuk-lean` never had to
   decide**: (i) is a subalgebra a *subset with ambient operations* (the blueprint's
   choice, which scales, since absorption is already relative) or a *type with its own
   instance* (`Substructure.inducedStructure`, which fights you at every `≤_T^A` triple);
   (ii) how a congruence is represented (bespoke `Congruence L M` + `Quotient` instance
   vs Mathlib's class-bound `Prestructure`); (iii) whether the type parameter
   `T ∈ {BA,C,S,PC,L,D}` of 2404's strong-subalgebra calculus is a first-class indexed
   definition or is expanded per case. All three are quantifier/typing decisions that
   are cheap now and catastrophic to revisit at 20k lines.
4. **Budget honestly**: 25k–45k Lean lines and a 300–450-page blueprint for the
   mathematics; roughly as much again for the algorithm layer. `zhuk-lean` is ~3% of that
   by volume — but it is the part that proves the pipeline works, and it retires three of
   the paper's own imported black boxes.
