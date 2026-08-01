# Zhuk 2404.01080v2 — Deep read of §3.1 (Additional definitions) and §3.2 (Auxiliary statements)

Source of record: `/tmp/claude-1000/-home-alvaro-claude-zeb/b3d460d7-227a-4a0c-983d-31fbf26d8692/scratchpad/papers/src2404/main.tex`.

- §3 begins at **L1932**; §3.1 = **L1969–L2228** (printed pp. 15–17); §3.2 = **L2230–L3406** (printed pp. 17–21); §3.3 "Main Statements" begins **L3407**.
- Cross-referenced Section 2 material lives at **L1064–L1931** of the same file, plus `necessaryClaims.tex` (`\input` at L1929). Proofs of all Section 2 statements are in `StrongSubalgebras.tex` (paper §5).
- Comparison text used throughout: Zhuk's original *A Proof of CSP Dichotomy Conjecture*, `papers/1704.01914.txt` (cited below as **[orig]** with line numbers of that txt file).

Everything below that is in `code font` is a faithful transcription of the LaTeX; prose in *italics after* a definition is my formalization commentary.

---

# 1. Definitions

## 1.0 Vocabulary imported from §2 that §3 uses without restating

These are *not* in §3 but every §3.2 statement is stated in them. A blueprint must have them before §3.

| Notion | Location | Statement |
|---|---|---|
| `V_n` | L1110–1121 | class of **finite** algebras `A = (A; w^A)` whose single basic operation is an **idempotent special WNU** of arity `n`. `Z_p` = `({0..p-1}; x_1+...+x_n mod p)`, a member of `V_n` for the fixed `n`. |
| special WNU | L1079 | `w(x,...,x,y) = w(x,...,x,w(x,...,x,y))`. |
| subdirect / `≤_sd` | L1149, L1157 | all projections onto single coordinates are onto. |
| `pr_{i_1..i_s}`, `∘`, `δ^{-1}`, `B∘δ`, `a/σ`, `B/σ`, `R/σ`, `σ^{[n]}` | L1153–1194 | standard. `σ^{[n]} = {(a_1..a_n) : ∀i,j (a_i,a_j) ∈ σ}`. |
| linked binary relation | L1190 | subdirect `δ ⊆ A×B` whose bipartite graph is connected. **NB:** this is *linkedness of a relation*; §3.1 separately defines *linkedness of an instance*. |
| bijective binary relation | L1193 | subdirect `δ ⊆ A_1×A_2` with `\|δ\| = \|A_1\| = \|A_2\|`. |
| **parallelogram property** | L1203–1212 | `R` (n-ary) has it if **every permutation** of its variables gives `R'` with: for all `ℓ ∈ {1..n-1}` and all `a,b`: `(a_1..a_ℓ,b_{ℓ+1}..b_n) ∈ R'`, `(b_1..b_ℓ,a_{ℓ+1}..a_n) ∈ R'`, `(b_1..b_ℓ,b_{ℓ+1}..b_n) ∈ R'` ⟹ `(a_1..a_n) ∈ R'`. |
| `i`-th variable rectangular | L1213–1219 | same shape with the split `{i}` vs `[n]\{i}`. Parallelogram ⟹ rectangular. |
| rectangular closure | L1222 | minimal rectangular `R' ⊇ R`. |
| stable under `σ` | L1227–1236 | `(a_1..a_n) ∈ R`, `(a_i,b_i) ∈ σ` ⟹ `(a_1..b_i..a_n) ∈ R`; relation stable = every variable stable. |
| **irreducible congruence** | L1237–1244 | `σ` on `A` is irreducible if it **cannot be represented as an intersection of other binary subalgebras of `A×A` that are stable under `σ`**. Equivalent form given: no `S_1..S_k ≤ A/σ × A/σ` with `0_{A/σ} = ⋂S_i` and `S_i ≠ 0_{A/σ}` for all `i`. |
| `σ^*` (`\cover{σ}`) | L1245–1248 | for irreducible `σ`: the **minimal `δ ≤ A×A` with `δ ⊋ σ` and `δ` stable under `σ`**. |
| **bridge** | L1251–1261 | `δ ≤ D_1^2 × D_2^2` is a bridge from congruence `σ_1` on `D_1` to `σ_2` on `D_2` iff (1) first two variables stable under `σ_1`; (2) last two stable under `σ_2`; (3) `pr_{1,2}(δ) ⊋ σ_1` and `pr_{3,4}(δ) ⊋ σ_2`; (4) `(a_1,a_2,a_3,a_4)∈δ` ⟹ (`(a_1,a_2)∈σ_1` ⟺ `(a_3,a_4)∈σ_2`). |
| `δ̃` | L1277 | `δ̃(x,y) := δ(x,x,y,y)`. |
| perfect linear congruence | L1295–1301 | irreducible `σ` such that ∃`ζ ≤ A×A×Z_p` with `pr_{1,2}ζ = σ^*` and `(a_1,a_2,b)∈ζ ⟹ ((a_1,a_2)∈σ ⟺ b=0)`. |
| linear congruence | L1366–1380 | `σ` irreducible, `σ^*` is a congruence, and ∃ prime `p`, `S ≤ (σ^*)^{[4]}` s.t. every block `B` of `σ^*` has `(B/σ; S∩(B/σ)^4) ≅ (Z_p^n; x_1-x_2=x_3-x_4)`. |
| PC congruence | L1382 | irreducible and not linear. |
| BA / central / S / D / L / PC subuniverses | L1328–1554 | `C <_{BA}^A B` : `C` binary absorbs `B`. `C <_C^A B`: `C` central in `B`. `C <_D^A B`: ∃ irreducible `σ` with (i) `B^2 ⊆ σ^*`, (ii) `C = B ∩ E` for a block `E` of `σ`, (iii) `B/σ` BA-and-center-free. `<_L`/`<_{PC}` = `<_D` with `σ` linear / PC. `C <_S^A B`: ∃ `D ≤ C` simultaneously BA and central in `B`. All require `∅ ≠ C ⊊ B`. Notation `C <_{T(σ)}^A B` names the witnessing congruence (full congruence when `T ∈ {BA,C,S}`). |
| S-free | L1550 | `A` is S-free if there is no `D ≤ A` that is both BA and central, equivalently no `C <_S A`. |
| `⋘` (`\lll`) | L1588–1604 | `C ⋘^A B` iff there is a chain `C = B_n <_{T_n}^A B_{n-1} <_{T_{n-1}}^A ... <_{T_1}^A B_0 = B` with `T_i ∈ {BA,C,S,D}`. `n = 0` allowed (reflexive). `B ⋘ A` abbreviates `B ⋘^A A`. |
| `≤_{T(σ)}` | L1605 | `C ≤_{T(σ)}^A B` iff `C = B` or `C <_{T(σ)}^A B`. |
| `MT` types | L1609–1616 | for `T ∈ {L,PC,D}`: `C <_{MT}^A B` iff `C ≠ ∅` and `C = C_1 ∩ ... ∩ C_t` with each `C_i <_T^A B`. **Note the built-in nonemptiness.** |
| dotted relations | L1628–1637 | `B ⋘̇ A` means `B ⋘ A` **or** `B = ∅`; likewise `<̇_T`, `≤̇_T`. Undotted always means nonempty. |

## 1.1 CSP instances (L1971–1991)

- `An instance I of CSP(Γ) is a list (or conjunction) of constraints of the form R(x_1,...,x_m), R ∈ Γ.`
- `We write C ∈ I meaning that C is a constraint of I.`
- `Var(I)`, `Var(C)` = set of variables appearing in the instance / constraint.
- `Every variable x appearing in an instance has its domain D_x. Every domain can be viewed as an algebra D_x = (D_x; w^{D_x}) ∈ V_m.`
- `A subset of constraints of an instance I is called a subinstance of I.`
- `Then for every constraint R(x_1,...,x_h) the relation R is a subuniverse of D_{x_1} × ... × D_{x_h}.`
- `We say that a solution set of an instance I is subdirect if for every x and every a ∈ D_x the instance has a solution with x = a.`

*Formalization notes.* (i) An instance is a **list**, i.e. a multiset/indexed family, of constraints; the same relation may occur twice, and §3.2/§3.3 rely on being able to *replace one occurrence* of a constraint. Do **not** model instances as sets of constraints. (ii) `Var(C)` is a *set*, while a constraint is `R(x_1..x_m)` with a *tuple* of variables: the paper silently assumes the `x_i` in a constraint are pairwise distinct (see the Expanded-covering definition, which explicitly says "the variables ... are different"). Repeated variables in a scope would break `Con(C,x_i)` (ambiguous `i`). Recommend: model a constraint as `(scope : Fin m ↪ Var, R : Subuniverse (∏ D_{scope i}))`. (iii) "solution" is never defined; it is the obvious `s : ∀x, D_x` with `(s(x_1),...,s(x_m)) ∈ R` for all constraints. (iv) The domain family `D_x` is *part of the instance data*, not of `Γ`; a reduction changes it.

## 1.2 Reductions (L1993–2009)

- `A reduction D^(⊤) for a CSP instance I is a mapping that assigns a subuniverse D_x^(⊤) ≤ D_x to every variable x of I.` (The commented-out word `%nonempty` in the source shows the author deliberately allows `∅`.)
- `D can be viewed as a trivial reduction.`
- `For two reductions D^(⊥) and D^(⊤) we write D^(⊥) ⋘ D^(⊤) and D^(⊥) ≤_T D^(⊤) whenever D_i^(⊥) ⋘ D_i^(⊤) for every i ∈ I and D_i^(⊥) ≤_T D_i^(⊤) for every i ∈ I, respectively.`
- `For an instance I and a reduction D^(⊤) by I^(⊤) we denote the instance whose variables x are restricted to D_x^(⊤).`
- `A reduction D^(⊤) is called nonempty if D_x^(⊤) ≠ ∅ for every x.`

*Formalization notes.* (a) **Notation collision:** "`for every i ∈ I`" — here `I` is an index set of variables, but `I` (script) is the instance. (b) `D^(⊥) ⋘ D^(⊤)` is *pointwise* `D_x^(⊥) ⋘^{D_x?} D_x^(⊤)`; the paper writes both `D^(2) ⋘ D^(1)` and `D^(2) ⋘^D D^(1)` and `D^(2) ≤_T^D D^(1)`, meaning the ambient algebra is `D_x`. Superscript `D` = "relative to the original domain family". Fixing one uniform convention is a prerequisite. (c) `I^(⊤)` is the instance with the same constraint *scopes* and relations `R ∩ ∏ D^(⊤)_{x_i}`, and domains `D^(⊤)_x`. The paper freely writes `C^(2)`, `R^(1)`, `E^{(1)}_1` for such restrictions of arbitrary relations. (d) `D_x^(⊤) ≤ D_x` should be read as "subuniverse", so `∅` is allowed only because subuniverses of idempotent algebras include `∅`.

## 1.3 Induced congruences `Con(R,i)` (L2012–2029)

```
Con(R,i) := σ(y,y') defined by
  ∃x_1...∃x_{i-1}∃x_{i+1}...∃x_n  R(x_1,..,x_{i-1},y,x_{i+1},..,x_n) ∧ R(x_1,..,x_{i-1},y',x_{i+1},..,x_n).
For a constraint C = R(x_1,...,x_n),  Con(C,x_i) := Con(R,i).
For an instance I,  Con(I,x) := { Con(C,x) | C ∈ I }.
Con(I) := ⋃_{x ∈ Var(I)} Con(I,x).
```
Two facts stated inline without proof:
- `the i-th variable of a relation R is rectangular iff R is stable under Con(R,i);`
- `if the i-th variable of a subdirect relation R is rectangular then Con(R,i) is a congruence.`

*Formalization notes.* (a) **Serious notation collision**: `\ConOne` and `\Congruences` both render as `Con`. `Con(R,i)` (a binary relation) and `Con(I,x)` (a *set* of binary relations) are the same glyph, disambiguated only by argument type. Use two names, e.g. `Con1` and `Cons`. (b) `Con(R,i)` is always reflexive on `pr_i(R)` and symmetric, but **transitivity needs rectangularity**; it is a congruence only under subdirectness+rectangularity. The paper calls it "the first coordinate congruence" implicitly everywhere. (c) The two inline facts must be proved (each is 5–15 lines).

## 1.4 Linear-type and PC-type (L2050–2056)

`A relation R is of the PC/Linear type if R is rectangular and each congruence Con(R,i) is a PC/Linear congruence. An instance has the PC/Linear type if all of its constraints are of the PC/Linear type.`

*Note.* "rectangular" for a relation = every variable rectangular (L1213 defines per-variable; "a relation is rectangular" appears in a commented-out block at L2044 but is used in §3 as if defined).

## 1.5 Paths, tree-instances (L2059–2069)

- `z_1 - C_1 - z_2 - ... - C_{l-1} - z_l is a path in I if z_i, z_{i+1} ∈ Var(C_i).`
- `the path connects b and c if there exist a_i ∈ D_{z_i} for every i such that a_1 = b, a_l = c, and the projection of C_i onto z_i,z_{i+1} contains (a_i,a_{i+1}).`
- `I is a tree-instance if there is no path z_1-C_1-...-C_{l-1}-z_l such that l ≥ 3, z_1 = z_l, and all the constraints C_1,...,C_{l-1} are different.`

*Notes.* Paths may repeat variables and constraints; `l = 1` (a bare variable) is a legal path and trivially connects `a` to `a`. The "connects" predicate is evaluated in the **unreduced** domains `D_z`; this is important and is a source of trouble later (Hazard H8). Tree-instance is defined by absence of a *closed* path with distinct constraints, not by acyclicity of a Gaifman graph.

## 1.6 Consistency (L2071–2086)

- `I is 1-consistent if pr_z(C) = D_z for any constraint C of I and any variable z of C.`
- `A reduction D^(⊤) is 1-consistent for I if I^(⊤) is 1-consistent.`
- `I is cycle-consistent if it is 1-consistent and for every variable z and a ∈ D_z any path starting and ending with z in I connects a and a.`

*Notes.* Cycle-consistency quantifies over **all** closed paths at `z` (arbitrarily long, constraints may repeat). Note the asymmetry with §1.2: `D^(⊤)` 1-consistent is defined, `D^(⊤)` cycle-consistent is **never** defined, yet Lemma `LEMFindOneConsistentForAll` needs something very close to it (Hazard H8).

## 1.7 Linkedness, fragmentedness, irreducibility (L2088–2110)

- `I is linked if for every variable z ∈ Var(I) and every a,b ∈ D_z there exists a path starting and ending with z in I that connects a and b.`
- `I is fragmented if Var(I) can be divided into 2 disjoint nonempty sets X_1 and X_2 such that Var(C) ⊆ X_1 or Var(C) ⊆ X_1 for any C ∈ I.` **[sic: the second `X_1` must read `X_2`]**
- `I is irreducible if there is no instance I' satisfying: (1) Var(I') ⊆ Var(I); (2) each constraint of I' is a projection of a constraint of I on some variables; (3) I' is not fragmented; (4) I' is not linked; (5) the solution set of I' is not subdirect.`

*Notes.* (a) `linked` here is a *global* property (all variables at once); [orig L1128] has the same. (b) [orig L1134] additionally requires each `X_i` to contain a variable *in some constraint scope*; 2404's "nonempty" version makes an instance with an isolated variable fragmented. Harmless but different. (c) The definition of `irreducible` is a `¬∃` over *all* instances built from projections of constraints of `I` on subsets of `Var(I)` — a large but finite search space (finitely many subsets × finitely many constraints). Formalizing "instance built from projections" needs care: `I'` is any list of constraints each of which is `pr_X(C)` for `C ∈ I`, `X ⊆ Var(I)`; note `I'` may use several projections of the same `C`, and `Var(I')` may be a strict subset.

## 1.8 Weakening (L2113–2131)

- `R_1(y_1,...,y_t) is weaker or equivalent to R_2(z_1,...,z_s) if {y_1..y_t} ⊆ {z_1..z_s} and R_2(z_1..z_s) implies R_1(y_1..y_t).`
- `C_1 is weaker than C_2 if C_1 is weaker or equivalent to C_2 but C_1 does not imply C_2.`
- `The weakening of a constraint C in an instance I is the replacement of C by all weaker constraints.`
- `I' is a weakening of I if Var(I') ⊆ Var(I) and every constraint of I' is weaker or equivalent to a constraint of I.`

*Formalization notes.* (a) "implies" means: after cylindrification to a common variable set, `R_2^↑ ⊆ R_1^↑`. Define `C^↑ := {s : Var(I) → ∏D | (s(y_1),..,s(y_t)) ∈ R}`; then weaker-or-equivalent = `C_2^↑ ⊆ C_1^↑` **plus** the scope containment `{y} ⊆ {z}`, and "weaker" = additionally `C_1^↑ ⊄ C_2^↑`, i.e. `C_2^↑ ⊊ C_1^↑`. (b) The "all weaker constraints" family is finite up to equivalence but is a set of `(X, R)` pairs over all `X ⊆ Var(C)`; a Lean encoding will want the canonical finite family `{(X, S) : X ⊆ Var(C), S ⊇ pr_X-cylinder of R, (X,S)^↑ ⊋ C^↑}`. (c) **Removing a constraint is a special case**: if `R` is the full product then nothing is strictly weaker, so the weakening deletes it. (d) `I'` a weakening of `I` is *not* required to have one constraint per constraint of `I`; it is a completely separate instance.

## 1.9 Crucial instances (L2133–2153)

- `A variable y_i of the constraint R(y_1,...,y_t) is dummy if R does not depend on its i-th variable.`
- `Let D_i' ⊆ D_i for every i.` **[a dangling, unused sentence]**
- `Suppose D^(⊤) is a reduction for an instance I. A constraint C of I is crucial in D^(⊤) if it has no dummy variables, I^(⊤) has no solutions, but the weakening of C ∈ Θ gives an instance I' with a solution in D^(⊤).` **[`Θ` is a leftover from the original paper; read `C ∈ I`]**
- `An instance I is crucial in D^(⊤) if it has at least one constraint and all its constraints are crucial in D^(⊤).`

**Remark `GetCrucialInstance` (L2146–2153):** `Suppose I^(⊤) has no solutions. Then we can iteratively replace every constraint by all weaker constraints having no dummy variables until it is crucial in D^(⊤). Notice that R ≤ D_{x_1}×...×D_{x_n} for any weaker constraint R(x_1,..,x_n) we introduce.`

*Formalization notes (this remark is a real proof obligation).* (a) **Termination is not argued.** A workable measure: `μ(I) = multiset { |∏_{x∈Var(I)} D_x| − |C^↑| : C ∈ I }` under the Dershowitz–Manna multiset order; each weakening replaces one constraint by finitely many constraints of strictly smaller measure. (b) **Dummy variables:** deleting a dummy variable yields an *equivalent*, not a strictly weaker, constraint, so the phrase "weaker constraints having no dummy variables" needs an extra normalisation step (project away dummy coordinates first). Without it the remark is not literally executable. (c) The invariant maintained is "`I^(⊤)` has no solutions"; the terminal instance is crucial *by definition of crucial*. (d) The final sentence records that all the introduced relations are still subuniverses (pp-definability).

## 1.10 Relations defined by instances (L2155–2167)

`For an instance I and x_1,...,x_n ∈ Var(I), I(x_1,...,x_n) := { (a_1,...,a_n) : I has a solution with x_i = a_i for every i }.` The obtained relation is a subuniverse of `D_{x_1}×...×D_{x_n}` (pp-definable).

*Note.* Used heavily in the form `I^(⊤)(x)`, `Θ^{(2)}(x_0'')`, `Υ_y^{(⊤)}(y)`. When `x_i` repeat this is still fine. The claim "`I(x_1..x_n)` is a subuniverse" needs the (standard) closure of pp-definable relations.

## 1.11 Expanded coverings (L2169–2212)

```
For an instance I, ExpCov(I) is the set of all instances I' such that there exists
S : Var(I') → Var(I) satisfying
 1. if x ∈ Var(I) ∩ Var(I') then S(x) = x;
 2. D_x = D_{S(x)} for every x ∈ Var(I');
 3. for every constraint R(x_1,...,x_n) of I'
      either  S(x_1),...,S(x_n) are pairwise different and R(S(x_1),...,S(x_n)) is weaker or
              equivalent to some constraint of I,
      or      S(x_1) = ... = S(x_n)  and  {(a,a,...,a) | a ∈ D_{x_1}} ⊆ R.
```
- `An expanded covering I' of I is a covering if for every constraint R(x_1,...,x_n) of I' the constraint R(S(x_1),...,S(x_n)) is in I.`
- `An instance is a tree-covering if it is a covering and also a tree-instance.`
- `S(x)` is **the parent** of `x`, `x` is **a child** of `S(x)`; same terminology for constraints.

Eight asserted properties `(p1)–(p8)` ("The following easy facts can be derived from the definition"):

| tag | statement |
|---|---|
| (p1) | replacing every `x` by `S(x)` in an expanded covering of `I` (and removing all constraints `R(x,x,...,x)`) gives a **weakening** of `I` |
| (p2) | a weakening is an expanded covering with `S(x) = x` for every `x` |
| (p3) | any solution of an instance can be naturally expanded to a solution of its expanded covering |
| (p4) | if an instance is 1-consistent and its expanded covering is a **tree-covering**, then the solution set of the covering is **subdirect** |
| (p5) | the union (union of all constraints) of two expanded coverings is an expanded covering |
| (p6) | an expanded covering of an expanded covering is an expanded covering |
| (p7) | an expanded covering of a cycle-consistent irreducible instance is cycle-consistent and irreducible (= Lemma `LEMExpandedConsistencyLemma`) |
| (p8) | any reduction of an instance can be naturally extended to its expanded covering; moreover, if the reduction was 1-consistent for the instance, it is 1-consistent for the covering |

*Formalization notes.* (a) The definition text writes `Var(Ω')`, `Var(Ω)`, "some constraint of `Ω`" — `Ω` is a leftover name for the instance; read `I'`, `I`, `I`. (b) `ExpCov` is `\Expanded`; the paper never writes `Expanded(I)` in prose, only `ExpCov(I)`. (c) `S` is part of the data but the definition is phrased as "there exists `S`"; downstream, `S` is used (parent/child), so in practice an expanded covering is a *pair* `(I', S)`. This existential-vs-structure slip must be resolved. (d) (p1)–(p8) are eight separate lemmas. (p4) is the workhorse (used in `CORExistenceOfTreeCoverings`, `LEMFindOneConsistentForAll`, §3.3) and is *not* trivial: it is an induction over the tree using 1-consistency. (p7) is an imported result [orig Lemma 6.1, proof at orig L1225–1256] whose proof is about a page and uses cycle-consistency to glue paths. (p5) needs the two `S`-maps to agree, which is not stated. (p8)'s "naturally extended" means `D^{(⊤)}_x := D^{(⊤)}_{S(x)}`.

## 1.12 Connected instances (L2214–2227)

- `A bridge δ ⊆ D^4 is reflexive if (a,a,a,a) ∈ δ for every a ∈ D.`
- `Two congruences σ_1, σ_2 on D_x are adjacent if there exists a reflexive bridge from σ_1 to σ_2.`
- `Since we can always put δ(x_1,x_2,x_3,x_4) = σ(x_1,x_3) ∧ σ(x_2,x_4), any proper congruence σ is adjacent with itself.`
- `Two rectangular constraints C_1 and C_2 are adjacent in a common variable x if Con(C_1,x) and Con(C_2,x) are adjacent.`
- `An instance I is connected if all its constraints are rectangular, all the congruences of Con(I) are irreducible, and the graph whose vertices are constraints and edges are adjacent constraints is connected.`

*Formalization notes.* (a) A reflexive bridge is only defined when `σ_1,σ_2` live on the **same** `D` (`δ ⊆ D^4`); "adjacent" is therefore intra-variable. (b) The self-adjacency remark silently requires `σ` **proper** (`σ ≠ D^2`), matching Hazard H1. (c) In the "connected" graph, edges join constraints adjacent *in some common variable* — the variable is existentially quantified; the graph is on the multiset of constraints. (d) `δ̃ ⊇ Δ` ⟺ `δ` reflexive; this equivalence is used silently in §3.2 and §3.3.

---

# 2. Statement inventory for §3.2

Line counts are of `main.tex`; "live" excludes `%`-commented lines and blanks. §3.2 contains **11** numbered items. Two are imported verbatim from earlier papers with no proof.

| # | Label | Kind | Lines (stmt+proof) / live | Statement (faithful) | Proof cites |
|---|---|---|---|---|---|
| 1 | `LEMExpandedConsistencyLemma` | Lemma ([zhuk2020proof], Lemma 6.1) | 2254–2258 / 5, **no proof** | `I` cycle-consistent irreducible, `I' ∈ ExpCov(I)` ⟹ `I'` cycle-consistent and irreducible. | — (external) |
| 2 | `LEMMinimalPCLinearReductionIsConsistent` | Lemma | 2262–2294 / 27 | Suppose (1) `D^(1)` is a 1-consistent reduction for `I`; (2) `D_x^(1)` is S-free for every `x ∈ Var(I)`; (3) `T ∈ {PC,L,D}`; (4) `D^(1) ⋘ D`; (5) `D_x^(2) ≤_{MT} D_x^(1)` is a **minimal** `MT` subuniverse for every `x`. Then either some constraint has `C^(2) = ∅`, or `I^(2)` is 1-consistent. | `LEMPropagation`(fm) |
| 3 | `LEMCrucialMeansIrreducible` | Lemma | 2298–2318 / 20 | `R(x_1..x_n)` a **rectangular** constraint of a **1-consistent** instance `I`, crucial in `D^(⊤)` ⟹ `Con(R,i)` is an irreducible congruence for every `i ∈ [n]`. | — (self-contained) |
| 4 | `LEMBridgeFromRelation` | Lemma | 2320–2343 / 24 | `R ≤_sd A_1×...×A_n`, first and last variables of `R` rectangular, and ∃ `(b_1,a_2,..,a_n), (a_1,..,a_{n-1},b_n) ∈ R` with `(a_1,..,a_n) ∉ R`. Then ∃ bridge `δ` from `Con(R,1)` to `Con(R,n)` with `δ̃ = pr_{1,n}(R)`. | — (self-contained) |
| 5 | `LEMConnectedProperties` | Lemma (3 parts) | 2345–2423 / 59 | `I` cycle-consistent **connected**. Then **(a)** any two constraints with a common variable are adjacent; **(b)** for any `C_1,C_2 ∈ I`, `x_1 ∈ Var(C_1)`, `x_2 ∈ Var(C_2)`, and any path from `x_1` to `x_2`, ∃ bridge `δ` from `Con(C_1,x_1)` to `Con(C_2,x_2)` with `δ̃` containing all pairs connected by this path; **(p)** if `I` is **linked** then `Con(C,x)` is a **perfect linear congruence** for every `C ∈ I`, `x ∈ Var(C)`. | `LEMBridgeFromRelation`, `LEMBridgeComposition`, `LEMBuildingPerfectCongruence` |
| 6 | `LEMExistenceOfTreeCoverings` | Lemma ([zhuk2021strong], Lemma 5.6) | 2425–2434 / 10, **no proof** | `D^(⊤)` a reduction for `I`, `D^(⊥)` an inclusion-**maximal** 1-consistent reduction with `D^(⊥) ≤ D^(⊤)`. Then for every `y ∈ Var(I)` there exists a **tree-covering** `Υ_y` of `I` such that `Υ_y^(⊤)(y)` defines `D_y^(⊥)`. | — (external) |
| 7 | `CORExistenceOfTreeCoverings` | Corollary | 2436–2455 / 20 | `D^(⊤)` a reduction of a 1-consistent `I`, `D^(⊤) ⋘ D`, `D^(⊥)` an inclusion-maximal **nonempty** 1-consistent reduction with `D^(⊥) ≤ D^(⊤)`. Then `D^(⊥) ⋘^D D^(⊤) ⋘ D`. | `LEMExistenceOfTreeCoverings`, `CORPropagateToRelations`(r1), (p4) |
| 8 | `LEMFindOneConsistentForAll` | Lemma | 2457–2506 / 47 | `D^(1)` a 1-consistent reduction of a **cycle-consistent** `I`, `D^(1) ⋘ D`, `B <_T^{D_x} D_x^(1)` for some variable `x`, `T ∈ {BA,C,PC}`. Then there exists a **nonempty** 1-consistent reduction `D^(2) ⋘ D^(1)` with `D_x^(2) ≤ B`. Moreover (1) if `T ∈ {BA,C}` then `D^(2) ≤_T D^(1)`; (2) if `T = PC` and every `D_y^(1)` is S-free then `D^(2) ≤_{MPC} D^(1)`. | `LEMExistenceOfTreeCoverings`, `CORMainStableIntersection`, `LEMBACenterImplies`, `CORPropagateToRelations`(rm)†, (p4) |
| 9 | `LEMParalPropertyFromCrucialInMultiType` | Lemma | 2574–2731 / 100 | Suppose (1) `D^(1)` is a 1-consistent reduction for a **constraint** `R(x_1..x_n)`; (2) `T ∈ {L,PC,D}`; (3) `D^(2) ≤_{MT}^D D^(1) ⋘ D`; (4) `R(x_1..x_n)` is crucial (**as the whole instance**) in `D^(2)`. Then `R` has the **parallelogram property** and `Con(R,i)` is a congruence of type `T` with `Con(R,i)^* ⊇ (D_{x_i}^{(1)})^2` for every `i ∈ [n]`. Moreover, if `T = PC` then `n = 2`. | `CORPropagateToRelations`(r),(m),(r1), `LEMPreserveLinkdness`, `CORMainStableIntersection` (×2), `LEMMaximalMultExtention`, `LEMCrucialMeansIrreducible` |
| 10 | `LEMGetABridgeFromSubdirectPCLinearInstance` | Lemma | 2856–3038 / 140 | Suppose (1) `I` has a **subdirect solution set**; (2) `D^(1)` is a reduction with `D_x^(1) ⋘ D_x` for every `x`; (3) `C ∈ I` is a constraint **of type `T ∈ {PC,L}`**; (4) `B <_{𝒯(ξ)}^{D_z} D_z^(1)` for some variable `z`, `𝒯 ∈ {BA,C,S,PC,L}`; (5) if `T = PC` then `𝒯 ∈ {PC,L}`; (6) `I^(1)` has a solution; (7) `I^(1)` has no solutions with `z ∈ B`; (8) weakening of `C` in `I` gives an instance with a solution in `D^(1)` and `z ∈ B`. Then **`𝒯 = T`** and for **any** variable `x` of `C` there exists a bridge `δ` from `ξ` to `Con(C,x)` such that `δ̃ ⊇ I(z,x)`. | `CORMainStableIntersection` (×2), `CORPropagateToRelations`(r1), `LEMUbiquity`, `CORPropagateMultiplyByCongruence`(f), `LEMBACenterImplies`, `CORPropagationModuloCongruence`(s) |
| 11 | `CORSameTypeReductionAndConstraint` | Corollary | 3385–3405 / 20 | `I` with subdirect solution set, `D^(1),D^(2)` reductions, `I^(1)` has a solution, `D^(2) ≤_T^D D^(1) ⋘ D` with `T ∈ {BA,C,S}`, `C ∈ I` of type `L`. Then `C` is **not crucial** in `D^(2)`. | `LEMGetABridgeFromSubdirectPCLinearInstance` |

† the source writes `CORPropagateToRelations(rm)`; there is no item `(rm)` in that corollary — items are `(r),(r1),(b),(b1),(m),(m1)`. Intended: `(m1)`.

## 2.1 One-to-three-sentence proof digests

**#2 `LEMMinimalPCLinearReductionIsConsistent`.** If no `C^(2)` is empty, fix a constraint `R(x_1..x_n)`; propagate `D^(2) ≤_{MT} D^(1)` through the relation to get `pr_i(R^(2)) ≤_{MT} D_{x_i}^(1)`, then use minimality of `D_{x_i}^(2)` to conclude `pr_i(R^(2)) = D_{x_i}^(2)`, i.e. 1-consistency. Consumes: relation-propagation of `MT` types under surjective projections and **S-freeness** (needed by `LEMPropagation`(fm)/`CORPropagateToRelations`(m1)).

**#3 `LEMCrucialMeansIrreducible`.** Suppose `Con(R,1) = ω_1 ∩ ω_2` with both `ω_j ⊋ Con(R,1)` binary subalgebras stable under `Con(R,1)`; define `R_j(x_1,..,x_n) = ∃y (R(y,x_2,..,x_n) ∧ ω_j(y,x_1))`; then `R ⊊ R_j` (1-consistency) and `R = R_1 ∩ R_2` (rectangularity + stability), so `R` can be replaced by two weaker constraints without creating a solution, contradicting cruciality. Consumes: nothing from §2 — but uses the *definition* of irreducible congruence and of rectangular.

**#4 `LEMBridgeFromRelation`.** Take `δ(x_1,x_2,y_1,y_2) = ∃z_2..z_{n-1} R(x_1,z̄,y_1) ∧ R(x_2,z̄,y_2)`; rectangularity of the two end variables gives bridge-condition (4); the assumed pair of tuples supplies `(b_1,a_1,a_n,b_n) ∈ δ` with `(b_1,a_1) ∉ Con(R,1)`, giving condition (3); `δ̃ = pr_{1,n}(R)` by inspection. Consumes: nothing.

**#5 `LEMConnectedProperties`.** (a) Walk along a path in the connectivity graph from `C_1` back to `C_2` through `x`; alternate the "internal" bridges `δ_i` from `LEMBridgeFromRelation` with the reflexive "adjacency" bridges `ω_j`, compose all of them by `LEMBridgeComposition` (legal because connectivity guarantees all `Con(C,z)` are irreducible), and use cycle-consistency to see that the composite is reflexive. (b) Same computation along an arbitrary path, now legal because (a) already gives adjacency at every shared variable. (p) Compose the bridges `δ_{a,b}` obtained from (b) over all pairs `a,b ∈ D_x`; the result has `δ̃ = D_x^2`, so `LEMBuildingPerfectCongruence` applies. Consumes: `LEMBridgeComposition` ([zhuk2020proof] 6.3), `LEMBuildingPerfectCongruence` ([zhuk2020proof] 8.17.1).

**#7 `CORExistenceOfTreeCoverings`.** Get tree-coverings `Υ_y` with `Υ_y^(⊤)(y) = D_y^(⊥)`; their solution sets are subdirect by (p4); apply `CORPropagateToRelations`(r1) to conclude the chain `⋘`.

**#8 `LEMFindOneConsistentForAll`.** Set `D^(⊤)` = `D^(1)` except `D_x^(⊤) = B`, and let `D^(2)` be the inclusion-maximal 1-consistent reduction below it. Non-emptiness: if some `Υ_y^(⊤)` had no solution, `CORMainStableIntersection` on the (subdirect) solution set of the tree-covering would force exactly **two** children of `x` to be responsible, which contradicts cycle-consistency of `I` (the tree path between two children of `x` projects to a closed path at `x`). The "moreover" clauses come from `LEMBACenterImplies` (for `BA`,`C`) and `CORPropagateToRelations`(m1) (for `PC`).

**#9 `LEMParalPropertyFromCrucialInMultiType`.** Part 1 (parallelogram): for each 2-block split, view `R` as a binary `R' ≤_sd E_1 × E_2`, set `S' = R'∘R'^{-1}∘R'`; since `R'^{(2)} = ∅`, `LEMPreserveLinkdness` forces `S'^{(2)} = ∅`; cruciality then forces `S = R`. Part 2 (type of `Con(R,i)`): let `E = pr_1(R ∩ (D_{x_1} × D^{(2)}_{x_2} × ... × D^{(2)}_{x_n}))`; cruciality gives `E ≠ ∅`, `E ∩ D_{x_1}^{(2)} = ∅`; choose `C <_{MT}^{D_{x_1}} B ⋘ D_{x_1}` separating `E`; show the maximal congruence `σ` with `(E∘σ)∩C = ∅` equals `Con(R,1)` (else weaken the constraint by `σ`); `LEMMaximalMultExtention` writes `σ` as an intersection of type-`T` congruences with `ω_i^* ⊇ B^2` and `LEMCrucialMeansIrreducible` collapses that intersection to a single one. Part 3 (`T = PC ⟹ n = 2`): `CORMainStableIntersection` yields two coordinates `i,j` such that `R` avoids `B_i × B_j`; if `n ≥ 3`, `pr_{i,j}(R)` is a strictly weaker constraint with no solution in `D^(2)`.

**#10 `LEMGetABridgeFromSubdirectPCLinearInstance`.** Build `Θ` = a renamed copy of `I` in which the occurrence of `x_0` inside `C` is split off as `x_0''` and reconnected by the constraint `ω^*(x_0',x_0'')` with `ω = Con(C,x_0)`. Take `D^(⊤)` **minimal** in the `⋘`-interval `[D^(1), D]` for which the coupled instance `Θ^{(2)} ∧ I^{(⊤)} ∧ ω(x_0,x_0'')` has a solution, and `D^(⊥)` one step below at a variable `y` with witness `G <_{𝒯_0(ν)} D_y^{(⊤)}`; `CORMainStableIntersection` on the coupled instance gives `𝒯 = 𝒯_0` and a bridge `δ'` from `ξ` to `ν`. Then localise: `F := Θ^{(2)}(x_0'') ∩ (I^{(⊤)}(x_0)∘ω)` satisfies `F∘ω = F` and `F ⋘ D_{x_0}`, and `LEMUbiquity` (iterated) produces a single `ω`-block `E` with `{E} ⋘ F/ω`. Case `T = L`, `𝒯 ∈ {BA,C,S}` gives a BA/central subuniverse inside a block of `ω^*` — impossible for a linear congruence. Case `𝒯 ∈ {PC,L}` produces a second bridge `δ''` from `ν` to a congruence `ζ` which must equal `ω`; composing `δ'` and `δ''` finishes.

**#11 `CORSameTypeReductionAndConstraint`.** Take `D^(⊤)` minimal among the `2^{|Var|}` mixtures of `D^(1)` and `D^(2)` for which `I^(⊤)` has a solution; pick `z` with `D_z^(⊤) = D_z^(1)`, put `B = D_z^(2)`, and apply #10, whose conclusion `𝒯 = T` contradicts `T ∈ {BA,C,S}` vs constraint type `L`.

---

# 3. Dependency graph

## 3.1 Inside §3.2 (local edges)

```
LEMBridgeFromRelation ──────────────► LEMConnectedProperties (a),(b)
LEMCrucialMeansIrreducible ─────────► LEMParalPropertyFromCrucialInMultiType
LEMExistenceOfTreeCoverings ───┬────► CORExistenceOfTreeCoverings      [orphan, see below]
                               └────► LEMFindOneConsistentForAll
LEMGetABridgeFromSubdirectPCLinearInstance ─► CORSameTypeReductionAndConstraint
LEMExpandedConsistencyLemma  ─── (only cited as fact (p7) in §3.1) ───► (nothing in §3.2)
```
`CORExistenceOfTreeCoverings` is **never cited anywhere** in `main.tex`, `StrongSubalgebras.tex`, `XYSymmetric.tex` or `necessaryClaims.tex` — it is dead weight (and, as noted in H10, under-justified). Safe to drop from a blueprint.

## 3.2 Edges into §3.2 from §2 / §2.4 (what §3.2 consumes)

```
LEMMinimalPCLinearReductionIsConsistent  ← LEMPropagation(fm)                       [main.tex L1659]
LEMConnectedProperties                   ← LEMBridgeComposition                     [necessaryClaims L23; zhuk2020proof 6.3]
                                         ← LEMBuildingPerfectCongruence             [necessaryClaims L14; zhuk2020proof 8.17.1]
CORExistenceOfTreeCoverings              ← CORPropagateToRelations(r1)               [L1726]
LEMFindOneConsistentForAll               ← CORMainStableIntersection                 [L1803]
                                         ← LEMBACenterImplies                        [L1753; zhuk2021strong 6.1.2, 6.9.2]
                                         ← CORPropagateToRelations("rm" → (m1))      [L1726]
LEMParalPropertyFromCrucialInMultiType   ← CORPropagateToRelations(r),(m),(r1)       [L1726]
                                         ← LEMPreserveLinkdness                      [L1873]
                                         ← CORMainStableIntersection                 [L1803]
                                         ← LEMMaximalMultExtention                   [L1888]
LEMGetABridgeFromSubdirectPCLinearInstance ← CORMainStableIntersection               [L1803]
                                         ← CORPropagateToRelations(r1)               [L1726]
                                         ← LEMUbiquity                               [L1653]
                                         ← CORPropagateMultiplyByCongruence(f)       [L1713]   (should be CORPropagateFromFactor(f), L1699)
                                         ← LEMBACenterImplies                        [L1753]
                                         ← CORPropagationModuloCongruence(s)         [L1682]
                                         ← (silent) LEMNoAbsCenterPCInLinearAlgebra  [necessaryClaims L69]
                                         ← (silent) LEMNoBridgeBetweenDifferentTypes [L1405]
                                         ← (silent) LEMIntersectALL(i)               [L1762]
                                         ← (silent) CORPropagationModuloCongruence(f)[L1682]
                                         ← (silent) LEMBridgeComposition             [necessaryClaims L23]
```
**Section-2 hot spots**, by number of consumers in §3.2: `CORMainStableIntersection` (5 uses across 3 lemmas), `CORPropagateToRelations` (5), `LEMBACenterImplies` (2), `CORPropagateMultiplyByCongruence` (2), `LEMExistenceOfTreeCoverings` (2). `CORMainStableIntersection` + the Remark at L1838 ("we can always duplicate the coordinate of the relation and apply restrictions separately") is *the* engine of §3.2/§3.3 and must be formalised in a shape that supports the duplication trick natively (i.e. an indexed family of restrictions per coordinate, not one per coordinate).

## 3.3 Edges out of §3.2 into §3.3–§3.4 (who consumes §3.2)

```
LEMGetABridgeFromSubdirectPCLinearInstance ── 6 uses (THMMainInductiveCSPClaim, THMPCDoesnotKillAllSolutions)
LEMConnectedProperties                      ── 5 uses
LEMFindOneConsistentForAll                  ── 4 uses
LEMParalPropertyFromCrucialInMultiType      ── 2 uses (L3543, L4064)
LEMMinimalPCLinearReductionIsConsistent     ── 2 uses (L3531, L4043)
CORSameTypeReductionAndConstraint           ── 1 use  (L3489)
LEMExistenceOfTreeCoverings                 ── 2 uses (L3558, and inside §3.2)
LEMExpandedConsistencyLemma                 ── 0 direct uses (implicit via (p7))
LEMBridgeFromRelation, LEMCrucialMeansIrreducible ── 0 direct uses outside §3.2
CORExistenceOfTreeCoverings                 ── 0 uses anywhere
```
Note also that §3.3 contains **dangling references** to labels that do not exist in this paper (leftovers from [orig]): `\ref{PathInConnectedComponent}`, `\ref{LinkedLink}`, `\ref{CriticalMeansIrreducible}`, `\ref{LEMCrucialMeansRectangular}`, `\ref{LEMMinimalContainingIsMinimal}`, `\ref{CorretnessSection}` — most are inside comments, but `LEMMinimalContainingIsMinimal` (a *deleted* lemma, L1864–1870 commented out) is genuinely needed at L3527 to know that the "minimal `MT` subuniverse containing `s(x)`" is a minimal `MT` subuniverse, i.e. exactly hypothesis 5 of `LEMMinimalPCLinearReductionIsConsistent`. **That is a live hole in §3.3 which §3.2's hypothesis 5 exposes.**

---

# 4. The five hardest statements (formalization cost centres)

Ranked by (proof length) × (number of hypotheses) × (density of implicit steps).

### 1. `LEMGetABridgeFromSubdirectPCLinearInstance` (L2856–3038) — **by far the worst**
183 source lines, 140 live, 8 numbered hypotheses, a two-case analysis, three auxiliary instances (`I`, `Θ`, and the coupled `Θ ∧ I ∧ ω(x_0,x_0'')`), two nested minimality choices (`D^(⊤)` minimal in a `⋘`-interval, then `E',E''` from a `⋘`-chain), an iterated application of `LEMUbiquity` down to a singleton in a quotient, and two applications of `CORMainStableIntersection` whose hypothesis-checking is entirely omitted. The conclusion `𝒯 = T` is obtained only by chaining `𝒯 = 𝒯_0 = T_0 = type(ζ) = type(ω) = T` across the two cases; one link (`ζ = ω`) is a one-sentence argument that needs the minimality of `σ^*`. The paper's own history is a warning: three earlier versions of this lemma are commented out immediately after it (L3041–3383), with different hypothesis lists and different conclusions. Budget: this is a whole Lean file.

### 2. `LEMParalPropertyFromCrucialInMultiType` (L2574–2731)
158 lines, 100 live, 4 hypotheses but three logically independent conclusions (parallelogram property; congruence type + `Con(R,i)^* ⊇ (D^{(1)}_{x_i})^2`; `n=2` for `PC`). The parallelogram part needs the `2^{n-1}`-fold splitting argument plus `LEMPreserveLinkdness` (itself a hard §5 lemma proved over ~200 lines in `StrongSubalgebras.tex`). The type part needs a delicate "walk up the `⋘` chain until `E` becomes non-empty" construction and a maximal-congruence argument. Also the whole lemma is stated for the **one-constraint instance**, and the "crucial (as the whole instance)" parenthetical is load-bearing.

### 3. `LEMConnectedProperties` (L2345–2423)
Only 59 live lines but it is where the *bridges-in-instances* theory lives, it has three parts, and its proof of (a) **applies `LEMBridgeFromRelation` without checking that lemma's third hypothesis** (see H4). In [orig] the same result (Theorem 8.22) took 1.5 pages and relied on *critical* relations (Lemmas 8.10/8.21) precisely to supply that hypothesis. Formalizing this honestly means re-importing the criticality machinery that 2404 tried to delete.

### 4. `LEMFindOneConsistentForAll` (L2457–2506)
47 live lines, but three types (`BA`, `C`, `PC`) with genuinely different arguments compressed into one paragraph; the `BA` case is **not covered** by the cited `CORMainStableIntersection` (its case `(ba)` permits `n > 2`), and the cycle-consistency step needs the closed path to be realisable inside `D^(1)` (see H8). In [orig] this is Theorem 9.2 + Theorem 9.3, roughly 2 pages, with four separate corollaries invoked by case.

### 5. `LEMMinimalPCLinearReductionIsConsistent` (L2262–2294)
Short (27 live lines) but disproportionately dangerous: hypothesis 5 says *minimal `MT` subuniverse* while the proof uses *minimal `MD` subuniverse* (H6), the cited lemma is arguably the wrong one (`LEMPropagation`(fm) instead of `CORPropagateToRelations`(m1)), and its hypothesis 5 is exactly what §3.3 fails to establish because the supporting lemma `LEMMinimalContainingIsMinimal` was commented out of the paper. It is also used twice downstream, including in the proof of `THMCodimensionOneTheorem` (L4043).

Runner-up worth flagging: `LEMExistenceOfTreeCoverings` is stated without proof ([zhuk2021strong] Lemma 5.6) and is the single most structurally demanding *imported* result — it asserts that maximal 1-consistent reductions are computed by tree-coverings. Every use of it in §3.2 and §3.3 depends on (p4). A blueprint must either import it as an axiom-with-citation or budget a full development.

---

# 5. Formalization hazards

Ordered roughly by severity.

**H1 — "irreducible congruence" silently means *proper*.** 2404 L1237 drops the word "proper" that [orig L1138] has ("`σ` is irreducible if it is **proper** and it cannot be represented as ..."). With 2404's wording, whether `σ = A^2` is irreducible depends on the empty-intersection convention (`⋂∅ = A^2`), and `σ^*` (the minimal `δ ⊋ σ` stable under `σ`) does not exist for `σ = A^2`. Every use of `σ^*` and every bridge (condition `pr_{1,2}(δ) ⊋ σ_1`) presupposes properness. **Fix: add `σ ≠ A^2` to the definition.** Also 2404 requires the `δ_i` in the definition to be *subalgebras* while [orig] says *binary relations*; check that the intended meaning (subalgebras) is what `LEMCrucialMeansIrreducible` and `LEMMaximalMultExtention` both use.

**H2 — `Con` is overloaded.** `Con(R,i)` (binary relation) vs `Con(I,x)` / `Con(I)` (sets of binary relations) share one glyph.

**H3 — `LEMCrucialMeansIrreducible`: typo + omitted step.** The proof defines `R_j(x_1..x_n) = ∃y (R(y,x_2,..,x_n) ∧ ω_1(y,x_1))` for **both** `j ∈ {1,2}` — must be `ω_j`. It also says "still be without a solution in `D^(1)`" where the reduction is `D^(⊤)`. And the key step `R = R_1 ∩ R_2` requires using **stability of `ω_j` under `Con(R,1)`** (part of the definition of irreducible) — [orig Lemma 8.11] spells this out ("Since `δ_j` is stable under `σ`, we may assume that `x'_1` takes the same value"), 2404 does not.

**H4 — `LEMConnectedProperties` applies `LEMBridgeFromRelation` without its third hypothesis. This is a genuine gap.** `LEMBridgeFromRelation` needs tuples `(b_1,a_2..a_n),(a_1,..,a_{n-1},b_n) ∈ R` with `(a_1..a_n) ∉ R`. Equivalently, it needs: *not* every "slice" `R_z = {(u,v) : (u,z̄,v) ∈ R}` (`z̄` = values of the middle coordinates) is a direct product. In the degenerate case (`R_z = P_z × Q_z` for all `z̄`), the constructed `δ` satisfies `pr_{1,2}(δ) = Con(R,1)` exactly and is **not** a bridge. Concrete witness that "connected + cycle-consistent" does not exclude it: `R = {(x,z,y) ∈ Z_4 × Z_2 × Z_4 : x ≡ z ≡ y (mod 2)}` — subdirect, has the parallelogram property, `Con(R,1) = Con(R,3) = (mod 2)` and `Con(R,2) = 0_{Z_2}` are all proper irreducible congruences, the one-constraint instance is 1-consistent, cycle-consistent and (trivially) connected, and every slice is a product. In [orig], the corresponding Lemma 8.21 assumes `ρ` is **critical** and derives the tuples from Lemma 8.10; 2404 removed criticality from the vocabulary without replacing the argument. **Fix options:** (i) add "every constraint relation is critical (`R ⊊ ⋂_i ∃x_i R`)" to the definition of *connected*, which is available in the intended applications since crucial ⟹ critical; or (ii) restate `LEMConnectedProperties` with that hypothesis. Do not skip: the whole bridge-composition chain in (a),(b),(p) rests on it.

**H5 — `LEMConnectedProperties`(p) misattributes its hypothesis.** "Since `I` is **connected**, for any `a,b ∈ D_x` there exists a path from `x` to `x` connecting `a` and `b`" — that is the definition of **linked**, which is the actual hypothesis of (p). Harmless as a typo, fatal if transcribed literally.

**H6 — `LEMMinimalPCLinearReductionIsConsistent`: `MT` vs `MD` mismatch.** Hypothesis 5 assumes `D_x^{(2)}` is a **minimal `MT`** subuniverse; the proof derives `pr_i(R^{(2)}) ≤_{MD}^{D_{x_i}} D_{x_i}^{(1)}` and then says "Since `D_{x_i}^{(2)}` is a minimal subuniverse `B` such that `B ≤_{MD}^{D_{x_i}} D_{x_i}^{(1)}` ...". Minimality among `ML`-subuniverses does **not** give minimality among `MD`-subuniverses. Either the propagation step should preserve `MT` (it does — `CORPropagateToRelations`(m1) and `LEMPropagation`(fm) both keep the same `T`), in which case `MD` is a slip; or hypothesis 5 must be strengthened. Also, the cited `LEMPropagation`(fm) is a statement about a surjective homomorphism `f : A → A'`; applied here with `f = pr_i` its ambient algebra is `pr_i(R)`, not `D_{x_i}`, so the superscript in the displayed conclusion is wrong. Cleanest: cite `CORPropagateToRelations`(m1).

**H7 — `LEMFindOneConsistentForAll`: the `BA` case is not covered by the cited corollary.** The proof says "By `CORMainStableIntersection` there should be **two** children of `x` ...". But when all restrictions have type `BA`, the corollary's case `(ba)` allows arbitrarily many coordinates, so no contradiction with cycle-consistency is produced. [orig] handles `BA` by a separate lemma (Lemma 7.5) and central/PC by `k = 2` vs `k ≥ 3` sub-cases (Corollaries 7.10.3, 7.13.3, 8.26.1). The `BA`/`C` case is in fact easy from `LEMBACenterImplyIntersection` (`StrongSubalgebras.tex` L108: `B ≤_T A`, `C ≤ A` ⟹ `B ∩ C ≤_T C`, **non-empty**), but the paper's ordering (nonemptiness first, type second) hides this.

**H8 — cycle-consistency is stated over `D`, used over `D^{(1)}`.** In `LEMFindOneConsistentForAll` the contradiction requires that restricting only two children of `x` to `B` still leaves a solution of `Υ_y^{(1)}` — i.e. a path realisable **inside the reduced domains**. Cycle-consistency of `I` only guarantees a realisation inside `D`. 1-consistency of `D^{(1)}` does **not** imply `I^{(1)}` is cycle-consistent. Either prove preservation (unlikely in general) or restructure the argument. The same tension recurs implicitly whenever §3.3 says "the bridge is reflexive because ... `I` is cycle-consistent".

**H9 — `GetCrucialInstance` (Remark) has no termination argument and mishandles dummy variables.** See §1.9 notes. A multiset measure works, but "replace by all weaker constraints *having no dummy variables*" is not implementable as stated, because dropping a dummy coordinate produces an *equivalent*, not strictly weaker, constraint.

**H10 — `CORExistenceOfTreeCoverings` is both unused and under-justified.** Its conclusion `D^(⊥) ⋘^D D^(⊤)` is *relative* to `D^(⊤)`, but the cited `CORPropagateToRelations`(r1) yields only `Υ_y^{(⊤)}(y) ⋘̇ D_y` (relative to `D_y`). Getting the relative statement needs (b1) with a different instantiation and still does not obviously land on `⋘^{D_y} D_y^{(⊤)}`. Recommend dropping it.

**H11 — Wrong lemma cited in `LEMGetABridgeFromSubdirectPCLinearInstance`.** "`By Corollary CORPropagateMultiplyByCongruence(f) E ⋘ F`" — the step is `{E} ⋘^{D/ω} F/ω ⟹ E = E∘ω ⋘ F∘ω = F`, which is `CORPropagateFromFactor`(f), not `CORPropagateMultiplyByCongruence`(f). (The earlier commented-out version of the proof, L3126, cited `CORPropagateFromFactor(f)` correctly — this is a regression.) Also `F ⋘ D_{x_1}` should read `F ⋘ D_{x_0}`, and `δ̃'' = Θ(y'',x_0'')` should read `Θ(y',x_0'')` (`y''` is not a variable of `Θ`). Two silent steps in the same paragraph: `F/ω ⋘ D_{x_0}/ω` needs `CORPropagationModuloCongruence`(f), and `F = Θ^{(2)}(x_0'') ∩ (I^{(⊤)}(x_0)∘ω) ⋘ D_{x_0}` needs `LEMIntersectALL`(i) on top of `CORPropagateToRelations`(r1).

**H12 — `𝒯 = S` is not handled in Case 1 of `LEMGetABridgeFromSubdirectPCLinearInstance`.** Case 1 assumes `𝒯 ∈ {BA,C,S}` and immediately applies `LEMBACenterImplies`, which is only stated for `T ∈ {BA,C}`. Presumably one replaces `B` by the BA-and-central witness `D ≤ B` from the definition of `<_S`, but the paper does not say so. Also the final contradiction ("a BA or central subuniverse in a block of `ω^*`, which contradicts the properties of a linear congruence") is exactly `LEMNoAbsCenterPCInLinearAlgebra` (`necessaryClaims.tex` L69) plus the block structure `B/σ ≅ Z_p^n` from the definition of a linear congruence — neither is cited.

**H13 — `LEMParalPropertyFromCrucialInMultiType`, part 2: `R_0 ⊋ R` needs `pr_1(R) = D_{x_1}`.** The step "if `σ ⊋ Con(R,1)` then we weaken `R` to `R_0(x_1..x_n) = ∃z R(z,x_2..x_n) ∧ σ(z,x_1)`" produces a *strictly* weaker constraint only if the extra `σ`-pairs meet `pr_1(R)`. The hypotheses give 1-consistency of `D^{(1)}` for the constraint, i.e. `pr_i(R^{(1)}) = D_{x_i}^{(1)}`, **not** `pr_i(R) = D_{x_i}`. Either add subdirectness of `R` over `D` as a hypothesis (which the surrounding development probably supplies) or restrict `σ` to `pr_1(R)`.

**H14 — `LEMParalPropertyFromCrucialInMultiType`, part 3: the two coordinates might coincide.** `CORMainStableIntersection` is applied with duplicated coordinates (per the Remark at L1838), so the returned pair `(i,j)` could be the *same* coordinate with two different `PC` subuniverses of `D_{x_i}^{(1)}`. That case is excluded only by `D_x^{(2)} ≠ ∅` (built into the definition of `<_{MT}`), which the paper never says.

**H15 — `LEMPreserveLinkdness` is invoked with `S' = R'∘R'^{-1}∘R'`, not the rectangular closure.** The lemma is about "a rectangular closure of `R`". `R'∘R'^{-1}∘R'` is one closure step and need not be rectangular. The usage is nevertheless *sound* (the conclusion used is the contrapositive `S ∩ (C_1×C_2) = ∅`, and `S' ⊆ rectangular closure`), but a literal formalization of the citation fails. Note also the indefinite article "**a** rectangular closure" in both `main.tex` L1879 and `StrongSubalgebras.tex` L2987 — the rectangular closure is unique, so this is sloppy but harmless.

**H16 — `CORSameTypeReductionAndConstraint` is a 6-line proof hiding 8 hypothesis checks.** "take `B = D_z^{(2)}` and apply Lemma X for the reduction `D^{(⊤)}`" requires verifying all eight hypotheses of #10, including hypothesis 7 (from minimality of `D^{(⊤)}`) and hypothesis 8 (from cruciality of `C` in `D^{(2)}` plus `D^{(2)} ≤ D^{(⊤)}`), plus the degenerate case `D^{(⊤)} = D^{(2)}` (then `I^{(2)}` has a solution and `C` is not crucial for the trivial reason). None of this is written.

**H17 — Expanded coverings: `S` is existentially quantified but used as data.** The definition says "there exists a mapping `S`", yet parent/child terminology, (p1), (p8), and every §3.3 argument that speaks of "children of `x`" require a *fixed* `S`. Bundle `S` into the structure. Also the definition text uses `Ω`/`Ω'` for `I`/`I'` (leftover naming) — L2171 and L2179.

**H18 — (p1)–(p8) are eight unproved lemmas advertised as "easy facts".** (p4) and (p7) are not easy. (p5) needs a compatibility condition on the two `S` maps that is not stated.

**H19 — Instances are lists, weakenings are sets.** "The weakening of a constraint `C` in an instance `I`" replaces **one** constraint by a family. If `I` contains two syntactically identical constraints, the definition of *crucial instance* ("all its constraints are crucial") and the weakening operation both need occurrence-level, not relation-level, semantics.

**H20 — Types `D`, `L`, `PC` and their `M`-versions interact non-uniformly.** `CORMainStableIntersection`'s hypothesis list allows `T_i ∈ {BA,C,S,L,PC}` — **not** `D`. Every place §3.2 says "type `T ∈ {L,PC,D}`" and then applies that corollary silently uses "a `D`-subuniverse is either an `L`- or a `PC`-subuniverse". True by definition, but the case split has to be made explicit at each use (it appears at least 3 times in #9 and #10).

**H21 — Nonemptiness conventions.** `⋘`, `<_T`, `≤_T` never hold for `∅`; the dotted variants do. `<_{MT}` builds in `C ≠ ∅`. The §3.2 proofs move between these constantly (e.g. "`E ≠ ∅` and by `CORPropagateToRelations`(r1) `E ⋘ D_{x_1}`" upgrades a dotted conclusion to an undotted one). A Lean development should probably carry `Option`/`Finset`-valued subuniverses with explicit nonemptiness side conditions rather than trying to mirror the dot notation.

---

# 6. Practical recommendations for the blueprint

1. **Split the CSP-instance layer from the algebra layer.** §3.1 is entirely combinatorial/syntactic (instances, paths, coverings, weakenings, cruciality) and is independent of `V_n`. It can be developed and even formalized ahead of, and independently from, §2/§5. Suggested modules: `CSP/Instance`, `CSP/Path`, `CSP/Consistency`, `CSP/Weakening`, `CSP/Crucial`, `CSP/Covering`, `CSP/Connected`.
2. **Fix `Con1` and irreducibility first.** H1–H3 are cheap to fix and unblock #3, #5, #9.
3. **Decide early on H4** (criticality). If you add "critical" back into the definition of *connected* (or of the ambient instances), you must also prove "crucial ⟹ critical" ([orig] Lemma 9.4-ish, ~10 lines) and re-prove [orig] Lemma 8.10. That is maybe 1 extra blueprint page and it removes a real gap.
4. **`CORMainStableIntersection` should be formalized in "indexed family" form** (a finite family of restrictions each attached to a coordinate, possibly several per coordinate) so that the "duplicate the coordinate" Remark never has to be invoked.
5. **Budget order-of-magnitude**: §3.1 ≈ 25 definitions + 8 covering facts + 1 remark-with-termination-proof. §3.2 ≈ 9 provable statements + 2 imported. `LEMGetABridgeFromSubdirectPCLinearInstance` and `LEMParalPropertyFromCrucialInMultiType` together are probably >50 % of §3.2's total Lean cost.
