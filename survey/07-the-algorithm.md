# 07 — Zhuk's algorithm: full pseudocode, correctness, termination, complexity, and what a Lean statement would have to say

Sources actually read (line numbers are into the files on disk):

* `papers/1704.01914.txt` — Zhuk, *A Proof of CSP Dichotomy Conjecture* (arXiv version of JACM 2020). **This is the only place the algorithm exists.**
  * §2 Outline of the algorithm, L132–339 (worked `Z_4` example).
  * §3 Definitions, L340–449 (instances, cycle-consistency, irreducible, weaker, crucial).
  * §4 Algorithm, L450–909 — **all pseudocode**: `Solve` L469–477, `AnswerOrReduce` L500–514, `SolveLinearCase` L554–579, `CheckAllTuples` L603–611, `FindOneEquationLinked` L661–682, `FindEquationsNonlinked` L709–720, `FindOneEquationNonlinked` L729–750, `CheckTuple` L763–773, `CheckCycleConsistency` L790–808, `CheckIrreducibility` L831–865, `CheckWeakerInstance` L878–889, `SolveNonlinked` L902–908.
  * §5 Correctness, L912–1121: Thm 5.1 (existence, L921), Lemma 5.2 + Cor 5.2.1 (complexity, L1003–1039), Lemma 5.3 (cycle-consistency, L1042), Lemma 5.4 (irreducibility, L1059), Thms 5.5/5.6/5.7 (L1091–1120).
  * §6 L1123–1330 (Lemma 6.1 expanded coverings, Lemma 6.2 `LinkedCon`, reductions), Lemma 7.20 / Cor 7.20.1 (L1884–1890), §9.3 (proofs of 5.5–5.7, incl. Thm 9.15).
  * §10.1–10.2 L4197–4227 (the algorithm is exponential in `|A|`; `WeakenEveryConstraint` conjecturally removable).
* `papers/src2404/main.tex` — Zhuk 2404.01080v2. Macro block L567–591; the **two `algorithm` environments**: `Solve` at L617–633 and `SolveLinear` at L684–716; surrounding narrative L593–755; informal claims L518–565; formal claims `THMCSPDReductionsAreSafe` L3985 and `THMCodimensionOneTheorem` L4004; definitions of strong subuniverses L1318–1640; `LEMUbiquity` L1653.
* `papers/2005.00593.txt` — Zhuk, *Strong subalgebras and the CSP*: the **decidable** redefinition of "center" as *central subuniverse* (L279–285), Thm 6.15 (L1670+), Cor 6.11.1 (L1591).
* `csp.tex` (Brady) L750 — the RAM/word-RAM caveat, relevant to any honest complexity statement.

Everything below marked **[FLAG]** is something that will break, or at least badly slow, a formalization.

---

## 0. Executive summary

1. The algorithm exists only in 1704.01914/JACM. The 2404 paper's two `algorithm` environments are a **sketch** ("for the precise algorithm see [zhuk2020proof, ZhukFVConjecture]", main.tex:593); one of its two loops is, read literally, **not justified by its own Theorem `THMCodimensionOneTheorem`** (see §3.3 and **[FLAG-2404-WEAKEN]**).
2. Correctness decomposes cleanly into: 4 "main" theorems (5.1, 5.5, 5.6, 5.7 — the only hard mathematics), 4 easy auxiliary lemmas (5.3, 5.4, 6.1, 6.2), and 1 linear-algebra lemma (7.20) that is used *pervasively and silently* to justify "the solution set is an affine subspace, so `k+1` queries suffice".
3. Termination and polynomiality are **not** the same argument. Termination follows from a well-founded measure. Polynomiality follows from a *constant* bound on **recursion depth** (`|A| + |Γ|`) plus a polynomial bound on the work per node — so total work is `poly(N)^{|A|+|Γ|}`. The depth bound rests on the claim "every recursive call strictly shrinks *every* domain of size > 1", which is **false as written** for the `CheckTuple → SolveNonlinked → Solve` path (**[FLAG-DEPTH]**). Fixable, but it must be fixed.
4. For Lean: "this algorithm is correct" is a *pure proposition about a recursive function* and is formalizable with today's Mathlib. "`CSP(Γ) ∈ P`" is not: Mathlib has Turing machines but no time-bounded complexity classes, no `P`, no cost semantics. The honest formulation I recommend is a **fuel-indexed interpreter** with two theorems (partial correctness; polynomial fuel suffices), plus an explicit, written-down statement of the cost model as a *definition*, not a claim.
5. Everything the algorithm quantifies over is decidable for a fixed finite domain — **except two things**: `∃ t ∈ Clo(A)` of unbounded arity (absorption) and `∃ B` an arbitrary finite algebra (the 1704 definition of *center*). Both are repaired by the 2005/2404 definitions (binary/ternary absorption; *central subuniverse* defined internally). This is a strong argument for basing the formalization on 2404 vocabulary. See §6.

---

## 1. Standing setup

**Input language.** `Γ0` is a finite constraint language on a finite set `A`, preserved by an idempotent WNU. Then (1704 L343–345) there is a *special* WNU `w ∈ Clo(Γ0-polymorphisms)`: idempotent, arity `m`, satisfying `x ∘ (x ∘ y) = x ∘ y` where `x ∘ y := w(x,…,x,y)`. Let `k0 = ` max arity in `Γ0` and

> **`Γ := { all relations of arity ≤ k0 on A preserved by w }`** (1704 L452–456).

This enlargement is **essential and load-bearing**, not cosmetic: the algorithm constantly forms (i) intersections `ρ ∩ (D1'×…×Ds')` with subuniverses, (ii) projections onto subsets of the scope, (iii) *all weaker constraints* of a constraint. `Γ` as defined is closed under all three, and `|Γ| ≤ 2^{|A|^{k0}}` is finite. Every complexity constant is measured against this `|Γ|`.

**Instance.** `Θ = ⟨X, D, C⟩`, `X = (x_1,…,x_n)`, `D = (D_1,…,D_n)` with `D_i ⊆ A`, `C = {C_1,…,C_q}`, each `C_j = ((x_{i_1},…,x_{i_s}); ρ)` with `ρ ⊆ D_{i_1}×…×D_{i_s}`.
*Invariant maintained everywhere*: each `D_i` is a **subuniverse** of `A` (closed under `w`) and each `ρ` is a subalgebra of `D_{i_1}×…×D_{i_s}`. Every reduction the algorithm performs produces a pp-definable set (a projection of a solution set), hence a subuniverse — this needs to be stated as an invariant in a formalization; Zhuk never states it.

**`Reduce`** (1704 L465–467): `Reduce(Θ, D') = (X, D', C')` with `C' = {((x_{i_1},…,x_{i_s}), ρ ∩ (D'_{i_1}×…×D'_{i_s}))}`.

**Consistency vocabulary** (1704 L400–416; 2404 main.tex L2085–2135, essentially identical):
* *1-consistent*: every constraint is subdirect (`pr_z C = D_z` for every `z ∈ Var(C)`).
* *path* `z_1 − C_1 − z_2 − … − C_{l−1} − z_l`; it *connects* `b,c` if there are `a_i ∈ D_{z_i}`, `a_1=b`, `a_l=c`, `(a_i,a_{i+1}) ∈ pr_{z_i,z_{i+1}} C_i`.
* *cycle-consistent*: 1-consistent, and for every `z` and `a ∈ D_z` every path from `z` to `z` connects `a` to `a`.
* *linked*: for every `z` and every `a,b ∈ D_z` some path from `z` to `z` connects `a,b`.
* *fragmented*: `X` splits into two nonempty parts with no constraint straddling them.
* *irreducible*: there is **no** instance `Θ'` with `Var(Θ') ⊆ Var(Θ)`, every constraint of `Θ'` a projection of a constraint of `Θ`, `Θ'` not fragmented, not linked, and with non-subdirect solution set.
  **[FLAG-IRRED-QUANT]** This is a `∀` over all sets of projections of constraints of `Θ` over all subsets of variables — i.e. over an exponentially large family. `CheckIrreducibility` decides it in polynomial time; the *equivalence* of the polynomial test with the definition is Lemma 5.4 and is the least routine of the "easy" lemmas (its proof, L1062–1085, is a gluing-of-paths argument that silently uses cycle-consistency twice).
* *weaker or equivalent*: `C1 = ρ1(y_1..y_t)` is weaker-or-equivalent to `C2 = ρ2(z_1..z_s)` if `{y} ⊆ {z}` and `C2 ⟹ C1`. *Weaker* = weaker-or-equivalent and not conversely. **Weakening a constraint `C` in `Θ`** := delete `C`, insert **all** constraints strictly weaker than `C` (finitely many, since scopes are subsets of `Var(C)` and relations are subalgebras).
* *dummy variable*, *crucial in `D'`* (1704 L429–444): `C` crucial in `D'` iff `C` has no dummy variables, `Θ` has no solution in `D'`, and weakening `C` yields an instance with a solution in `D'`. `Θ` crucial in `D'` iff nonempty and all its constraints are crucial.

**Two facts used constantly and worth naming now.**
* **Remark 1 / Lemma 6.1** (1704 L425–427, L1225): *if `Θ` is cycle-consistent and irreducible and `Θ' ∈ ExpCov(Θ)` (in particular, `Θ'` any weakening of `Θ`, or `Θ` with constraints deleted, or with dummy variables projected away) then `Θ'` is cycle-consistent and irreducible.* This is what lets `SolveLinearCase` weaken freely and still invoke Theorem 5.7.
* **Lemma 7.20 + Cor 7.20.1** (1704 L1884–1890): *if `ρ ≤ (Z_{p_1})^{n_1} × … × (Z_{p_k})^{n_k}` with `p_i` distinct primes dividing `m−1`, and each `Z_{p_i}` carries `x_1+…+x_m`, then `ρ = L_1 × … × L_k` with `L_i` an affine subspace of `(Z_{p_i})^{n_i}`.* Hence linear algebras are closed under `S`, `H`, `P`, hence a **minimal linear congruence** exists on every algebra (1704 L369–374). **Every "we only need `k+1` queries because the set is affine" step in the algorithm is this lemma.**

---

## 2. The algorithm, in full

I keep Zhuk's line numbers so the report can be diffed against the source. Comments in `⟨…⟩` are mine.

### 2.1 `Solve` — the driver (1704 L469–477)

```
 1: function Solve(Θ)                      -- Θ = (X,D,C), X=(x_1..x_n), D=(D_1..D_n)
 3:   repeat
 4:     Output := AnswerOrReduce(Θ)
 5:     if Output = "Solution"    then return "Solution"
 6:     if Output = "No solution" then return "No solution"
 7:     if Output = (x_i, U) then           -- ∅ ≠ U ⊊ D_i
 8:       Θ := Reduce(Θ, (D_1,…,D_{i−1}, U, D_{i+1},…,D_n))
 9:   until Done                            -- ⟨never reached; exit is by return⟩
```

Contract of `AnswerOrReduce`: returns `"Solution"`, `"No solution"`, or a pair `(x_i,U)` with `∅ ≠ U ⊊ D_i` such that **if `Θ` has a solution then `Θ` has a solution with `x_i ∈ U`** (1704 L462–465). Everything else in the paper exists to establish that contract.

### 2.2 `AnswerOrReduce` — the case analysis (1704 L500–514)

```
 1: function AnswerOrReduce(Θ)
 3:   Output := CheckCycleConsistency(Θ);  if Output ≠ "Ok" then return Output
 5:   if |D_i| = 1 for every i then return "Solution"
 6:   Output := CheckIrreducibility(Θ);    if Output ≠ "Ok" then return Output
 8:   Output := CheckWeakerInstance(Θ);    if Output ≠ "Ok" then return Output
10:   if B_i is a nontrivial binary absorbing subuniverse of D_i then return (x_i, B_i)
11:   if C_i is a nontrivial center of D_i                      then return (x_i, C_i)
12:   if σ is a proper congruence on D_i and (D_i;w)/σ is polynomially complete then
        choose an equivalence class E of σ;  return (x_i, E)
14:   return SolveLinearCase(Θ)
```

**The order of the tests is part of the proof, not a stylistic choice.**
* Line 5 is sound *only because* line 3 already returned "Ok": if every `|D_i| = 1` and the instance is 1-consistent, then each constraint `ρ` satisfies `pr_z ρ = D_z = {a_z}`, so `ρ = {(a_{z_1},…,a_{z_s})}` and the unique assignment is a solution.
* Line 12 may only fire when lines 10–11 did not, because **Theorem 5.6 hypothesises "no nontrivial BA subuniverse and no nontrivial center on `D_j` for every `j`"** (1704 L1095).
* Line 14 may only be reached when 10–12 did not fire, because `SolveLinearCase` needs the minimal linear congruence `σ_i` to be **proper** on every `D_i` with `|D_i| > 1`; that is exactly what **Theorem 5.1** yields once the other three alternatives are excluded.
* `CheckWeakerInstance` (line 8) is needed **only** to supply hypothesis (3) of Theorem 5.7. Zhuk conjectures it can be deleted (Problem 2, L4222).

### 2.3 `CheckCycleConsistency` (1704 L790–808)

```
 1: function CheckCycleConsistency(Θ)
 3:   for i,j ∈ {1..n}:  ρ_{i,j} := D_i × D_j
 5:     for C ∈ Θ:  ρ_{i,j} := ρ_{i,j} ∩ pr_{x_i,x_j} C
 7:   repeat
 8:     Changed := false
 9:     for i,j,k ∈ {1..n}:
10:       ρ'_{i,j}(x,y) := ∃z  ρ_{i,j}(x,y) ∧ ρ_{i,k}(x,z) ∧ ρ_{k,j}(z,y)
11:       if ρ_{i,j} ≠ ρ'_{i,j} then ρ_{i,j} := ρ'_{i,j}; Changed := true
14:   until ¬Changed
15:   for i,j ∈ {1..n}:
16:     if ρ_{i,j} = ∅         then return "No solution"
17:     if pr_1(ρ_{i,j}) ≠ D_i then return (x_i, pr_1(ρ_{i,j}))
18:     if pr_2(ρ_{i,j}) ≠ D_j then return (x_j, pr_2(ρ_{i,j}))
      return "Ok"
```

Notes. `i = j` is allowed and is what enforces 1-consistency (`ρ_{i,i} ⊆ diag(pr_{x_i} C)`, so `pr_1 ρ_{i,i} = D_i` forces `pr_{x_i} C = D_i`).
**[FLAG-PROJ]** line 6 is silent about constraints whose scope misses `x_i` or `x_j`; the intended reading is "skip" (equivalently `pr_{x_i,x_j} C := D_i × D_j`). Also silent: the "projection onto `(x_i,x_i)`" is the diagonal of `pr_{x_i} C`.

**Lemma 5.3** (1704 L1042): if it returns "Ok" the instance *is* cycle-consistent; if "No solution" there is none; if `(x_i,D)` every solution has `x_i ∈ D`. Proof (L1045–1058) reduces cycle-consistency to the fixpoint identity `ρ_{i,j}(x,y) = ∃z ρ_{i,j}(x,y) ∧ ρ_{i,k}(x,z) ∧ ρ_{k,j}(z,y)` and an induction on path length that is **written as one sentence** ("This follows from the fact that we terminated the function when …"). In Lean this is a genuine (easy) induction on the path, plus a lemma that pp-definable binary projections are preserved along paths. **[FLAG-53]**

### 2.4 `CheckIrreducibility` (1704 L831–865)

```
 1: function CheckIrreducibility(Θ)
 3:   for k = 1..n:
 4:     for σ_k = {E_k^1,…,E_k^t} a maximal congruence on D_k:
 5:       I := {k}
 6:       repeat
 7:         Changed := false
 8:         for C ∈ Θ, i ∈ I, j ∉ I with x_i,x_j ∈ Var(C):
 9:           δ := pr_{x_i,x_j} C
10:           for u = 1..t:  E_j^u := { b ∈ D_j | ∃a ∈ E_i^u : (a,b) ∈ δ }
12:           if E_j^1,…,E_j^t are pairwise disjoint then
13:             I := I ∪ {j}; Changed := true; break
16:       until ¬Changed
17:       for i ∈ I:
18:         D_i' := ∅
19:         for a ∈ D_i:
20:           choose u with a ∈ E_i^u
21:           for j = 1..n:
22:             E_j := {a}          if j = i
25:                 := E_j^u        if j ∈ I
27:                 := D_j          otherwise
28:           X0 := { x_i | i ∈ I }
29:           if Solve( pr_{X0}( Reduce(Θ,(E_1,…,E_n)) ) ) = "Solution" then D_i' := D_i' ∪ {a}
31:         if D_i' = ∅        then return "No solution"
32:         else if D_i' ≠ D_i then return (x_i, D_i')
      return "Ok"
```

Idea (L810–829): start from a maximal congruence on one domain and propagate the *partition* along constraints; since `σ_k` is maximal, along each binary projection either all classes are connected or none are, so the partition propagates with the same number of blocks; the resulting sub-instance on `X0`, restricted to matching blocks, splits into `t` independent instances on strictly smaller domains, each solvable by recursion. Well-definedness of the propagated partition (path-independence) is where cycle-consistency is used (L1074–1078).

**[FLAG-IRRED-WD]** The pseudocode *chooses* constraints and an order of adding to `I`; the proof of Lemma 5.4 asserts the result is independent of those choices ("the order … is not important"), justified by gluing two paths and invoking cycle-consistency. This is a real lemma (partition propagation is a well-defined function of `σ_k` alone) and must be proved, not assumed, in Lean.

**Lemma 5.4** (1704 L1059): same contract as 5.3.

### 2.5 `CheckWeakerInstance` (1704 L878–889)

```
 1: function CheckWeakerInstance(Θ)
 3:   Θ' := WeakenEveryConstraint(Θ)      -- replace *every* constraint by all weaker
 4:   for i = 1..n:                       --   constraints without dummy variables
 5:     D_i' := ∅
 6:     for a ∈ D_i:
 7:       Output := Solve( Reduce(Θ',(D_1,…,D_{i−1},{a},D_{i+1},…,D_n)) )
 8:       if Output = "Solution" then D_i' := D_i' ∪ {a}
10:     if D_i' = ∅        then return "No solution"
11:     else if D_i' ≠ D_i then return (x_i, D_i')
      return "Ok"
```

Contract: on "Ok", **the solution set of `WeakenEveryConstraint(Θ)` is subdirect** — i.e. hypothesis (3) of Theorem 5.7. Safety of the reduction is trivial: `Sol(Θ) ⊆ Sol(Θ')`, so `pr_{x_i} Sol(Θ) ⊆ D_i'`.

### 2.6 `SolveLinearCase` (1704 L554–579)

Preamble (L532–552). For each `i`, `σ_i` := the **minimal linear congruence** on `D_i` (least `σ` with `D_i/σ` linear); `L_i := D_i/σ_i ≅ Z_{p_1}×…×Z_{p_l}`. `FactorizeInstance(Θ) = Θ_L`: same variables, domains `L_i`, and each `((x_{i_1}..x_{i_s}); ρ)` becomes `((x'_{i_1}..x'_{i_s}); ρ')` with

  `(E_1,…,E_s) ∈ ρ'  ⟺  (E_1×…×E_s) ∩ ρ ≠ ∅`.

`ρ'` is the image of `ρ` under the surjective homomorphism `∏D → ∏L`, hence a subalgebra of the *linear* algebra `∏L`; by Lemma 7.20 it is a conjunction of linear equations. Fix once and for all a natural bijection `ψ : Z_{p_1}×…×Z_{p_r} → L_1×…×L_n` (grouping the prime factors of each `L_i`) and identify `Θ_L` with a system of linear equations in `z_1,…,z_r` (each equation lives over a single prime; only variables over the same `Z_p` may co-occur).

```
 1: function SolveLinearCase(Θ)
 3:   Θ_L := FactorizeInstance(Θ)
 4:   Eq  := ∅                                        -- equations added to Θ_L
 5:   repeat
 6:     φ := SolveLinearSystem(Θ_L ∪ Eq)              -- φ : Z_{q_1}×…×Z_{q_k} → L_1×…×L_n
                                                     -- affine, image = solution set (Gauss)
 7:     if φ = ∅ then return "No solution"
 8:     if Solve(Reduce(Θ, φ(0,…,0))) = "Solution" then return "Solution"
 9:     else if k = 0 then return "No solution"       -- Θ_L ∪ Eq had a unique solution
10:     Θ' := RemoveTrivialities(Θ)
11:     repeat                                        -- try to weaken Θ'
12:       Changed := false
13:       for C ∈ Θ':
14:         Ω := RemoveTrivialities(WeakenConstraint(Θ', C))
15:         if ¬CheckAllTuples(Ω, φ) then
16:           Θ' := Ω; Changed := true; break
19:     until ¬Changed                                -- Θ' cannot be weakened anymore
20:     if Θ' is not linked then
21:       Eq := Eq ∪ FindEquationsNonlinked(Θ')
22:     else
23:       Eq := Eq ∪ { FindOneEquationLinked(Θ', φ) }
24:   until Done
```

```
 1: function CheckAllTuples(Θ, φ)
 3:   if Solve(Reduce(Θ, φ(0,…,0))) = "No solution" then return false
 4:   for i = 1..k:
 5:     t := (0,…,0,1,0,…,0)          -- 1 in position i
 6:     if Solve(Reduce(Θ, φ(t))) = "No solution" then return false
      return true
```

`RemoveTrivialities(Θ)` (L621–624): iteratively (a) drop constraints that are weaker than some other constraint of `Θ`, (b) drop constraints with no non-dummy variables, (c) replace each constraint by its projection onto its non-dummy variables. It preserves the solution set.
**[FLAG-RT]** "constraints without non-dummy variables" is ambiguous: a constraint all of whose variables are dummy is either full (drop it) or empty (the instance is unsatisfiable). The pseudocode never distinguishes. Also, is `RemoveTrivialities` a *function* (confluent)? Step (a) can remove different constraints depending on order when two constraints are equivalent. The rest of the proof only uses "the result is a weakening of `Θ` with the same solution set and no dummy variables", so confluence is not needed — but a Lean definition must make a deterministic choice and prove exactly that contract.

**Meaning.** With `A := image of Sol(Θ) in L_1×…×L_n` and `B := Sol(Θ_L ∪ Eq) = φ(Z)`, the invariant is `A ⊆ B`; each pass through the outer loop strictly lowers `dim B` while keeping `A ⊆ B`; the loop stops when `φ(0) ∈ A` ("Solution") or `B = ∅` / `k=0` with `φ(0) ∉ A` ("No solution").

**Why `CheckAllTuples` is sound with only `k+1` queries.** For an instance `Ω`, `{ t | Ω has a solution in φ(t) } = φ^{-1}(A_Ω)`, where `A_Ω ≤ L_1×…×L_n` is the image of `Sol(Ω)` — a subalgebra of a linear algebra, hence (Lemma 7.20) a product of affine subspaces; `φ` is affine; so `φ^{-1}(A_Ω)` is a subalgebra of `Z_{q_1}×…×Z_{q_k}`, i.e. an affine subspace. If it contains `0` and every `e_i` then it contains the subgroup they generate, i.e. everything. **[FLAG-AFF]** Zhuk states this as "Since `A` and `B` are subuniverses of `L_1×…×L_n` (almost subspaces), we just need to check …" (L596–598). The parenthesis "(almost subspaces)" is doing real work and must be replaced by Lemma 7.20 in a formalization.

### 2.7 Learning the equation (1704 L661–773)

```
 1: function FindOneEquationLinked(Θ, φ)
 3:   t := ∅
 4:   if Solve(Reduce(Θ, φ(0,…,0))) = "No solution" then t := (0,…,0)
 6:   else for i = 1..k:
 8:     t' := (0,…,0,1,0,…,0)         -- 1 in position i
 9:     if Solve(Reduce(Θ, φ(t'))) = "No solution" then t := t'; break
12:   if t = ∅ then return "0 = 0"
13:   for i = 1..k:
14:     b_i := 0
15:     for a ∈ Z_{q_i} \ {t(i)}:
16:       t' := t;  t'(i) := a
18:       if Solve(Reduce(Θ, φ(t'))) = "Solution" then b_i := 1/(a − t(i))
      return "b_1(y_1 − t(1)) + … + b_k(y_k − t(k)) = 1"
```

Correctness: given (Theorem 5.7) that `V := φ^{-1}(A_Θ)` is empty or an affine hyperplane, and given `t ∉ V`, write `V = { y | Σ c_i (y_i − t_i) = 1 }`; then the point `t` with coordinate `i` changed to `a` lies in `V` iff `c_i (a − t_i) = 1`, i.e. `c_i = 1/(a − t_i)`, and `c_i = 0` iff no such `a`. `V = ∅` yields all `b_i = 0`, i.e. the equation "`0 = 1`".
**[FLAG-TYPES]** The returned equation formally mixes variables over *different* prime fields. This is only meaningful because, by Lemma 7.20, a subalgebra of `Z_{q_1}×…×Z_{q_k}` is a product over the primes, so the coefficients `b_i` for all but one prime are automatically `0`. 2404 makes this explicit in a footnote (main.tex L676–678); 1704 does not. A Lean definition has to be typed correctly from the start (e.g. return an equation *per prime class*, or return the affine subspace itself).
**[FLAG-COORD]** The returned equation is in the `y`-coordinates (the parameters of the *current* `φ`), but `Eq` is a system in the `z`-coordinates of `ψ`. The pullback along the affine map `y ↦ z` implicit in `φ = ψ ∘ (affine)` is never mentioned. (2404's `SolveLinear` handles this cleanly by `φ := φ ∘ ψ`.)

```
 1: function FindEquationsNonlinked(Θ)
 3:   I := {1}                                  -- set of "independent" variables
 4:   E := ∅
 5:   for j = 1..r:
 6:     e := FindOneEquationNonlinked(Θ, I ∪ {j})
 7:     if e = "0 = 0"      then I := I ∪ {j}
 9:     else if e = "0 = 1" then return "No solution"
10:     else E := E ∪ e
      return E
```

```
 1: function FindOneEquationNonlinked(Θ, I = {i_1,…,i_h})
 3:   t := ∅
 4:   if ¬CheckTuple(Θ, I, (0,…,0)) then t := (0,…,0)
 6:   else for j = 1..h:
 8:     t' := (0,…,0,1,0,…,0)          -- 1 in position j
 9:     if ¬CheckTuple(Θ, I, t') then t := t'; break
12:   if t = ∅ then return "0 = 0"
13:   for j = 1..h:
14:     b_j := 0
15:     for a ∈ Z_{p_{i_j}} \ {t(j)}:
16:       t' := t;  t'(j) := a
18:       if CheckTuple(Θ, I, t') then b_j := 1/(a − t(j))
      return "b_1(z_{i_1} − t(1)) + … + b_h(z_{i_h} − t(h)) = 1"
```

```
 1: function CheckTuple(Θ, I, t)
 3:   R := { α ∈ Z_{p_1}×…×Z_{p_r} | pr_I(α) = t }        -- not materialised
 5:   for i = 1..n:  D_i' := ⋃_{E ∈ pr_i(ψ(R))} E
 6:   if SolveNonlinked( Θ ∧ (x_1∈D_1') ∧ … ∧ (x_n∈D_n') ) = "Solution" then return true
 7:   else return false
```

```
 1: function SolveNonlinked(Θ)
 3:   X0 := Var(Θ)
 4:   Θ' := pr_{X0}(Θ)
 5:   for a linked component (D_1',…,D_{n'}') of Θ':
 6:     if Solve(Reduce(Θ',(D_1',…,D_{n'}'))) = "Solution" then return "Solution"
      return "No solution"
```

`CheckTuple` is correct because `R` is a *cylinder* (a product set in `z`-coordinates) and `ψ` is coordinatewise, so `ψ(R) = S_1×…×S_n` is a product set of blocks and "`Θ` has a solution inside the union `⋃S_i`" is equivalent to "`Θ` has a solution whose factorisation lies in `ψ(R)`". If `ψ(R)` were not a product set this step would be **wrong**; nothing in the text says why it is one. **[FLAG-CYL]**

`SolveNonlinked` is correct because for a cycle-consistent instance `LinkedCon(Θ,x)` is a congruence on `D_x` (Lemma 6.2, L1261) and the linked components therefore restrict to subuniverses; a solution lies entirely inside one component.

**[FLAG-FEN-BUG]** `FindEquationsNonlinked` line 3 initialises `I := {1}` — asserting that `z_1` is independent — while the loop runs `j = 1..r` and only adds `j` to `I` when the answer is "`0=0`". The invariant the method needs is "`pr_I(A_Θ)` is full", so that `pr_{I∪{j}}(A_Θ)` is full or of codimension 1 and hence learnable by one equation. With `I := {1}` that invariant fails whenever `z_1` is constrained. Concrete failure: `r = 2`, `p_1 = p_2 = 2`, `A_Θ = {(0,0)}`. Step `j=1` correctly returns `z_1 = 0` and adds it to `E`, but `1` stays in `I`; step `j=2` queries `pr_{\{1,2\}}`, finds `t=(1,0) ∉ A_Θ`, computes `b_1 = 1, b_2 = 0` and returns `z_1 = 0` **again**, losing `z_2 = 0`. The final `E` describes `{(0,0),(0,1)} ⊋ A_Θ`, so `B` is not shrunk to `A'` and the outer loop's dimension-decrease invariant breaks. Initialising `I := ∅` fixes it. I am confident this is a typo, but it is exactly the sort of typo a formalization must find and repair, and it should be repaired explicitly in the blueprint.

### 2.8 The 2404 sketch (main.tex L617–633, L684–716)

```
Solve(I):
  repeat
    I := ForceConsistency(I)                       -- cycle-consistency + irreducibility
    if I = false then return "No"                  --   + the CheckWeakerInstance condition
    if D_{x_i} has a strong subset B then I := ReduceDomain(I, x_i, B)
  until nothing changed
  return SolveLinear(I)

SolveLinear(I):
  m := dim(D_{x_1}/σ_{x_1} × … × D_{x_n}/σ_{x_n})
  φ := a bijective linear map Z_{p_1}×…×Z_{p_m} → D_{x_1}/σ_{x_1} × … × D_{x_n}/σ_{x_n}
  while φ^{-1}(I) ≠ Z_{p_1}×…×Z_{p_m}:             -- test by (p1)
    I' := I
    for C ∈ I':
      if φ^{-1}(I' \ {C}) ≠ Z_{p_1}×…×Z_{p_m} then I' := I' \ {C}
    F := φ^{-1}(I')                                -- by (p2) if I' not linked, else (p3)
    if F = ∅ then return "No"
    m := dim F;  ψ := bijective linear Z_{p_1}×…×Z_{p_m} → F;  φ := φ ∘ ψ
  return "Yes"
```
with the four primitives (main.tex L647–680):
`(p0)` membership `α ∈ φ^{-1}(I)` by reducing every domain to the block `φ(α)_i` and recursing;
`(p1)` `φ^{-1}(I) = Z` by `(p0)` on `0` and each `e_i`;
`(p2)` if `I` is not linked, split into linked instances on smaller domains, recurse, and take the **union** of the `φ^{-1}(I_j)`;
`(p3)` if `dim φ^{-1}(I) = m−1` or it is empty, find `a ∉ φ^{-1}(I)` by `(p1)`, then for each `i` find `b_i` with `(a_1..b_i..a_m) ∈ φ^{-1}(I)`, and output `Σ_{i∈J}(y_i − a_i)/(b_i − a_i) = 1`.

This is much cleaner than 1704 and is the right *shape* to formalize. But:

**[FLAG-2404-WEAKEN]** The inner loop **removes** constraints (`I' := I' \ {C}`) whereas `THMCodimensionOneTheorem` hypothesis (7) is about **weakening** a constraint. From "removing `C` makes `φ^{-1}` full" one cannot conclude "weakening `C` makes `φ^{-1}` full": `Sol(I') ⊆ Sol(weaken C) ⊆ Sol(I'\{C})`, and fullness of the largest tells us nothing about the middle. The sketch is therefore *not* justified by its own theorem — **unless** one first saturates `I` with all weaker constraints of each constraint (which does not change the solution set), after which "delete `C`" and "weaken `C`" coincide. That saturation is nowhere stated. A blueprint must state it.

**[FLAG-2404-P2]** `(p2)` returns a *union* of affine subspaces, but `SolveLinear` immediately treats `F` as an affine subspace (`dim F`, `ψ` bijective linear onto `F`). The union *is* affine, because `φ^{-1}(I')` is the preimage under an affine map of the image of a solution set — a subalgebra of a linear algebra (Lemma 7.20). But as written the pseudocode asserts a fact it does not prove.

**[FLAG-2404-STRONG]** "if `D_{x_i}` has a strong subset `B`" glosses over the fact that `THMCSPDReductionsAreSafe` covers `T ∈ {BA, C, PC}` **only**; a strong subuniverse of type `L` (linear) may **not** be reduced to — that is precisely the case `SolveLinear` handles. `LEMUbiquity` (main.tex L1653) produces `T ∈ {BA, C, L, PC}`, so the algorithm's dichotomy is "some `BA/C/PC` subuniverse exists, or every domain has a proper linear congruence".

---

## 3. Correctness: exactly which theorem is used where

### 3.1 The four theorems

**Theorem 5.1** (existence; 1704 L921; 2404 = `LEMUbiquity` + `LEMLInearOnTheTopIsEasy` + `LEMPCOnTheTopIsEasy`).
*Let `A = (A;w)` be finite with `w` a special WNU of arity `m`. Then one of: (1) a nontrivial binary absorbing `B ⊊ A`; (2) a nontrivial center `C ⊊ A`; (3) a proper congruence `σ` with `A/σ` polynomially complete; (4) a proper congruence `σ` with `A/σ ≅ (Z_p; x_1+…+x_m)`.*
Proof by induction on `|A|` using **Rosenberg's classification of maximal clones** (L937–998) — an outside import of substantial size (see §7). 2404 replaces this by `LEMUbiquity`: *if `B ⋘ A` and `|B| > 1` then there is `C <_T^A B` with `T ∈ {BA, C, L, PC}`*, proved inside the paper's own theory. **For a formalization the 2404 route avoids Rosenberg entirely — a large win.**
*Used at*: `AnswerOrReduce` fall-through to line 14. Its role is purely: "in the remaining case every `D_i` with `|D_i|>1` has a **proper** minimal linear congruence `σ_i`", which is what makes the recursion in `SolveLinearCase` shrink domains.

**Theorem 5.5** (safety of BA/center; 1704 L1091).
*If `Θ` is cycle-consistent and irreducible and `B` is a nontrivial binary absorbing subuniverse or a nontrivial center of `D_i`, then `Θ` has a solution iff `Θ` has a solution with `x_i ∈ B`.*
*Used at*: `AnswerOrReduce` lines 10, 11.

**Theorem 5.6** (safety of PC blocks; 1704 L1095).
*If `Θ` is cycle-consistent and irreducible, **no `D_j` has a nontrivial BA subuniverse or center**, `(D_i;w)/σ` is polynomially complete and `E` is **any** equivalence class of `σ`, then `Θ` has a solution iff it has one with `x_i ∈ E`.*
*Used at*: line 12. Note the `∀E` — this is what licenses the algorithm's arbitrary `choose`.
2404 strengthens this: `THMPCDoesnotKillAllSolutions` (main.tex L3860) **drops the "no BA/center anywhere" hypothesis**, and `THMCSPDReductionsAreSafe` (L3985) merges 5.5 and 5.6 into one statement for `T ∈ {BA, C, PC}` with no side conditions. That is a real simplification of the *algorithm's* proof obligations (though the algorithm still tests BA/center first, so the extra hypothesis is free).

**Theorem 5.7** (codimension one; 1704 L1100; 2404 `THMCodimensionOneTheorem` L4004).
*Suppose (1) `Θ` is a linked, cycle-consistent, irreducible instance with domains `(D_1..D_n)`; (2) no `D_j` has a nontrivial BA subuniverse or center (2404: each `D_{x_i}` is `S`-free); (3) weakening **all** constraints of `Θ` gives an instance with subdirect solution set; (4) `L_i = D_i/σ_i` with `σ_i` the minimal linear congruence (2404: `σ_{x_i}` = intersection of all linear congruences `σ` with `σ* = D_{x_i}^2`); (5) `φ : Z_{q_1}×…×Z_{q_k} → L_1×…×L_n` a homomorphism, `q_i` prime; (6) weakening **any one** constraint of `Θ` gives, for every `(a_1..a_k)`, an instance with a solution in `φ(a_1..a_k)`. Then `{(a_1..a_k) | Θ has a solution in φ(a_1..a_k)}` is empty, or full, or an affine subspace of codimension 1.*
*Used at*: `SolveLinearCase` line 23 (`FindOneEquationLinked`). This is the deepest theorem; its proof goes through **Theorem 9.15** (existence of a constraint `ρ(x_{i_1}..x_{i_s})` and `ζ ≤ D_{i_1}×…×D_{i_s}×Z_p` such that `pr_{1..s} ζ ⊋ ρ` but `pr_{1..s}(ζ ∩ (…×{0})) = ρ`), i.e. the whole bridge/connectedness machinery. In 2404 the same step is "`Con(C,x)` is a **perfect linear congruence**" (main.tex L4038–4098).

### 3.2 The invariant chain in `Solve`/`AnswerOrReduce`

At the moment `AnswerOrReduce` reaches line `k`:
* after line 3 "Ok": `Θ` is **cycle-consistent** (Lemma 5.3);
* after line 6 "Ok": `Θ` is **irreducible** (Lemma 5.4);
* after line 8 "Ok": **`WeakenEveryConstraint(Θ)` has subdirect solution set**;
* after lines 10–11: **no `D_i` has a nontrivial BA subuniverse or center**;
* after line 12: **no `D_i` has a proper congruence with PC quotient**; hence by Theorem 5.1 every `D_i` with `|D_i|>1` has a proper congruence with quotient `Z_p`, hence its minimal linear congruence `σ_i` is proper.

Each *reduction* returned is safe: lines 3/6/8 by Lemmas 5.3/5.4 and by `Sol(Θ) ⊆ Sol(WeakenEveryConstraint(Θ))`; lines 10/11 by Theorem 5.5; line 12 by Theorem 5.6.

### 3.3 The invariant chain in `SolveLinearCase`

Write `π : ∏D_i → ∏L_i`, `A := π(Sol Θ)`, `B := Sol(Θ_L ∪ Eq) = φ(Z)` with `Z = Z_{q_1}×…×Z_{q_k}`.

* **(I0)** `Θ` is never modified. `Θ'` is always a *weakening* of `Θ` (constraints replaced by weaker ones, deleted, or projected onto non-dummy variables), so by **Lemma 6.1** `Θ'` is still cycle-consistent and irreducible, with the same domains — hence hypotheses (1)(2) of Theorem 5.7 persist, as does (3) (weakening `Θ'` further stays below `WeakenEveryConstraint(Θ)`, whose solution set is subdirect). **[FLAG-53b]** The step "(3) for `Θ` ⟹ (3) for `Θ'`" is used but never stated; it needs transitivity of "weaker or equivalent" plus monotonicity of solution sets.
* **(I1)** `A ⊆ B`. Initially `Eq = ∅` and any solution of `Θ` factors to a solution of `Θ_L`. Preserved because every added equation is valid on `A_{Θ'} ⊇ A`.
* **(I2)** At line 10: `k ≥ 1` and `φ(0,…,0) ∉ A`, so `A ⊊ B`.
* **(I3)** Inner-loop invariant: `¬CheckAllTuples(Θ',φ)`, i.e. there is `b ∈ {0,e_1,…,e_k}` with no solution of `Θ'` in `φ(b)`.
* **(I4)** At inner-loop exit: for **every** `C ∈ Θ'`, weakening `C` gives an instance with a solution in `φ(a)` for **every** `a ∈ Z` — i.e. hypothesis (6) of Theorem 5.7. Only `k+1` tuples were tested; the upgrade to `∀a` is Lemma 7.20 (**[FLAG-AFF]**).
* Consequently `Θ'` is **crucial** in the reduction `D^{(1)} := φ(b)` (no solution there, but weakening any constraint yields one), which is what Theorem 5.7's proof actually consumes.
* **Exit**: if `Θ'` is linked, Theorem 5.7 says `φ^{-1}(A_{Θ'})` is empty, full, or codim 1; it is not full by (I3); `FindOneEquationLinked` learns the defining equation with `≤ 1 + k + k·max q_i` recursive queries. If `Θ'` is not linked, `FindEquationsNonlinked` computes `A_{Θ'}` outright by `O(r · max p_i)` `CheckTuple` queries. Either way `B := B ∩ A_{Θ'} ⊊ B` and `A ⊆ B` persists.

### 3.4 Soundness of every terminal answer

"Solution" is returned only from (a) `AnswerOrReduce` line 5, where the singleton assignment is a genuine solution *because the instance is 1-consistent*; and (b) `SolveLinearCase` line 8, forwarding a recursive "Solution". So a solution is genuinely exhibited (by induction), and in fact the algorithm can be turned into a search algorithm at no cost, since `w` idempotent ⟹ `{a}` is a subuniverse ⟹ the unary singleton relations lie in `Γ` (for `k0 ≥ 1`), so "fix `x_i := a` and re-run" is an instance of the same problem.

"No solution" is returned from: `CheckCycleConsistency` L16 (`ρ_{i,j} = ∅`, and `ρ_{i,j}` is pp-derived from `Θ`); `CheckIrreducibility` L31 and `CheckWeakerInstance` L10 (`D_i' = ∅`, and `D_i' ⊇ pr_{x_i} Sol(Θ)`); `SolveLinearCase` L7 (`Θ_L ∪ Eq` unsatisfiable and `A ⊆ B = ∅`), L9 (`k = 0`: `B` is a single point not in `A`); `FindEquationsNonlinked` L9 (`A_{Θ'} = ∅ ⊇ A`); `SolveNonlinked` (all components fail, and every solution lies in one component — Lemma 6.2).

---

## 4. Termination

Zhuk never gives a termination *measure*; he gives a **recursion-depth bound** (Lemma 5.2), which is a stronger statement and implies termination once one also bounds each loop. For a Lean definition by well-founded recursion the measure must be produced explicitly. Here is what the recursion sites actually do.

Recursion sites (calls to `Solve` from inside a `Solve`):

| site | reduction applied before recursing | every domain of size >1 shrinks? |
|---|---|---|
| `CheckIrreducibility` L29 | project onto `X0 = {x_i : i ∈ I}`, domains become blocks `E_j^u` of a **maximal** (hence proper) congruence, and `{a}` at the pivot | **yes** (all surviving variables) |
| `CheckWeakerInstance` L7 | `D_i := {a}`; all other domains unchanged; **all constraints simultaneously weakened** | **no** — handled by the `Γ`-measure |
| `SolveLinearCase` L8 | domains → `σ_i`-blocks `φ(0)_i`, `σ_i` proper | **yes** |
| `CheckAllTuples` L3,L6 | idem | **yes** |
| `FindOneEquationLinked` L4,L9,L18 | idem | **yes** |
| `CheckTuple` → `SolveNonlinked` L6 | domains → *unions* of `σ_i`-blocks, then → a linked component | **not guaranteed** — see [FLAG-DEPTH] |

**The `Γ`-measure** (1704 L1009–1020). Order the relations of `Γ`: `ρ1 ≤ ρ2` iff (1) `ar(ρ1) < ar(ρ2)`; or (2) equal arity, `pr_i(ρ1) ⊆ pr_i(ρ2)` for all `i` with strict inclusion for some `j`; or (3) equal arity, all projections equal, and `ρ1 ⊇ ρ2`. This is a strict partial order of height `≤ |Γ|`. Claim: the algorithm never moves a constraint relation *up*; and the `CheckWeakerInstance` recursion moves *every* constraint relation strictly down. Checking the claim:
* `Reduce` shrinks relations and their projections → down by (2) (or stays).
* projecting onto non-dummy variables → down by (1).
* *weakening* enlarges the relation. It moves **down** by (3) only if the projections are unchanged. They are, **because the instance is 1-consistent at that point** (`pr_i ρ = D_i` already, and weaker relations still live in `D_{i_1}×…×D_{i_s}`). So the argument silently depends on `CheckCycleConsistency` having run first. **[FLAG-GAMMA-ORDER]** Zhuk does not say this.
* The correspondence "every constraint relation" is loose, since weakening `C` replaces it by *several* constraints. The correct statement is about the **multiset** of constraint relations under the multiset extension of `≤`.

**A measure that actually works** (proposal for the blueprint):
```
μ(Θ) := ( Σ_{x ∈ Var(Θ)} (|D_x| − 1) ,  Φ(Θ) )   ordered lexicographically,
Φ(Θ) := Σ_{C ∈ Θ} (K+1)^{rank(ρ_C)},   K := max #{weaker constraints of a relation} ≤ |Γ|,
rank(ρ) := height of ρ in the order ≤ above (≤ |Γ|).
```
* `CheckIrreducibility`, `SolveLinearCase`, `CheckAllTuples`, `FindOneEquationLinked`: first component drops.
* `CheckWeakerInstance`: `D_i → {a}` drops the first component when `|D_i|>1`; when all `|D_i| = 1` the instance is already answered at `AnswerOrReduce` L5, so this case does not arise. (Alternatively: `Φ` drops, since weakening replaces one constraint of rank `h` by `≤ K` constraints of rank `< h`, and `(K+1)^h > K(K+1)^{h−1}`.)
* `CheckTuple → SolveNonlinked`: the first component drops **provided** at least one domain of size `>1` shrinks. It does: `I ∪ {j}` fixes at least the `z_j` coordinate, so the `L_i` containing `z_j` is cut down to a proper subset of blocks, so `D_i' ⊊ D_i`. (This is enough for **termination** but not for the depth bound.)
* The inner `repeat` of `SolveLinearCase` decreases `Φ`; the outer `repeat` decreases `dim B`; the `repeat` of `Solve` decreases `Σ(|D_x|−1)`; `CheckCycleConsistency`'s `repeat` decreases `Σ_{i,j}|ρ_{i,j}|`; `CheckIrreducibility`'s `repeat` increases `|I|`.

---

## 5. Complexity

**Lemma 5.2** (1704 L1003): *the depth of the recursion is `< |A| + |Γ|`.* Argument: along any root-to-leaf path, each `Solve`-call other than those from `CheckWeakerInstance` strictly reduces **all** domains of size `>1` (so at most `|A|` of them), and each `Solve`-call from `CheckWeakerInstance` strictly lowers **every** constraint relation in the `≤`-order (so at most `|Γ|` of them).

**Corollary 5.2.1** (L1022): *the algorithm is polynomial*, because each loop is polynomial:
`Solve`'s loop ≤ `n·|A|`; `SolveLinearCase`'s outer loop ≤ `r ≤ |A|·n`; its inner loop "≤ `|Γ|·N`"; `CheckCycleConsistency`'s loop ≤ `|Γ|·n²`; `CheckIrreducibility`'s loop ≤ `n`.

**How "polynomial" actually follows.** Let `W(N)` bound the non-recursive work of one `Solve`-node on an instance of size `N`, and `R(N)` the number of recursive calls it makes, both polynomial. Since the depth `d ≤ |A| + |Γ|` is a **constant** (depending only on `Γ`, not on the instance), the total work is `≤ (R(N)·W(N'))^{d}` where `N'` bounds the instance size at any node. Hence `T(N) = N^{O(|A|+|Γ|)}`. **This is the entire complexity argument.** Two consequences that must be stated honestly:
* the *degree* of the polynomial is `O(|A| + |Γ|)` with `|Γ| ≤ 2^{|A|^{k0}}` — doubly exponential in the domain size. Zhuk acknowledges this (§10.1, L4198–4199: "depends exponentially on the size of the domain"; and §10.2: removing `WeakenEveryConstraint` would drop the depth from `|A|+|Γ|` to `|A|`);
* the instance *size* grows along the recursion (weakening multiplies constraints by up to `K ≤ |Γ|` each time), so `N' ≤ N·K^{|Γ|}` — again a constant factor for fixed `Γ`.

**[FLAG-DEPTH] The depth bound is not established for the `CheckTuple → SolveNonlinked → Solve` path.** `CheckTuple` reduces `D_i` to a *union* of `σ_i`-blocks; only the coordinates touched by `I ∪ {j}` are constrained, so domains at untouched variables are unchanged. `SolveNonlinked` then splits into linked components, and the claim "all domains shrink" needs: *in a 1-consistent, non-fragmented, non-linked instance every linked component meets every domain in a proper subset*. That statement is **true** — if some `D_x` lies entirely in one component then, by 1-consistency, every neighbouring domain does too, and by non-fragmentedness the whole instance is one component, i.e. linked — but its hypothesis **1-consistency fails** for the instance `CheckTuple` builds, because it bolts unary constraints `x_i ∈ D_i'` onto `Θ` without re-propagating. Counterexample to the general claim without 1-consistency: `D_x = D_y = {0,1}`, single constraint `ρ(x,y) = {(0,0),(1,0)}`; the components are `{(x,0),(x,1),(y,0)}` and `{(y,1)}`, and `D_x` is not reduced. If a domain fails to shrink, the depth becomes `O(n·|A|)` rather than `O(|A|)`, and the running time `N^{O(n)}` — **not polynomial**. *Repair*: run 1-consistency propagation (arc consistency) inside `SolveNonlinked` before computing components (and return "No solution" if a domain empties). This is cheap and restores the invariant. A blueprint must include this fix and the lemma above.

**[FLAG-INNER-LOOP]** "the inner repeat loop runs at most `|Γ|·N` times" is not right as stated: weakening one constraint replaces it by up to `K` constraints, so `N` grows. The corrected bound is `Φ(Θ) ≤ N·(K+1)^{|Γ|}` passes (see §4) — still `O(N)` for fixed `Γ`, but with an astronomically larger constant. This does not affect the truth of Corollary 5.2.1.

**[FLAG-COST-MODEL]** Every "polynomial" here is in a RAM-style model where a relation `ρ ⊆ A^k` (`k ≤ k0`) is a unit-cost object and set operations on it are unit cost. Compare Brady's explicit caveat, `csp.tex` L750, that running-time claims in this subject implicitly use a word-RAM model. There is no bit-level analysis anywhere in Zhuk's paper.

---

## 6. Decidability / computability audit (fixed finite domain)

For each "existential over an infinite or unstructured domain" in the algorithm:

| construct | as written | decidable? | how |
|---|---|---|---|
| `B` is a **binary absorbing** subuniverse of `D` | `∃ t ∈ Clo(D)` binary with `t(B,D)∪t(D,B) ⊆ B` | **yes** | the binary part of `Clo(D)` is the least subset of `D^{D²}` containing the projections and closed under `f ↦ w(f_1,…,f_m)`; a finite least fixpoint (`≤ |D|^{|D|²}` elements) |
| `C` is a **center** of `D` (1704 §3.5) | `∃` a *finite algebra* `B=(B;w_B)` with a special WNU of arity `m`, `B` without nontrivial BA subuniverse, and `R ≤_{sd} D×B` with `C = {a : ∀b∈B, (a,b)∈R}` | **not obviously** — unbounded quantification over all finite algebras | **repaired in 2005.00593 / 2404**: a *central subuniverse* is defined internally — `C` is an absorbing subuniverse of `D` and for every `a ∈ D\C`, `(a,a) ∉ Sg_{D²}(({a}×C) ∪ (C×{a}))` (2005.00593 L279–284). `Sg` is a finite closure; and since every central subuniverse is **ternary** absorbing (Cor 6.11.1, L1591), "absorbing" may be replaced by "ternary absorbing", which is again a finite fixpoint. Thm 6.15 (L1670) connects the two notions. **Use the 2404 definition.** |
| `A/σ` is **polynomially complete** | the clone generated by `w` and all constants is *all* operations — a condition on operations of every arity | **yes** | by **Sierpiński**: every operation of arity `≥2` on a finite set is a composition of binary ones. So `Clo(w, constants) = O_A` iff its **binary** part is all of `A^{A²}` (unary then follows: `u(x) = b(x,x)` for `b(x,y):=u(x)`). Finite fixpoint again |
| `σ` is a **congruence** / **maximal congruence** / **minimal linear congruence** | quantifies over equivalence relations on `D` | **yes** | `≤ Bell(|D|)` candidates, each check finite |
| `σ` is **irreducible** / **linear** / **PC** (2404) | `σ*` = least `δ ⊋ σ` stable under `σ`; linear iff `∃` a bridge `δ ≤ D⁴` from `σ` to `σ` with `δ̃ ⊋ σ` (`LEMLinearEquivalentConditions`) | **yes** | subalgebras of `D⁴` form a finite lattice (`≤ 2^{|D|⁴}` sets to filter) |
| `D/σ ≅ (Z_p; x_1+…+x_m)`, "`D/σ` is linear" | isomorphism to a product of prime fields | **yes** | finitely many candidate abelian-group structures / bijections |
| **all weaker constraints** of `C` | `{(Y,ρ') : Y ⊆ Var(C), ρ' ⊇ pr_Y ρ, ρ' a subalgebra}` minus those equivalent to `C` | **yes** | finite; but note the *conjunction* of all weaker constraints equals `ρ` unless `ρ` is critical — so "weakening" may be a no-op **as a solution set** while still changing the instance syntactically. That is fine for the algorithm (progress is measured by the multiset of relations, not by the solution set) but must be understood |
| `Θ` **irreducible** | `∀` over sub-instances of projections | in principle exponential; the algorithm uses the polynomial `CheckIrreducibility` + Lemma 5.4 | |
| `Θ` **linked**, **fragmented**, **cycle-consistent** | graph reachability | **yes, polynomial** | |
| the special WNU `w` | derived from an idempotent WNU (1704 L343–345, citing "Lemma 4.7 in [47]") | **yes**, computable | but it is an *input* to the algorithm; the Lean statement should take `w` as data |

**Lean note.** All of the "yes" rows are *free* `Decidable` instances in Lean 4: they are bounded quantifications over `Fintype`s (`Fintype.decidableForallFintype`, `Finset` operations). The only ones needing work are the two least-fixpoint computations (binary/ternary parts of a clone, `Sg`), which are `Finset` closures — easiest as `Nat.rec`-bounded iteration with a proof that iterating `|D|^{|D|^3}` times reaches the fixpoint, or via `Relation.ReflTransGen` + a decidability instance. Nothing here is research-level; it is a day or two of engineering each.

---

## 7. What "this algorithm is correct" would take in Lean — and what it would *not* prove

### 7.1 Separate the two statements

**(C) Combinatorial correctness** — a pure proposition about a recursive function:
> There is a function `solve : Instance → Bool` such that `∀ I, solve I = true ↔ I.HasSolution`.

**(P) Complexity** — a statement about a cost model:
> `solve` is computable within `C · size(I)^d` steps of *some specified machine*.

(C) is formalizable now. (P) is not, without first building a cost model, because **Mathlib has essentially no complexity theory** (worth re-verifying against the current Mathlib before committing): `Mathlib/Computability/*` provides Turing machines (`Turing.TM0/TM1/TM2`), primitive/partial recursive functions, many-one reducibility, and the halting problem, but **no time-bounded classes, no `P`, no `NP`, no cost semantics for Lean functions**. Formalizing `P` seriously is the Cook–Levin-scale project (cf. Gäher–Kunze in Coq, Balbach in Isabelle) and is orthogonal to CSP.

Note also that (C) *alone* is mathematically vacuous as a statement about `CSP(Γ)`: satisfiability of a finite-domain CSP instance is trivially decidable by brute force. All of the content of the tractability half lives in (P). **Any honest blueprint must say this out loud.** What (C) buys is that it forces every one of Theorems 5.1/5.5/5.6/5.7 to be stated and proved, and pins down the exact hypotheses under which each reduction is safe — which is the mathematics.

### 7.2 Recommended formulation: fuel + explicit cost

Define the algorithm as a **fuel-indexed** function (structurally recursive on `fuel`, so no well-founded-recursion pain, and `partial_fixpoint`/`termination_by` obligations disappear):

```lean
variable {A : Type} [Fintype A] [DecidableEq A]
variable {m : ℕ} (w : (Fin m → A) → A) (hw : IsSpecialWNU w) (k₀ : ℕ)

structure Instance (w) (k₀) where
  vars        : Finset V
  dom         : V → Finset A
  dom_sub     : ∀ x, Subuniverse w (dom x)
  cons        : List (Constraint w k₀ dom)      -- scope + relation + proof it is a subalgebra

def Instance.HasSolution (I : Instance w k₀) : Prop :=
  ∃ f : V → A, (∀ x ∈ I.vars, f x ∈ I.dom x) ∧ ∀ C ∈ I.cons, C.Satisfied f

def solve : ℕ → Instance w k₀ → Option Bool     -- none = out of fuel
```

Then three theorems:

```lean
-- (1) partial correctness: whatever it says, it says truly.        [induction on fuel]
theorem solve_sound (n : ℕ) (I : Instance w k₀) (b : Bool) :
    solve w k₀ n I = some b → (b = true ↔ I.HasSolution)

-- (2) termination: enough fuel always suffices.                    [well-founded on μ]
theorem solve_total (I : Instance w k₀) :
    ∃ n, solve w k₀ n I ≠ none

-- (3) efficiency: *polynomially* much fuel suffices.               [the depth argument]
theorem solve_poly (hΓ : …) :
    ∃ (C d : ℕ), ∀ I : Instance w k₀,
      solve w k₀ (C * I.size ^ d) I ≠ none
```

Theorem (3) is the honest surrogate for "in P". Its honesty depends entirely on what one unit of `fuel` is charged for. **Write that down as a definition, and state the caveat as a comment/remark, not as a theorem**: e.g. "one unit of fuel = one evaluation step of `solve`, where the primitive operations are: membership/union/intersection/projection of `Finset`s of tuples over `A` of arity `≤ k₀` (unit cost), Gaussian elimination over `Z_p` for `p | m−1` (unit cost per call, itself separately bounded), and graph reachability on the instance (unit cost per call)". Then the reader can see precisely which gap remains between (3) and "`CSP(Γ) ∈ P`": a simulation theorem for the primitives on a bit-level machine. That gap is *real* but *shallow* (all primitives are trivially polynomial in `size(I)` for fixed `A, k₀`), and saying so plainly is the honest move.

A **stronger and still cheap** variant: instrument `solve` to return the exact number of primitive operations,
`solveC : Instance → Bool × ℕ`, and prove `(solveC I).2 ≤ C * I.size ^ d` together with `(solveC I).1 = true ↔ I.HasSolution`. This makes the cost model a *definition inside the formalization* and removes all hand-waving except the final "primitive ops are polynomial-time on a TM".

**What I would *not* do**: state the theorem as `CSP Γ ∈ P` with a home-made `P` unless you are prepared to also build (i) an encoding `Instance → List Bool`, (ii) a machine model with a step function, (iii) a compiler or simulation from the Lean function to that machine. That is a second project of comparable size to the CSP mathematics.

### 7.3 Which algorithm to formalize

You are free to formalize *any* correct algorithm; the theorem is about `CSP(Γ)`, not about Zhuk's code. Recommendations:

1. **Base the vocabulary on 2404** (strong subuniverses `<_{BA}, <_C, <_{PC}, <_L`, `⋘`, S-free, perfect linear congruence), because (a) it avoids Rosenberg's classification of maximal clones entirely, (b) its "center" is decidable by definition, (c) `THMCSPDReductionsAreSafe` merges Theorems 5.5 and 5.6 with weaker hypotheses.
2. **Base the control flow on 1704** (`Solve`/`AnswerOrReduce`/`SolveLinearCase`), because 2404's `SolveLinear` sketch has the two defects [FLAG-2404-WEAKEN] and [FLAG-2404-P2], while 1704's version is fully justified by its own theorems.
3. **Simplify where the theorems allow.** Concretely:
   * Replace `CheckWeakerInstance` + `WeakenEveryConstraint` by nothing **only if** you can prove Zhuk's Problem 2 — do not assume it. Keep it.
   * Replace `FindEquationsNonlinked/FindOneEquationNonlinked/CheckTuple/SolveNonlinked` by the cleaner 2404 `(p2)`: split the non-linked instance into linked components, recurse on each (smaller domains, after re-establishing 1-consistency), and take the union — plus the lemma "the union is an affine subspace". This removes four functions and the `I := {1}` bug.
   * Merge the three consistency checks into one `ForceConsistency` that returns a reduction or `⊥`, with a single specification: "returns `⊥` only if unsatisfiable; otherwise returns a domain reduction that preserves satisfiability; and if it returns 'no change' then the instance is cycle-consistent, irreducible, and its full weakening has subdirect solution set".
4. **Make the "language" a parameter with closure properties**, not a literal finite set: `Γ = { ρ : arity ≤ k₀, ρ preserved by w }` should be *defined*, and the three closure lemmas (intersection with subuniverse boxes, projections, weaker constraints) proved once.

### 7.4 Cost estimate / module sketch

```
Zhuk/Algebra/            WNU, special WNU, Clo, subuniverse, congruence, quotient, linear algebra
Zhuk/Algebra/Sierpinski  binary generation ⇒ decidability of PC              (small)
Zhuk/Strong/             BA, central, PC, linear subuniverses; ⋘; S-free; bridges; σ*   (big)
Zhuk/Strong/Ubiquity     LEMUbiquity  (= Thm 5.1 without Rosenberg)          (big)
Zhuk/Instance/           instances, solutions, 1-/cycle-consistency, linked, fragmented,
                         irreducible, weakening, coverings, crucial, Lemma 6.1, Lemma 6.2
Zhuk/Instance/Linear     Lemma 7.20, factorisation Θ ↦ Θ_L, affineness of A and B
Zhuk/MainClaims/Safe     THMCSPDReductionsAreSafe (5.5 + 5.6)                (very big)
Zhuk/MainClaims/Codim    THMCodimensionOneTheorem (5.7)                      (very big)
Zhuk/Algorithm/Defs      solve (fuel-indexed), all subroutines
Zhuk/Algorithm/Sound     solve_sound          — uses Lemmas 5.3, 5.4 + the four theorems
Zhuk/Algorithm/Total     solve_total          — the measure μ of §4
Zhuk/Algorithm/Cost      solve_poly           — depth ≤ |A|+|Γ| (with the [FLAG-DEPTH] fix)
Zhuk/Dichotomy           tractability half; + core/idempotent reduction (separate import)
```
Rough proportions: the four main theorems are ≥ 80% of the work; `Algorithm/*` is maybe 10–15%, of which `Cost` is the least interesting and the most tedious. `Algorithm/Sound` is the part that *forces* the main theorems to be stated with exactly the right hypotheses, so it is worth writing early, even as `sorry`-ed statements, to fix the interfaces.

### 7.5 Imports the tractability half needs that are *not* in the algorithm section

* **The core / idempotency reduction.** Zhuk's §4 assumes `Γ0` is preserved by an **idempotent** WNU. For a general `Γ` preserved by a WNU one must: pass to a core, add all constants (singleton unary relations), and observe the resulting language has an idempotent WNU polymorphism and a polynomial-time equivalent CSP. Standard (Bulatov–Jeavons–Krokhin) but **not proved in either Zhuk paper**, and it is a genuine polynomial-time *reduction*, so it also needs the cost model.
* **Special WNU from idempotent WNU** (1704 L343–345, "not hard to show", citing Lemma 4.7 of [47]) — a small but real lemma.
* **Rosenberg's classification of maximal clones** — needed *only* if you follow 1704's Theorem 5.1. Avoided by 2404's `LEMUbiquity`. This alone justifies the 2404 route.
* **`Γ` finite / arity bound `k0`.** The algorithm is only polynomial for a *fixed* `Γ`; the uniform problem (CSP-WNU, §10.1 L4200–4215) is open.

---

## 8. Consolidated list of flags

| tag | where | what |
|---|---|---|
| **FLAG-FEN-BUG** | 1704 `FindEquationsNonlinked` L711 | `I := {1}` should be `I := ∅`; otherwise equations are lost when `z_1` is constrained (explicit 2-variable counterexample in §2.7). Breaks the "dimension strictly decreases" invariant |
| **FLAG-DEPTH** | 1704 Lemma 5.2, L1006–1008 | "we reduce all domains of size >1 before using the recursion" is false for `CheckTuple → SolveNonlinked`; without a fix the depth is `O(n|A|)` and the algorithm is not polynomial. Fix: 1-consistency propagation inside `SolveNonlinked` + the lemma "1-consistent + non-fragmented + non-linked ⇒ every component meets every domain properly" |
| **FLAG-INNER-LOOP** | 1704 Cor 5.2.1, L1030–1032 | "`|Γ|·N` passes" ignores that weakening multiplies the number of constraints; correct bound needs a weighted potential `Σ (K+1)^{rank}` |
| **FLAG-GAMMA-ORDER** | 1704 L1017 | "we never make any relation bigger" holds for weakening only because the instance is already 1-consistent; unstated |
| **FLAG-AFF** | 1704 L596–598 and everywhere | "(almost subspaces)" — every `k+1`-query shortcut is really Lemma 7.20 applied to the image of a solution set under `∏D → ∏L` |
| **FLAG-TYPES** | 1704 `FindOneEquation*` | returned equations mix variables over different prime fields; well-typed only because Lemma 7.20 forces the cross-prime coefficients to vanish |
| **FLAG-COORD** | 1704 `SolveLinearCase` L23 | equation returned in `y`-coordinates is silently pulled back to the `z`-coordinates of `Eq` |
| **FLAG-CYL** | 1704 `CheckTuple` | correctness needs `ψ(R)` to be a **product set**; true because `R` is a cylinder and `ψ` is coordinatewise, but unstated |
| **FLAG-RT** | 1704 `RemoveTrivialities` | "constraints without non-dummy variables" ambiguous (full vs empty); non-deterministic; only the contract "weakening with the same solution set, no dummies" is used |
| **FLAG-PROJ** | 1704 `CheckCycleConsistency` L6 | projection onto variables not in the scope is undefined; the diagonal case `i=j` is used implicitly to get 1-consistency |
| **FLAG-53 / 53b** | Lemma 5.3 proof; §3.3 | one-sentence induction on path length; and "hypothesis (3) of Thm 5.7 passes to weakenings" is used but never stated |
| **FLAG-IRRED-WD** | `CheckIrreducibility`, Lemma 5.4 | the propagated partition must be shown independent of the choice of constraints/order (proved by gluing paths + cycle-consistency, in one sentence) |
| **FLAG-IRRED-QUANT** | definition of irreducible | `∀` over sub-instances of projections; the polynomial test is only *equivalent* by Lemma 5.4 |
| **FLAG-2404-WEAKEN** | 2404 main.tex L698–703 | `SolveLinear` **removes** constraints where `THMCodimensionOneTheorem`(7) needs **weakening**; only valid after saturating the instance with all weaker constraints — unstated |
| **FLAG-2404-P2** | 2404 main.tex L660–666 + L705–709 | `(p2)` returns a union of affine subspaces which is then used as an affine subspace |
| **FLAG-2404-STRONG** | 2404 main.tex L626 | "strong subset" in `Solve` must exclude type `L`; `THMCSPDReductionsAreSafe` covers only `BA, C, PC` |
| **FLAG-CENTER-DEC** | 1704 §3.5 | the 1704 definition of *center* quantifies over all finite algebras `B`; not obviously decidable. Use 2005/2404 *central subuniverse* |
| **FLAG-COST-MODEL** | throughout | "polynomial" is in an unstated unit-cost RAM model over relations of arity `≤ k0`; degree is `O(|A| + |Γ|)` with `|Γ| ≤ 2^{|A|^{k0}}` |

---

## 9. One-paragraph recommendation

Formalize the mathematics with 2404's vocabulary and the three main claims exactly as `THMCSPDReductionsAreSafe`, `THMCodimensionOneTheorem`, `LEMUbiquity`. Formalize the *algorithm* as a fuel-indexed Lean function following 1704's control flow with the four simplifications in §7.3, and state the tractability half as the pair "partial correctness + polynomially much fuel suffices", with the cost model written down as a definition and the residual gap to "`∈ P`" stated as an explicit remark rather than papered over. Do not claim `P` unless you build a machine model. Budget the `Cost` module last: it is the least mathematically interesting part and it contains the one place where Zhuk's published argument actually needs repair ([FLAG-DEPTH]).
