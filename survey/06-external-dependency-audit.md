# 06 — External dependency audit of Zhuk, arXiv:2404.01080v2

*"A simplified proof of the CSP Dichotomy Conjecture and XY-symmetric operations"*

Scope: every `\cite{...}` that appears **inside a theorem/lemma header, immediately before a
statement, or inside a proof** in `main.tex`, `StrongSubalgebras.tex`, `XYSymmetric.tex`,
`necessaryClaims.tex`; plus the results the paper uses without stating them at all
(the algorithm, the core reduction, NP-hardness).

Method: mechanical extraction of all 62 `\cite{...}` occurrences (71 bibliography keys), then a per-statement check of
whether a `\begin{proof}` follows the statement (directly or via the restated
`\newtheorem*{...LEM}` mechanism used in Sections 4 and 5). Everything below was verified
against the on-disk sources; line numbers are from the arXiv LaTeX source, page/lemma numbers
from the pdftotext dumps.

---

## 0. Headline

* **2404.01080 is not the CSP Dichotomy Theorem.** It proves exactly two statements
  (`THMCSPDReductionsAreSafe`, `THMCodimensionOneTheorem`, main.tex:3985 and :4004) plus
  the XY-symmetric theorem. The algorithm, its running time, the reduction to cores/idempotent
  algebras, the NP-hard half, and even the third correctness ingredient
  (Informal Claim 1, main.tex:518) are **not in the paper**.
* **19 statements are imported as black boxes** (16 with no proof at all, 3 with a proof that
  covers only some of the cases and cites elsewhere for the rest). One further statement
  (`CORPropagationModuloCongruence`) is stated, used 6×, and never proved anywhere — though it
  is an immediate specialisation of a lemma that *is* proved.
* Of these, the on-disk sources contain full proofs for **13**. Two (`miklos` Lemma 4.7;
  `hobby1988structure`) are not on disk at all; one of the on-disk proofs
  (JACM Theorem 8.17) itself bottoms out in a paper that is **not** on disk
  (Zhuk, *Key (critical) relations preserved by a WNU*, ref [62] of the JACM paper).
* The transitive closure, measured in "paper pages that must actually be formalised", is
  roughly **54 (2404) + 35 (Zhuk 2021 §3–§6) + ~15 (JACM bits) + ~25 (Brady: absorption
  theorem, abelian⇒affine, Galois connection) + ~12 (NP-completeness base)** ≈ **140 pages**,
  against ~54 pages if you only did 2404. See §3.

---

## 1. The black-box table

Legend for the **Use** column: number of `\ref{}` occurrences in the whole source.
Legend for **Diff**: trivial / moderate / hard / very hard, as a Lean-4 formalization estimate.

### 1.1 Imports with no proof anywhere in 2404

| # | Label (file:line) | Statement (verbatim-faithful) | Cited to | Proof actually lives | Use | Diff |
|---|---|---|---|---|---|---|
| 1 | `LEMExistenceOfSpesialWNULemma` (necessaryClaims.tex:5) | Suppose $w$ is an idempotent WNU operation on $A$. Then there exists a special idempotent WNU operation $w'\in\Clo(w)$ of arity $n^{n!}$. ("special": $w(x,\dots,x,y)=w(x,\dots,x,w(x,\dots,x,y))$, main.tex:1080.) | `miklos` = Maróti–McKenzie, *Existence theorems for weakly symmetric operations*, Alg. Univ. 59 (2008), **Lemma 4.7** | **NOT ON DISK.** JACM 1704.01914:343–345 also just cites it. Nothing in 2005.00593, 2104.11808 or csp.tex. | 2 | moderate (**but see gap G1**) |
| 2 | `LEMBuildingPerfectCongruence` (necessaryClaims.tex:14) | Suppose $\sigma$ is an irreducible congruence on $\mathbf A\in\mathcal V_n$ and $\delta$ is a bridge from $\sigma$ to $\sigma$ with $\widetilde\delta=A^2$. Then $\sigma$ is a perfect linear congruence. | `zhuk2020proof` **Cor. 8.17.1** | 1704.01914.txt:2596–2598, whose proof is Theorem 8.17 at :2528–2595 (≈2 pp). **Theorem 8.17 in turn invokes Theorem 8.15 (strongly rich relations) from ref [62], which is NOT on disk**, and Lemma 8.16 (= Zhuk 2021 Lemma 4.1, on disk at 2005.00593:404–425). | 3 | **hard**; see §1.4 for the alternative route already present in 2404 |
| 3 | `LEMBridgeComposition` (necessaryClaims.tex:23) | $\sigma_1,\sigma_2,\sigma_3$ irreducible congruences, $\rho_1$ a bridge $\sigma_1\to\sigma_2$, $\rho_2$ a bridge $\sigma_2\to\sigma_3$. Then $\rho(x_1,x_2,z_1,z_2)=\exists y_1\exists y_2\,\rho_1(x_1,x_2,y_1,y_2)\wedge\rho_2(y_1,y_2,z_1,z_2)$ is a bridge $\sigma_1\to\sigma_3$, and $\widetilde\rho=\widetilde{\rho_1}\circ\widetilde{\rho_2}$. | `zhuk2020proof` **Lemma 6.3** | 1704.01914.txt:1370–1385, ~12 lines, elementary. | 4 | **trivial–moderate** (pure relational bookkeeping; the only content is that irreducibility gives $\proj_{3,4}(\rho_1)\supseteq\sigma_2^*$) |
| 4 | `LEMCenterImpliesTernaryAbsorption` (main.tex:1355) | Suppose $B$ is a central subuniverse of $\mathbf A$; then $B$ is a ternary absorbing subuniverse of $\mathbf A$. | `zhuk2021strong` **Cor. 6.11.1** | 2005.00593:1591–1595, via Lemmas 6.10, 6.11, 6.7, 3.2 (≈2.5 pp). | **0** — stated for context, never used | **already done**: `/home/alvaro/claude/zhuk-lean`, 1 670 Lean lines |
| 5 | `LEMBACenterImplies` (main.tex:1753) | $R\le A_1\times\dots\times A_n$, $C_i\le_T A_i$ for all $i$, $T\in\{\TBA,\TC\}$. Then $\proj_1(R\cap(C_1\times\dots\times C_n))\dot\le_T A_1$. | `zhuk2021strong` **Cor. 6.1.2 and 6.9.2** | 2005.00593:1383–1392 and :1539–1540. Both are 3-line corollaries of Lemma 6.1 / Theorem 6.9 (= item 6 below). | 8 | trivial *given* item 6 |
| 6 | `LEMBACenterSImplyPPDefinition` (StrongSubalgebras.tex:95) | $R\le A^n$ defined by a pp-formula $\Phi$ containing a relation $S$; $\Phi'$ obtained from $\Phi$ by replacing **each appearance** of $S$ by $S'<_T S$, $T\in\{\TBA,\TC\}$. Then $\Phi'$ defines $R'$ with $R'\le_T R$. | `DecidingAbsorption` Lemma 2.9; `zhuk2021strong` **Lemma 6.1, Theorem 6.9** | 2005.00593: Lemma 6.1 at :1359–1375 (10 lines, easy); Theorem 6.9 at :1523–1535, which needs Lemmas 6.3–6.8 and Cor. 6.8.1 (≈4 pp of §6.2). | **11** (the single most-used import) | moderate for BA; **hard** for the central case (drags in the whole $\Sg\!\begin{smallmatrix}e&C\\C&e\end{smallmatrix}$ minimality machinery, Lemma 6.7) — *already covered by zhuk-lean* |
| 7 | `LEMBACenterImplyIntersection` (StrongSubalgebras.tex:108) | $B\le_T\mathbf A$, $C\le\mathbf A$, $T\in\{\TBA,\TC\}$ ⟹ $B\cap C\le_T C$. | *(no cite; "The above lemma implies an easier claim.")* | 2005.00593 Lemma 6.5 (central) / Cor. 6.1.3 (BA). | 3 | trivial given 6 |
| 8 | `LemAbsorptionImpliesEssential` (StrongSubalgebras.tex:159) | $B\le\mathbf A$, $n\ge 2$. $B$ is an absorbing subuniverse with an operation of arity $n$ **iff** there is no $S\le A^n$ with $S\cap B^n=\varnothing$ and $S\cap(B^{i-1}\times A\times B^{n-i})\neq\varnothing$ for every $i$. | `DecidingAbsorption` Prop. 2.14; `zhuk2021strong` **Lemma 3.2** | 2005.00593:1409–1432 — a full proof is given there (uses Lemma 6.2 at :1397–1407). ≈1.5 pp. | 1 | **moderate** (the ⇐ direction is a clean but fiddly $|A|^{k}$-column matrix argument) — *already in zhuk-lean* (`Essential.lean`) |
| 9 | `LEMBACenterLinkedness` (StrongSubalgebras.tex:194) | $R\le_{sd}A_1\times A_2$; $B_1,B_2$ absorbing subuniverses of $\mathbf A_1,\mathbf A_2$; $R\cap(B_1\times B_2)\le_{sd}B_1\times B_2$; $R$ linked. Then $R\cap(B_1\times B_2)$ is linked. | `barto2012absorbing` **Prop. 2.15 (i)** | Not in the Barto–Kozik paper on disk (absent). Brady csp.tex:8697 `\begin{thm}[Absorbing linked components]` states/proves the Jónsson-absorption version in 3 lines, but it depends on `absorbing-directed-path` earlier in §"Absorption, Jónsson absorption, and connectivity" (csp.tex:8540–8760). | 1 | moderate (≈2 pp incl. the directed-path theorem) |
| 10 | `LEMCentralRelationImplies` (StrongSubalgebras.tex:208) | $\mathbf R\le_{sd}\mathbf A\times\mathbf B$, $C=\{c\in A\mid \forall b\in B: (c,b)\in R\}$. Then **(1)** $C$ is a central subuniverse of $\mathbf A$, or **(2)** $\mathbf B$ has a nontrivial binary absorbing subuniverse. | `zhuk2021strong` **Theorem 6.15** | 2005.00593:1673–1732 (≈2 pp). **The source theorem has THREE cases**; case (3) is "$\mathbf B$ has a nontrivial projective subuniverse". | **8** | **hard**; and see gap **G2** |
| 11 | `LEMLinkedImpliesBACenter` (StrongSubalgebras.tex:220) | $R\lneq_{sd}\mathbf A\times\mathbf B$, $R$ linked. Then there exists a BA or central subuniverse on $\mathbf A$ or on $\mathbf B$. | `ZebsNotes` **Theorem 3.11.1** | This is the **Absorption Theorem** of Barto–Kozik. Brady csp.tex:10451 (`absorption-theorem`) with a complete proof (≈1.5 pp) built on `zhuk-center` (csp.tex:10257) and `bin-central-criterion` (csp.tex:10413), i.e. on all of csp.tex §"Zhuk's centers and ternary absorption" (10128–10442, ≈8 pp). | **5** | **very hard** — this is the single largest genuinely-external theorem |
| 12 | `LEMAbsorbingEquality` (StrongSubalgebras.tex:229) | $0_{\mathbf A}\subseteq\sigma\le\mathbf A^2$ and $\omega<_{BA}\sigma$. Then $\omega\cap 0_{\mathbf A}\neq\varnothing$. | `zhuk2020proof` **Lemma 7.2** | 1704.01914:1446–1468 (~18 lines) + Lemma 7.1 (pp-compatibility of BA absorption). | 1 | moderate (induction on $|A|$, short) |
| 13 | `LEMAbelianEquivalentDefinition` (StrongSubalgebras.tex:1077) | $\mathbf A$ is Abelian iff there exists a congruence $\delta$ on $\mathbf A^2$ such that $\{(a,a)\mid a\in A\}$ is a block of $\delta$. | `hobby1988structure` (Hobby–McKenzie, *The structure of finite algebras*) | **Book not on disk.** Brady csp.tex:10674 takes the block-of-congruence property as the *definition* of abelian; the equivalence with the term condition ($t(x,\bar u)=t(x,\bar v)\Rightarrow t(y,\bar u)=t(y,\bar v)$) is a short exercise. | 1 | **trivial–moderate** (a genuinely easy equivalence, ~20 lines of Lean once $\Sg$ is available) |
| 14 | `LEMAbelianEqualAffineForWNU` (StrongSubalgebras.tex:1098) | Suppose a finite algebra $\mathbf A$ has a WNU term operation. Then $\mathbf A$ is Abelian iff it is affine. | `hobby1988structure` | **Book not on disk**, but Brady csp.tex has a complete modern proof: §"Finite abelian Taylor algebras are affine" (10670–10855) in three steps — (i) abelian ⇒ hereditarily absorption-free, (ii) idempotent Taylor + hereditarily absorption-free ⇒ Mal'cev, (iii) abelian Mal'cev ⇒ affine (§`s-abelian-malcev`, csp.tex:4235–4707, ≈10 pp). | 1 | **very hard** (~15 pp of prerequisites incl. modules, polynomial equivalence, Mal'cev theory) |

### 1.2 Partial imports (proof given for some cases, cited for others)

| # | Label (file:line) | Statement | What is imported | Where |
|---|---|---|---|---|
| 15 | `LEMBACenterSImplyFactor` (SS:138) | $B\le_T A$, $\sigma$ a congruence on $A$, $T\in\{\TBA,\TC,\TS\}$ ⟹ $B/\sigma\le_T A/\sigma$. | Proof says: "For $T=\TBA$ it is straightforward, for $T=\TC$ **see Lemma 6.8 in `zhuk2021strong`**, for $T=\TS$ it is just a combination". | 2005.00593:1497–1510 (14 lines, uses Lemma 6.7). **15 uses** — the single most-referenced lemma in the paper. |
| 16 | `LEMBACenterSOnPowerImplies` (SS:169) | $B<_T A^n$, $T\in\{\TBA,\TC,\TS\}$ ⟹ there exists $C<_T A$. | "For $T\in\{\TBA,\TC\}$ **see Lemma 6.24 in `zhuk2021strong`**. For $T=\TS$ just repeat the same proof **word to word** replacing $\TBA$ by $\TS$." | 2005.00593:1937–1948 (12 lines). 11 uses. The "word to word" is a genuine (if benign) hand-wave; see **G4**. |
| 17 | `LEMReverseHomomorphism` (SS:301) | $f:\mathbf A\to\mathbf A'$ surjective hom., $T\in\{\TBA,\TC,\TS,\TL,\TD\}$: $C'<_{T(\sigma)}^{A}B' \Rightarrow f^{-1}(C')<_{T(f^{-1}(\sigma))}^{A}f^{-1}(B')$. | "For $T\in\{\TBA,\TC\}$ it follows from the properties of a homomorphism (**see Section 3.15 in `ZebsNotes`**)." | csp.tex has the pp-compatibility of $\lhd$ and $\lhd_Z$ scattered in §"Absorption…" and §"Zhuk's centers…"; the cited numbering **3.15 does not match the on-disk csp.tex** (see **G5**). 6 uses. |

### 1.3 Cited-but-actually-proved (not black boxes)

| Label | Cited to | Note |
|---|---|---|
| `LEMBridgeBetweenCongruences` (SS:1740) | `zhuk2020proof` Lemma 8.19 | **Full proof given in 2404** (SS:1752–1778). Cheap: an explicit pp-definition of the bridge. |

### 1.4 Stated, used, never proved (not even cited)

* `CORPropagationModuloCongruence` (main.tex:1682, 4 clauses (f)/(t)/(s)/(m)). Referenced 6× —
  including inside the proofs of `CORPropagateMultiplyByCongruence` — but there is no
  `\begin{proof}` and no `\newtheorem*{CORPropagationModuloCongruenceCOR}` restatement in
  `StrongSubalgebras.tex`. It *is* the special case $f=$ the quotient map $\mathbf A\to\mathbf A/\delta$
  of `LEMPropagation` (which is proved as `LEMPropagationLEM`). Harmless, but a blueprint must
  insert the derivation explicitly.

### 1.5 The *alternative* route the paper already contains for import #2

`LEMBuildingPerfectCongruence` (JACM Cor. 8.17.1) is the only import whose on-disk proof bottoms
out in a paper we do not have. But 2404 itself proves a very close statement:

* `LemBridgeEquivalentToAbelianness` (SS:1082) — $\mathbf A$ Abelian $\iff$ exists a bridge
  $\delta$ from $0_{\mathbf A}$ to $0_{\mathbf A}$ with $\widetilde\delta=\proj_{1,2}(\delta)=\proj_{3,4}(\delta)=A^2$;
* `LEMNiceBridgeGivesAbelianGroup` (SS:1103) — given a symmetric bridge $\delta$ from $\sigma$ to
  $\sigma$ with $\proj_{1,2}(\delta)=\widetilde\delta=A^2$, there is an abelian group $G$ with
  $(A/\sigma;\delta/\sigma)\cong(G;x_1-x_2=x_3-x_4)$.

These are exactly Zhuk's own remark in the JACM proof ("the remaining part of the proof could also
be derived from known facts of commutator theory … we do not want to introduce new algebraic
notions", 1704.01914:2561–2566). So the recommended route is: **drop the JACM Cor. 8.17.1 import
and derive it from `LEMNiceBridgeGivesAbelianGroup` + `LEMAbelianEqualAffineForWNU`**, which trades
the unavailable *Key relations* paper for the (available, but large) abelian⇒affine theorem — an
import we need anyway. This is a route decision worth making early.

---

## 2. The NP-hardness side

### 2.1 What 2404 says

main.tex:431–433, a single sentence with no statement and no proof:

> "The NP-hardness for constraint languages without a WNU follows from
> `\cite{bulatov2001algebraic,CSPconjecture}` and `\cite{miklos}`."

`bulatov2001algebraic` = Bulatov–Jeavons, *Algebraic structures in combinatorial problems* (TU
Dresden tech. report, 2001); `CSPconjecture` = Bulatov–Jeavons–Krokhin, SICOMP 34(3) 2005;
`miklos` = Maróti–McKenzie 2008. None of these is on disk.

### 2.2 The self-contained proof in `2005.00593` (Zhuk, *Strong subalgebras and the CSP*)

Yes — §5.3, `Theorem 5.5` at 2005.00593.txt:827–844 is a genuinely self-contained NP-hardness
proof, modulo two classical outside results. Verbatim statement:

> **Theorem 5.5.** Suppose $\Gamma$ does not have a WNU polymorphism, then $\mathrm{CSP}(\Gamma)$ is NP-hard.

Its dependency tree, all resolved inside 2005.00593 unless marked ⚑:

```
Theorem 5.5  (§5.3, ~23 lines)
├── Lemma 5.2   unary polymorphism f ⟹ CSP(Γ) ≡_p CSP(f(Γ))        (:781, 3 lines, trivial)
├── Theorem 5.4 core + all constants ⟹ poly-reducible to the core   (:801–818, ~20 lines)
│   └── Lemma 5.3  Sg_{A^k}((0,…,k−1)) has a quantifier-free pp-def (:790–799, ~8 lines)
├── Theorem 4.14 (1)⇔(3)⇔(4): no WNU ⟺ ∃ WNU-blocker in Inv(A)      (:692–712)
│   ├── Lemma 4.8   a WNU-blocker (B0∪B1)³∖(B0³∪B1³) is preserved by no idempotent WNU  (:601–613)
│   ├── Lemma 4.10  essentially-unary B ∈ HS(A) ⟹ WNU-blocker ∈ Inv(A)  (:629–633, 4 lines)
│   ├── Lemma 4.5   no n-ary WNU ⟹ ess.-unary or p-affine in HS(A)   (:536–557)
│   │   ├── Lemma 4.4  symmetric R ≤ Aⁿ has a constant tuple, or …   (:486–534, ~50 lines)
│   │   │   ├── Theorem 3.3  the FOUR/FIVE TYPES THEOREM             (:2226–2254 + all of §6)
│   │   │   ├── Theorem 3.5  strong subuniverses propagate           (:1971–1988)
│   │   │   └── Lemma 3.4    projective ⟹ ess.-unary in HS(A)        (:1950–1969)
│   │   ├── Cor 4.2.1 ← Lemma 4.2  HSP → HS                          (:430–449)
│   │   └── Cor 4.3.1 ← Lemma 4.3  p-affine is hereditary            (:451–478)
│   └── Lemma 4.12  WNU-blocker ⟹ 2-WNU-blocker (for Thm 4.15)       (:647–666)
├── ⚑ Inv–Pol Galois connection: "R ∈ Inv(B) ⟹ R is pp-definable over Γ′"
│      (Geiger 1968 / Bodnarchuk–Kaluzhnin–Kotov–Romov 1969; = `geiger1968closed`,`bond1`,`bond2`)
└── ⚑ NP-hardness of CSP({NAE₃}) (Schaefer 1978, ref [27])
```

Note the parenthetical in Zhuk's proof — *"we also need the equality and empty relations but they
can always be propagated out from the pp-definition of R"* — that is a real, unstated side lemma
about normalising pp-definitions (see **G6**).

### 2.3 What the two ⚑ items cost

**Inv–Pol (the hard direction).** Needed in the form: if $R$ is preserved by every polymorphism of
$\Gamma'$ over a finite domain, then $R$ is pp-definable from $\Gamma'$. Proof: the indicator /
free-structure argument — $R$ is the projection of $\mathrm{Sg}_{B^{|B|^{k}}}(\text{all columns})$.
Brady csp.tex §"The Inv-Pol Galois connection" (1193–1372) + the multi-sorted version (1373–1561),
≈4 pp, entirely elementary but combinatorially heavy in indices. **Diff: moderate–hard.**
Nothing in Mathlib. Note 2404 itself only ever uses the *easy* direction (main.tex:2167,
"pp-definable ⟹ preserved"), so this cost is exclusive to the hardness half.

**NP-hardness of NAE-3-SAT.** This is where the formalization leaves algebra entirely. To make
"NP-complete" mean anything you need a machine model, polynomial-time reductions, Cook–Levin, then
3-SAT → 1-in-3-SAT → NAE-SAT. Brady csp.tex has the whole chain written out:
§"Crash course on NP-completeness" (701–1192, ≈12 pp): Turing machines, P/NP, logspace reductions,
Circuit-SAT (:967), `thm-3-sat-np-complete` (:977), 1-IN-3-SAT (:1008–1031),
`thm-nae-np-complete` (:1035).
**Mathlib has no complexity theory at all** — no Turing-machine-based P/NP (there is
`Computability.TuringMachine` but no resource bounds), no Cook–Levin. This is a **very hard,
independent project** (the Isabelle Cook–Levin formalization is ~30k lines).

**Pragmatic recommendation.** Formalize the hardness half as a *relative* statement:
"there is a polynomial-time many-one reduction from $\mathrm{CSP}(\{NAE_3\})$ to
$\mathrm{CSP}(\Gamma)$ whenever $\Gamma$ has no WNU polymorphism", i.e. take
NP-hardness of NAE-3-SAT as an axiom/hypothesis and prove the *reduction*. That keeps the
algebra (Theorem 4.14 + Galois) and drops Cook–Levin. The reduction itself is a clean, finite,
syntactic gadget substitution and is genuinely formalizable.

### 2.4 The elephant: `Theorem 3.3` (four/five types)

`Theorem 3.3` — *every finite idempotent algebra of size ≥2 has a nontrivial BA subuniverse, or a
nontrivial central subuniverse, or a nontrivial PC subuniverse, or a congruence $\sigma$ with
$\mathbf A/\sigma$ $p$-affine, or a nontrivial projective subuniverse* — underlies the whole
hardness argument (via Lemma 4.4). Its proof (2005.00593:2226–2254) needs essentially **all** of
§6: §6.1 absorbing (2 pp), §6.2 central (4 pp), §6.3 projective (2 pp), §6.4 central relations +
Rosenberg-style analysis of minimal-arity invariants (3 pp), §6.5 PC subuniverses (4 pp),
§6.6 common properties (3 pp), §6.7 linear algebras / Mal'cev (3.5 pp), §6.8 existence (2 pp) —
about **24 pages**. Key sub-results: Lemma 6.16 (full-projective relations give a central relation
or a nontrivial equivalence), Lemma 6.17 (relations preserved by *all* operations are conjunctions
of equalities), Lemmas 6.26–6.31 (linear/Mal'cev/p-affine), Lemma 6.33.

**Good news for the tractable half**: 2404 does **not** need Theorem 3.3. Its analogue,
`LEMUbiquity` (main.tex:1653: *$B\lll A$, $|B|>1$ ⟹ $\exists C<_T^A B$ with $T\in\{\TBA,\TC,\TL,\TPC\}$*),
is proved in 2404 (SS:2301) from `LEMMainExistenceOfIrreducibleCongruence` (SS:2185), which reduces to
the **Absorption Theorem** (import #11) instead of to the Rosenberg machinery. That is a real
simplification and a strong argument for routing the whole formalization through the
Absorption Theorem rather than through Zhuk 2021 §6.3–§6.8.

---

## 3. Total transitive-closure estimate

### 3.1 What has to exist that is *not* in 2404 at all

| Missing piece | Where it lives | Size | Needed for |
|---|---|---|---|
| The algorithm (`Solve`, `ForceConsistency`, `ReduceDomain`, `SolveLinear`) and its **polynomial running time** | 1704.01914 §"The algorithm" / FOCS'17. 2404 only gives pseudocode + prose (main.tex:593–780) and explicitly says "for the precise algorithm see \cite{zhuk2020proof,ZhukFVConjecture}". | ~10 pp + all the complexity bookkeeping | the "in P" half |
| **Informal Claim 1** (`ICExistenceStrong`, main.tex:518): each $D_x$ of size ≥2 has a strong subset, or an equivalence $\sigma$ with $D_x/\sigma\cong\mathbb Z_p$ | **No formal counterpart anywhere in 2404.** §`SectionCSPMainClaims` only states the other two claims. Closest 2404 statements: `LEMUbiquity` + `LEMLInearOnTheTopIsEasy` (main.tex:1454), but the step from "no BA/C/PC subuniverse ⟹ linear congruence with $\sigma^*=A^2$ ⟹ $\mathbf A/\sigma\cong\mathbb Z_p$" is nowhere assembled. | 1–2 pp of glue + `LEMUbiquity` | the algorithm's case split |
| Reduction to a core; adding all constant relations (⟹ idempotent) | 2005.00593 §5.2 (Lemmas 5.2, 5.3, Theorem 5.4), ~1.5 pp, self-contained | small | both halves |
| Reduction to "WNU of every arity $n\ge3$" / to $\mathcal V_n$ (special WNU of a fixed arity) | `miklos` Lemma 4.7 (import #1) + 2005.00593 Theorem 4.14/4.15 | ~1 pp + Theorem 3.3 | both halves |
| NP-hardness | 2005.00593 §5.3 + Galois + Schaefer | see §2 | the "NP-complete" half |

### 3.2 Page budget

| Block | Source | Pages that must be formalised |
|---|---|---|
| 2404 proper (main.tex §2–§3, StrongSubalgebras, XYSymmetric) | 2404 | ~50 (of 54) |
| Zhuk 2021 §6.1–§6.2 (absorption + central, incl. Lemma 3.2, 6.1, 6.7, 6.8, 6.24, 6.25, 6.10, 6.11.1) | 2005.00593 | ~7 — **already formalised**, 1 670 Lean lines in `zhuk-lean` |
| Zhuk 2021 Theorem 6.15 (central relation) + Lemmas 6.12–6.14 (projective) | 2005.00593 | ~3.5 |
| Zhuk 2021 §5.6 Lemma 5.6 (tree-coverings) | 2005.00593 | ~1 |
| Zhuk 2021 §4 (WNU existence / WNU-blockers) + §5.2–§5.3 | 2005.00593 | ~10 |
| Zhuk 2021 §6.3–§6.8 (Theorem 3.3 route) | 2005.00593 | ~15 — **avoidable** if you route through the Absorption Theorem for the tractable half, but **not** avoidable for the hardness half as written |
| JACM Lemma 6.1, Lemma 6.3, Lemma 7.1–7.2 | 1704.01914 | ~2 |
| JACM Theorem 8.17/Cor 8.17.1 **or** its abelian-commutator replacement | 1704.01914 / csp.tex | ~2 **or** ~15 (see §1.4) |
| Absorption Theorem + Zhuk centers (csp.tex `absorption-theorem`, `zhuk-center`, `bin-central-criterion`, essential doubling) | csp.tex 10128–10560 | ~10 (of which the doubling trick is already in `zhuk-lean/Doubling.lean`) |
| Abelian Taylor ⇒ affine | csp.tex 4235–4707 + 10670–10855 | ~15 |
| Inv–Pol Galois (hard direction) | csp.tex 1193–1561 | ~4 |
| Cook–Levin → NAE-3-SAT | csp.tex 701–1192 | ~12 (**or 0** if axiomatised) |
| Maróti–McKenzie Lemma 4.7 (special WNU) | not on disk | ~1 |
| **Total** | | **~130–145 pp** (≈95–110 if Cook–Levin is axiomatised and the JACM 8.17 import is taken as-is) |

### 3.3 Lean-line calibration

The one hard data point available: `zhuk-lean` formalises Zhuk 2021 §6.1 + §6.2 through
Cor. 6.11.1 — about **3.5 printed pages** — in **1 670 lines of Lean** across 13 modules
(`Absorbs`, `Essential`, `Central`, `Center`, `Doubling`, `StarPower`, `Regrouping`, `Product`,
`Relational`, `Step`, `Probe`, `Absorption`, `Ternary`), with a **1 830-line blueprint**
(`zhuk_centers.tex`). That is ≈**480 Lean lines per printed page**, and roughly 1:1
blueprint-LaTeX to Lean.

Extrapolating naively: **130 pp × 480 ≈ 62 000 lines of Lean**, with a blueprint of comparable
size. That is a multi-person-year project. The 2404 core alone (50 pp) is ≈24 000 lines.
Caveat in both directions: the centre theorem is unusually definition-dense (favourable ratio for
the rest), but 2404 §3 is unusually *instance*-heavy (CSP instances, coverings, reductions,
crucial/connected instances) and the combinatorial bookkeeping there will formalise worse than
algebra does.

---

## 4. Which imports are cheap, and which are projects in themselves

### 4.1 Cheap (a day to a week each)

* **#3 `LEMBridgeComposition`** — pure relational algebra, 12 source lines. The only subtlety is
  that irreducibility of $\sigma_2$ is used to get $\proj_{3,4}(\rho_1)\supseteq\sigma_2^*$.
* **#5 `LEMBACenterImplies`**, **#7 `LEMBACenterImplyIntersection`** — 3-line corollaries of #6.
* **#12 `LEMAbsorbingEquality`** — short induction on $|A|$; needs only pp-compatibility of BA.
* **#13 `LEMAbelianEquivalentDefinition`** — genuinely a definitional equivalence.
* **#15 `LEMBACenterSImplyFactor`, #16 `LEMBACenterSOnPowerImplies`** — 12–14 source lines each,
  and both are in the same neighbourhood as what `zhuk-lean` already covers.
* **Core reduction (Zhuk 2021 §5.2)** — ~1.5 pp, elementary, no algebra beyond $\mathrm{Sg}$.
* **The NP-hardness *reduction* itself** (Theorem 5.5's gadget substitution) — clean and finite.

### 4.2 Already done

* **#4 `LEMCenterImpliesTernaryAbsorption`** — `/home/alvaro/claude/zhuk-lean`. Note it is
  **never actually used** in 2404 (0 `\ref`s); it is stated purely as motivation. Its
  *ingredients* (#6, #8, the doubling trick) are what 2404 really needs, and those are
  the parts `zhuk-lean` already has.

### 4.3 Medium (weeks)

* **#6 `LEMBACenterSImplyPPDefinition`** — the BA half is a 10-line argument; the central half is
  Zhuk 2021 Theorem 6.9, resting on Lemmas 6.3–6.8 (≈4 pp) — substantially overlapping
  `zhuk-lean/Central.lean` + `Center.lean`.
* **#8 `LemAbsorptionImpliesEssential`** — covered by `zhuk-lean/Essential.lean` in one direction;
  the ⇐ direction's matrix construction is fiddly but bounded.
* **#9 `LEMBACenterLinkedness`** — 2 pp with the directed-path prerequisite.
* **#7 tree-coverings (`LEMExistenceOfTreeCoverings`, Zhuk 2021 Lemma 5.6)** — only ~26 lines, but
  the proof is an *iterative procedure* ("we iteratively change these tree-coverings"; "since our
  instance is finite and every time we reduce some domain, this procedure will stop eventually").
  Formalizing a well-founded recursion whose invariant is "$\Upsilon_y$ is a tree-covering and
  $\Upsilon_y^{(\top)}(y)=D_y^{(\bot)}$" is real work — call it **hard-in-practice, easy-in-theory**.
* **Inv–Pol hard direction** — ~4 pp, elementary but index-heavy.

### 4.4 Projects in themselves

1. **#11 `LEMLinkedImpliesBACenter` — the Absorption Theorem.** ~10 pp with Zhuk centers,
   central-absorption criteria and the essential doubling trick. Used 5× and, crucially, it is what
   `LEMUbiquity` (existence of a strong subuniverse) reduces to. **Formalize this first after the
   centre theorem** — it is the load-bearing external result.
2. **#14 `LEMAbelianEqualAffineForWNU` — abelian Taylor ⇒ affine.** ~15 pp: modules, polynomial
   equivalence, hereditary absorption-freeness, Taylor+absorption-free ⇒ Mal'cev, abelian Mal'cev ⇒
   affine. Used only *once* in 2404 (SS:1118) — but that one use sits under
   `LEMNiceBridgeGivesAbelianGroup`, which is what makes linear congruences $\mathbb Z_p$-shaped, i.e.
   the entire linear side of the proof. Unavoidable unless you import JACM Cor. 8.17.1 wholesale,
   which itself is unavailable (see #2).
3. **#10 `LEMCentralRelationImplies` + Zhuk 2021 §6.3–§6.8 (Theorem 3.3).** ~18 pp if you need the
   full five-types theorem (you do, for the hardness half via Lemma 4.4).
4. **Cook–Levin / NAE-3-SAT.** ~12 pp of a *completely different* mathematical area, with zero
   Mathlib support. Recommend axiomatising.
5. **The algorithm and its running time.** Not in 2404 at all. Formalizing "runs in polynomial
   time" requires a cost model; Mathlib has none. Recommend restating the tractable half as
   "the constraint language admits a decision procedure of the following recursive shape and it is
   correct", and treating the complexity claim separately (or as an axiom).

---

## 5. Gaps, abuses of notation and ambiguous quantifiers (formalization hazards)

**G1 — `LEMExistenceOfSpesialWNULemma`: unbound $n$, and a suspicious arity.**
The statement reads *"Suppose $w$ is an idempotent WNU operation on $A$. Then there exists a
special idempotent WNU $w'\in\Clo(w)$ of arity $n^{n!}$."* — **$n$ never appears in the
hypotheses.** From the use site (XYSymmetric.tex:400–405: "$f$ of arity $n$ … there exists a special
WNU $w\in\Clo(f)$ of arity $N=n^{n!}$") $n$ must be the arity of $w$. But composing an $n$-ary WNU
with itself $k$ times gives $x\circ_k y=g_x^{k}(y)$ where $g_x(y)=w(x,\dots,x,y)$, and specialness
demands $g_x^{N}$ idempotent, i.e. $N$ at least the index and divisible by the period of $g_x$.
The period can be any integer $\le|A|$, and $n^{n!}$ need not be divisible by it (e.g. $n=3$,
a 5-cycle). Either Maróti–McKenzie Lemma 4.7 supplies extra structure that rules this out, or the
arity should be $n^{m!}$ with $m=|A|$ — in which case the derivation of the $n$-ary XY-symmetric
operation at XYSymmetric.tex:411–418 (which needs the arity to be a power of $n$) must be re-checked.
**This must be resolved against Maróti–McKenzie before the blueprint fixes an arity.**

**G2 — `LEMCentralRelationImplies` silently drops a case.**
Zhuk 2021 Theorem 6.15 has **three** conclusions: (1) $C$ central in $\mathbf A$; (2) $\mathbf B$ has a
nontrivial BA subuniverse; (3) $\mathbf B$ has a nontrivial **projective** subuniverse. 2404 states
only (1) and (2). The elimination of (3) is legitimate under 2404's standing assumption
(main.tex:1123: *"In this paper we assume that every algebra is a finite idempotent algebra having a
WNU term operation"*), because a nontrivial projective subuniverse that is not BA yields an
essentially unary algebra in $\mathrm{HS}(\mathbf A)$ (Zhuk 2021 Lemma 3.4, :1950–1969), which
contradicts Taylor-ness. **But 2404 never says this.** A blueprint must (a) carry the standing
Taylor hypothesis into the statement, and (b) formalize Lemma 3.4 + "Taylor ⟹ no essentially
unary in HS" as an explicit lemma. This is a genuine hidden import.

**G3 — `LEMBACenterSPossibleIntersections` is not literally Zhuk 2021 Lemma 6.25.**
2404 states: *$B<_{T_1}A$, $C<_{T_2}A$, $B\cap C=\varnothing$, $T_1,T_2\in\{\TBA,\TC,\TS\}$ ⟹
$T_1=T_2\in\{\TBA,\TC\}$.* Zhuk 2021 Lemma 6.25 is about types $\{BA(t),C,PC\}$ and concludes
"similar types" (where BA types with *different* terms count as similar). The $\TS$ type
("$C$ contains a subuniverse that is simultaneously BA and central") is **new in 2404** and does
not appear in the source. The derivation is short (if $B<_{\TS}A$ take $D\le B$ with
$D<_{\TBA,\TC}A$ and apply case 2 of 6.25) but it is not written down. Also note 2404 **drops the
term index** from BA types throughout, whereas Zhuk 2021 carefully writes $\le_{BA(t)}$ — the
pp-lemma (Lemma 6.1) genuinely preserves *the same term* $t$, and Theorem 3.7 only concludes
"$T_1,\dots,T_n$ are binary absorbing types", possibly with different terms. **Any Lean encoding
must decide whether `IsBinaryAbsorbing` carries its witness term.** (`zhuk-lean` already made this
choice; check consistency.)

**G4 — "word to word".** `LEMBACenterSOnPowerImplies` (SS:174–179): *"For $T=\TS$ just repeat the
same proof word to word replacing $\TBA$ by $\TS$."* Similarly `LEMBACenterSImplyFactor`
(SS:145–150): *"for $T=\TS$ it is just a combination of the results for $\TBA$ and $\TC$."* In Lean
these are separate obligations; the $\TS$ type is defined by an existential ($\exists D\le C$ that is
both BA and central) so the "same proof" is not literally the same proof — it needs the
witness $D$ to be transported through the construction. Budget explicit lemmas.

**G5 — `ZebsNotes` numbering does not match the on-disk `csp.tex`.**
2404 cites "Theorem 3.11.1", "Lemma 3.11.2 and 3.11.3", "Section 3.15" of arXiv:2210.07383 (2022).
The on-disk `/home/alvaro/claude/zeb/csp.tex` is a later, restructured version whose sectioning does
not produce those numbers. Identification **by content**:
* Theorem 3.11.1 = `\begin{thm}[Absorption Theorem \cite{cyclic}]\label{absorption-theorem}` (csp.tex:10451);
* Lemmas 3.11.2/3.11.3 = the two lemmas used in its proof (csp.tex:10464 and :10488) — these
  correspond exactly to 2404's `LEMBAConLeftOrCenterOnRight` (SS:241), for which 2404 gives its own
  proof, so the import is only for Theorem 3.11.1;
* "Section 3.15" (preimages of BA/central subuniverses under surjective homomorphisms) has **no
  clean single home** in the current csp.tex; the facts are spread over §"Absorption, Jónsson
  absorption and connectivity" and §"Zhuk's centers and ternary absorption". **Flag: this import is
  under-specified and should be restated as an explicit lemma in the blueprint** (it is easy:
  $\lhd$ and $\lhd_Z$ are pp-compatible, and $f^{-1}$ of a pp-definable set is pp-definable).

**G6 — pp-definitions with equality/empty relations.** Zhuk 2021 Theorem 5.5 says *"we also need
the equality and empty relations but they can always be propagated out from the pp-definition of
$R$."* This is a normalization lemma about pp-formulas that is nowhere proved. Small but real.

**G7 — `CORPropagationModuloCongruence` is never proved** (see §1.4). Six uses.

**G8 — Informal Claim 1 has no formal statement** (see §3.1). The algorithm's correctness argument
in main.tex:593–780 leans on it, and the paper's formal section
(`\subsection{Statements sufficient to prove that Zhuk's algorithm works}`) omits it. Anyone
building a blueprint must write it, and must supply the missing step
"no BA/C/PC subuniverse on $D_x$ ⟹ there is a linear congruence $\sigma$ with $\sigma^*=D_x^2$,
hence $D_x/\sigma\cong\mathbb Z_p$" — assembling `LEMUbiquity` (main.tex:1653) with
`LEMLInearOnTheTopIsEasy` (main.tex:1454). Also note the algorithm text (main.tex:610) asserts
$D_{x_i}/\sigma_{x_i}\cong\mathbb Z_{q_1}\times\dots\times\mathbb Z_{q_{n_i}}$ (a **product**),
while Informal Claim 1 (main.tex:523) says $D_x/\sigma\cong\mathbb Z_p$ (a single factor). The
reconciliation (take $\sigma$ minimal = the intersection of all such congruences, and use
`THMCodimensionOneTheorem` condition 4) is left implicit.

**G9 — Emptiness / strictness conventions.** 2404 is careful ("Suppose $\varnothing\neq C\lneq B\le A$.
We write $C<_T^A B$ …"; dotted $\dot\lll$, $\dot\le_T$ allow $\varnothing$). Zhuk 2021 uses
$\le_T$ which allows $B=A$ and $B=\varnothing$ (e.g. "a PC subuniverse … is $A$, or empty, or a block").
Every import therefore needs an explicit nonemptiness/properness translation. In particular Zhuk
2021 Theorem 6.15's conclusion "(1) $C$ is a central subuniverse of $A$" is used in 2404 only after
separately establishing $C\neq\varnothing$ (`LEMBAConLeftOrCenterOnRight`, SS:252–266). This is
exactly the kind of mismatch that silently breaks a port.

**G10 — `\mathcal V_n` is not a variety** (main.tex:1114) yet is used like one, and $\mathbf Z_p$ is
declared to "belong to $\mathcal V_n$ for a fixed $n$, hence the algebra $\mathbf Z_p$ is uniquely
defined" (main.tex:1119–1121) — i.e. $p$ and $n$ are silently constrained ($x_1+\dots+x_n \bmod p$
must be idempotent, so $n\equiv1 \pmod p$). That constraint is never stated. Formalizing
$\mathbf Z_p\in\mathcal V_n$ requires it.

---

## 6. Recommended import policy for the blueprint

1. **Route the tractable half through the Absorption Theorem, not through Zhuk 2021 §6.3–§6.8.**
   2404's `LEMUbiquity` already does this. It removes ~15 pp (projective subuniverses, PC
   subuniverses via Rosenberg, full-projective relations, Lemmas 6.26–6.33) from the tractable half.
2. **Replace JACM Cor. 8.17.1 with the abelian route** (`LemBridgeEquivalentToAbelianness` +
   `LEMNiceBridgeGivesAbelianGroup` + abelian-Taylor⇒affine), because Cor. 8.17.1's proof depends on
   a paper we do not have. This makes "abelian Taylor ⇒ affine" a first-class blueprint chapter.
3. **Reuse `zhuk-lean`** for the absorption/centre layer: `Absorbs`, `Essential`, `Central`,
   `Center`, `Doubling`, `StarPower` cover imports #4, #6 (central half), #8, and much of #15/#16.
4. **Axiomatise (or hypothesise) NP-hardness of $\mathrm{CSP}(\{NAE_3\})$ and the polynomial-time cost
   model**; prove the *reduction* and the algebra, not Cook–Levin.
5. **Write explicit blueprint statements for the six things 2404 leaves implicit**: G2 (the Taylor
   hypothesis eliminating projective subuniverses), G3 (the $\TS$ case of disjoint strong
   subuniverses), G5 (preimage lemma for BA/central), G6 (pp normalization), G7
   (`CORPropagationModuloCongruence`), G8 (Informal Claim 1 and the $\mathbb Z_p$ vs product
   reconciliation).
6. **Resolve G1 (the arity $n^{n!}$) against Maróti–McKenzie before committing to a definition of
   $\mathcal V_n$.** Getting the special-WNU arity wrong poisons the whole of Section 4
   (XY-symmetric), which threads $N=n^{n!}$ through every construction.

---

## Appendix A — every `\cite` in the source, classified

**Load-bearing (inside/before a statement, or inside a proof):** 21 sites — items #1–#17 above,
plus `LEMBridgeBetweenCongruences` (proved), plus the two "see Lemma 6.8/6.24" in-proof cites,
plus the Galois-connection remark at main.tex:2167.

**Contextual only (no mathematical load):** `FederVardi` (:401), the four dichotomy-proof cites
(:403, :423, :509, :594, :1040, :1452), `bergman2011universal` (:1094, standard universal algebra),
`istinger1979characterization` + `lausch2000algebra` (:1108, definition of PC algebras),
`agnes` (:1212, parallelogram property remark), `RossSlides` (:1275, bridges vs. centralizers),
`barto2017absorption` (:1342), `minimaltayloralgebras` (:1361, :1056), `kozik2016weak` +
`brady2022notes` (:2086, other consistency notions), `jankovec2023minimalni` (:840),
`borovs2023symmetric` (:1008), `brakensiek2020power`/`ciardo2023clap`/`barto2021algebraic`/
`krokhin2022invitation` (:936–:960, PCSP motivation), `freese1987commutator` (commented out),
`geiger1968closed`/`bond1`/`bond2` (:2167, easy direction only),
`MarotiMcKenzie`/`barto2012absorbing`/`kearnes2014optimal`/`siggers2010strong`/`bulatov2001algebraic`
(:802–:810, attributions inside `corTaylorEquivalentConditions`, which is stated **without proof**
as a "known characterization" — note this corollary is itself an unproved import chain of four
classical theorems, though it is never used).

## Appendix B — files and line anchors

* Zhuk 2404 source: `/tmp/.../scratchpad/papers/src2404/{main.tex,StrongSubalgebras.tex,XYSymmetric.tex,necessaryClaims.tex,refs.bib}`
* Zhuk JACM: `/tmp/.../scratchpad/papers/1704.01914.txt` — Lemma 6.1 :1225; Lemma 6.3 :1370;
  Lemma 7.2 :1446; Lemma 7.21 :1891; Theorem 8.15 :2521 (⚑ from [62], not on disk);
  Lemma 8.16 :2525; Theorem 8.17 :2528; Cor 8.17.1 :2596; Lemma 8.19 :2731.
* Zhuk 2021 (strong subalgebras): `/tmp/.../scratchpad/papers/2005.00593.txt` — §3 statements :262;
  §4 WNU existence :386; §5 CSP :746; §5.3 hardness :823; Lemma 5.6 :911; §6 :1335; Lemma 6.1 :1359;
  Lemma 3.2 :1409; Lemma 6.7 :1483; Lemma 6.8 :1497; Theorem 6.9 :1523; Cor 6.11.1 :1591;
  Theorem 6.15 :1673; Lemma 6.24 :1937; Lemma 6.25 :1993; Theorem 3.3 (proof) :2226.
* Minimal Taylor algebras: `/tmp/.../scratchpad/papers/2104.11808.txt` — Four Types Theorem 3.7 :661;
  Prop 4.3/4.4 (centers are 3-absorbing) :736/:744; Cor 4.5 :752.
* Brady's notes: `/home/alvaro/claude/zeb/csp.tex` — NP crash course :701; Inv–Pol :1193;
  abelian Mal'cev ⇒ affine :4235; Jónsson absorption/connectivity :8540; `absorbing-linked` :8697;
  Zhuk centers :10128; `zhuk-center` :10257; `bin-central-criterion` :10413;
  Absorption Theorem :10451; abelian Taylor ⇒ affine :10670.
* Existing Lean: `/home/alvaro/claude/zhuk-lean/ZhukLean/*.lean` (1 670 lines);
  blueprint `/home/alvaro/claude/zeb/zhuk_centers.tex` (1 830 lines).
