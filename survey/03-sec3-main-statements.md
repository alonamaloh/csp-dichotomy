# Zhuk 2404.01080v2 — Deep read of §3.3 "Main Statements" and §3.4 "Statements sufficient to prove that Zhuk's algorithm works"

Source: `/tmp/claude-1000/-home-alvaro-claude-zeb/b3d460d7-227a-4a0c-983d-31fbf26d8692/scratchpad/papers/src2404/main.tex`,
lines 3407–4122 (plus the §3.1 definitions L1969–2229 and §3.2 auxiliary statements L2230–3405 that they consume).
Rendered numbering (from `zhuk2404.txt`):

| label | number in PDF | location |
|---|---|---|
| `THMMainInductiveCSPClaim` | **Theorem 41** | main.tex L3408–3858 |
| `THMPCDoesnotKillAllSolutions` | **Theorem 42** | main.tex L3860–3976 |
| `THMCSPDReductionsAreSafe` | **Theorem 43** | main.tex L3985–4002 |
| `THMCodimensionOneTheorem` | **Theorem 44** | main.tex L4004–4121 |
| `LEMFindOneConsistentForAll` | **Lemma 37** | main.tex L2457–2506 (§3.2) |
| `LEMGetABridgeFromSubdirectPCLinearInstance` | **Lemma 39** | main.tex L2856–3038 (§3.2) |
| `CORSameTypeReductionAndConstraint` | **Corollary 40** | main.tex L3385–3405 (§3.2) |

§3.3 contains **exactly two** statements (Thm 41, Thm 42); §3.4 contains **exactly two** (Thm 43, Thm 44).
Neither subsection uses anything from §4 (XY-symmetric operations). Everything they use comes from
§2 (strong/linear subuniverses), §3.1 (definitions) and §3.2 (auxiliary statements), plus six imported
results from `[33] = zhuk2020proof` (arXiv 1704.01914 / JACM) and `[34] = zhuk2021strong` (arXiv 2005.00593).

---

## 0. Notation you must have loaded to read these statements

Everything below is *needed verbatim* to state Theorems 41–44; a formalization must define all of it.

**Algebras.** All domains are algebras $\mathbf D_x = (D_x; w^{\mathbf D_x}) \in \mathcal V_n$: finite, one basic
operation, an **idempotent special WNU** of arity $n$ (special: $w(x,\dots,x,y)=w(x,\dots,x,w(x,\dots,x,y))$).
$\mathbf Z_p$ = $(\{0,\dots,p-1\}; x_1+\dots+x_n \bmod p)$, which is in $\mathcal V_n$ for the fixed $n$
(so $p \mid n-1$ implicitly).

**Subuniverse types** (L1504–1563). For $\varnothing\neq C\subsetneq B\le A$:
- $C<^A_{\mathrm{BA}}B$: $C$ is a binary absorbing subuniverse of $\mathbf B$.
- $C<^A_{\mathrm C}B$: $C$ is a central subuniverse of $\mathbf B$ (absorbing + $\forall a\in B\setminus C:(a,a)\notin\mathrm{Sg}_{\mathbf B}((\{a\}\times C)\cup(C\times\{a\}))$).
- $C<^A_{\mathrm D}B$: there is an **irreducible congruence** $\sigma$ **on $\mathbf A$** with (i) $B^2\subseteq\sigma^*$, (ii) $C=B\cap E$ for some block $E$ of $\sigma$, (iii) $\mathbf B/\sigma$ is BA- and center-free.
- $C<^A_{\mathrm L}B$ / $C<^A_{\mathrm{PC}}B$: as $<_{\mathrm D}$ with $\sigma$ linear / PC.
- $C<^A_{\mathrm S}B$: some $D\subseteq C$ is simultaneously BA and central in $\mathbf B$.
- $C<^A_{T(\sigma)}B$ names the witnessing congruence. $C\le_{T}B$ means $C=B$ or $C<_TB$.
- **$C\lll^A B$**: there is a chain $C=B_m<^A_{T_m}\dots<^A_{T_1}B_0=B$ with $T_i\in\{\mathrm{BA},\mathrm C,\mathrm S,\mathrm D\}$; $m=0$ allowed, so $\lll$ is reflexive and transitive. $B\lll A$ abbreviates $B\lll^A A$. **$\varnothing\lll A$ never holds** — so $\lll$ silently carries nonemptiness.
- **$C<^A_{\mathcal MT}B$** ($T\in\{\mathrm L,\mathrm{PC},\mathrm D\}$): $C\neq\varnothing$ and $C=C_1\cap\dots\cap C_t$ with each $C_i<^A_TB$.
- **S-free**: $\mathbf A$ has no $C<_{\mathrm S}\mathbf A$, i.e. no subuniverse that is BA *and* central simultaneously.

**Congruence types.** $\sigma$ is *irreducible* if $0_{\mathbf A/\sigma}$ is not an intersection of nonzero
subalgebras of $(\mathbf A/\sigma)^2$; $\sigma^*$ = the minimal $\delta\le\mathbf A^2$ with $\delta\supsetneq\sigma$
stable under $\sigma$. $\sigma$ is *linear* if irreducible, $\sigma^*$ is a congruence, and there is
$S\le(\sigma^*)^{[4]}$ making every block $B$ of $\sigma^*$ satisfy $(B/\sigma;S\cap(B/\sigma)^4)\cong(\mathbb Z_p^m;x_1-x_2=x_3-x_4)$;
*PC* if irreducible and not linear. $\sigma$ is a **perfect linear congruence** if irreducible and there is
$\zeta\le\mathbf A\times\mathbf A\times\mathbf Z_p$ with $\mathrm{proj}_{1,2}\zeta=\sigma^*$ and
$(a_1,a_2,b)\in\zeta\Rightarrow((a_1,a_2)\in\sigma\Leftrightarrow b=0)$.

**Bridges.** $\delta\le\mathbf D_1^2\times\mathbf D_2^2$ is a *bridge* from $\sigma_1$ to $\sigma_2$ if the
first two coordinates are stable under $\sigma_1$, the last two under $\sigma_2$,
$\mathrm{proj}_{1,2}\delta\supsetneq\sigma_1$, $\mathrm{proj}_{3,4}\delta\supsetneq\sigma_2$, and
$(a_1,a_2,a_3,a_4)\in\delta\Rightarrow((a_1,a_2)\in\sigma_1\Leftrightarrow(a_3,a_4)\in\sigma_2)$.
$\widetilde\delta(x,y):=\delta(x,x,y,y)$. Reflexive bridge: contains $(a,a,a,a)$ for all $a$.
Two congruences on the same $\mathbf D_x$ are **adjacent** if joined by a reflexive bridge.

**CSP-side notions** (§3.1, L1969–2229):
- **Reduction** $D^{(\top)}$: assigns a subuniverse $D_x^{(\top)}\le\mathbf D_x$ to each variable (possibly empty). $\mathcal I^{(\top)}$ = $\mathcal I$ with domains restricted. $D^{(\bot)}\lll D^{(\top)}$ / $\le_TD^{(\top)}$ mean componentwise.
- **$\mathrm{Con}(R,i)$** = $\exists\bar x\,R(\dots,y,\dots)\wedge R(\dots,y',\dots)$ (the "induced congruence"); $\mathrm{Con}(C,x_i)$ likewise; $\mathrm{Congruences}(\mathcal I,x)=\{\mathrm{Con}(C,x):C\in\mathcal I\}$.
- **PC/Linear type of a relation**: $R$ rectangular **and every** $\mathrm{Con}(R,i)$ a PC / linear congruence. Instance of that type: all constraints are.
- **1-consistent**: $\mathrm{proj}_z(C)=D_z$ for every constraint and every variable of it. **Cycle-consistent**: 1-consistent and every path from $z$ to $z$ connects $a$ to $a$, for every $z,a\in D_z$.
- **Linked**: for every $z$ and $a,b\in D_z$ a path $z\to z$ connects $a$ and $b$. **Fragmented**: $\mathrm{Var}$ splits into two nonempty parts with no constraint straddling. **Irreducible**: there is no $\mathcal I'$ with $\mathrm{Var}(\mathcal I')\subseteq\mathrm{Var}(\mathcal I)$, all constraints projections of constraints of $\mathcal I$, not fragmented, not linked, and with non-subdirect solution set.
- **Solution set subdirect**: for every $x$ and every $a\in D_x$ (the **full** domain, *not* $D_x^{(\top)}$) the instance has a solution with $x=a$.
- **Weakening**: $C_1$ weaker-or-equivalent to $C_2$ iff $\mathrm{Var}(C_1)\subseteq\mathrm{Var}(C_2)$ and $C_2\Rightarrow C_1$; strictly weaker if additionally $C_1\not\Rightarrow C_2$. *The weakening of $C$ in $\mathcal I$* replaces $C$ by **all** strictly weaker constraints (Remark 2 adds: only those $R$ that are subuniverses of the product, and without dummy variables).
- **Crucial**: $C\in\mathcal I$ is crucial in $D^{(\top)}$ if $C$ has no dummy variables, $\mathcal I^{(\top)}$ has no solutions, and weakening $C$ yields an instance with a solution in $D^{(\top)}$. $\mathcal I$ is crucial in $D^{(\top)}$ if it has $\ge1$ constraint and all of them are crucial.
- **$\mathcal I(x_1,\dots,x_n)$** = the relation of tuples extendable to a solution.
- **Expanded covering** $\mathcal I'\in\mathrm{Expanded}(\mathcal I)$: a map $S:\mathrm{Var}(\mathcal I')\to\mathrm{Var}(\mathcal I)$ with $S(x)=x$ on shared variables, $D_x=D_{S(x)}$, and for each constraint $R(x_1,\dots,x_n)$ of $\mathcal I'$ either the $S(x_i)$ are pairwise distinct and $R(S(x_1),\dots,S(x_n))$ is weaker-or-equivalent to a constraint of $\mathcal I$, or all $S(x_i)$ coincide and $R$ is reflexive. *Covering*: the projected constraint is literally in $\mathcal I$. *Tree-covering*: a covering that is a tree-instance. Facts (p1)–(p8) at L2195–2212; in particular **(p2) every weakening is an expanded covering**, **(p4) a tree-covering of a 1-consistent instance has subdirect solution set**, **(p7) expanded coverings of cycle-consistent irreducible instances are cycle-consistent and irreducible** (= Lemma 30 = [33, Lemma 6.1]), **(p8) reductions extend to coverings, preserving 1-consistency**.
- **Connected instance**: all constraints rectangular, all congruences in $\mathrm{Congruences}(\mathcal I)$ irreducible, and the graph on constraints with edges = adjacency (in a shared variable) is connected.

---

## 1. Statement-by-statement, with all numbered hypotheses

### 1.1 Theorem 41 = `THMMainInductiveCSPClaim` (the summit)

> **Theorem 41.** Suppose
> - $D^{(1)}$ is a 1-consistent reduction of an irreducible, cycle-consistent instance $\mathcal I$;
> - $D^{(1)}\lll D$.
>
> **If $\mathcal I$ is crucial in $D^{(1)}$** then **(1a)** and **((1b) or (1c))**:
> - **(1a)** every constraint of $\mathcal I$ has the parallelogram property;
> - **(1b)** $\mathcal I$ is a connected linear-type instance having a subdirect solution set;
> - **(1c)** there exists an expanded covering $\mathcal J$ of $\mathcal I$ with a **linked connected** subinstance $\Upsilon$ such that the solution set of $\Upsilon$ is **not** subdirect and $\mathcal J$ is crucial in $D^{(1)}$.
>
> **If $D^{(2)}\le_{\mathcal T}D^{(1)}$ is a 1-consistent reduction of $\mathcal I$, where $\mathcal T\in\{\mathrm{BA},\mathrm C\}$, and $\mathcal I^{(1)}$ has a solution**, then
> - **(2)** $\mathcal I^{(2)}$ has a solution.

Structural remarks that matter for formalization:

1. This is **two theorems sharing a hypothesis block** (call them **(A)** and **(B)**), proved by one
   induction. **(B) does not assume cruciality.** **(A) does not assume $\mathcal I^{(1)}$ has a solution**
   (indeed cruciality says it has none).
2. (1a) and (1b) are *reduction-free* statements about $\mathcal I$; **(1c) mentions $D^{(1)}$**. This
   asymmetry is the source of the only genuinely missing step in the proof (see §5, H2).
3. "$D^{(1)}\lll D$" silently forces $D^{(1)}$ nonempty at every variable.
4. "linear-type instance" in (1b) means: every constraint is rectangular and *all* of its induced
   congruences $\mathrm{Con}(C,x)$ are linear.
5. $\mathcal T$ is a *single* type shared by all coordinates in "$D^{(2)}\le_{\mathcal T}D^{(1)}$"
   (the componentwise definition at L2001–2004 fixes one $T$ for all $i$).

### 1.2 Theorem 42 = `THMPCDoesnotKillAllSolutions`

> **Theorem 42.** Suppose $\mathcal I$ is a cycle-consistent irreducible instance,
> $B<^{D_y}_{\mathrm{PC}(\sigma)}D_y$ for some $y\in\mathrm{Var}(\mathcal I)$, and $\mathcal I$ has a solution.
> Then $\mathcal I$ has a solution with $y\in B$.

Note the reduction is *from the full domain* $D_y$ (so $\sigma^*=D_y^2$ and $\mathbf D_y/\sigma$ is
BA- and center-free by the definition of $<_{\mathrm D}$).

### 1.3 Theorem 43 = `THMCSPDReductionsAreSafe`

> **Theorem 43.** Suppose $\Theta$ is a cycle-consistent irreducible CSP instance, and
> $B<^{D_x}_TD_x$ where $T\in\{\mathrm{BA},\mathrm C,\mathrm{PC}\}$.
> Then $\Theta$ has a solution **if and only if** $\Theta$ has a solution with $x\in B$.

(The "if" direction is trivial; the content is "only if".)

### 1.4 Theorem 44 = `THMCodimensionOneTheorem`

> **Theorem 44.** Suppose:
> 1. $\mathcal I$ is a **linked** cycle-consistent irreducible CSP instance with $\mathrm{Var}(\mathcal I)=\{x_1,\dots,x_n\}$;
> 2. $D_{x_i}$ is **S-free** for every $i\in[n]$;
> 3. if we weaken **all** the constraints of $\Theta$, we get an instance whose solution set is subdirect;
> 4. $\sigma_{x_i}$ is the intersection of all the **linear congruences** $\sigma$ on $D_{x_i}$ such that $\sigma^*=D_{x_i}\times D_{x_i}$;
> 5. $L_{x_i}=D_{x_i}/\sigma_{x_i}$ for every $i\in[n]$;
> 6. $\phi:\mathbf Z_{q_1}\times\dots\times\mathbf Z_{q_k}\to L_{x_1}\times\dots\times L_{x_n}$ is a homomorphism, $q_1,\dots,q_k$ prime;
> 7. if we weaken **any** constraint of $\mathcal I$ then for every $(a_1,\dots,a_k)\in\mathbf Z_{q_1}\times\dots\times\mathbf Z_{q_k}$ there exists a solution of the obtained instance in $\phi(a_1,\dots,a_k)$.
>
> Then $\Delta:=\{(a_1,\dots,a_k)\mid \Theta \text{ has a solution in }\phi(a_1,\dots,a_k)\}$ is
> **either empty, or full, or an affine subspace of $\mathbf Z_{q_1}\times\dots\times\mathbf Z_{q_k}$ of codimension 1**
> (the solution set of a single linear equation).

`$\Theta$` in conditions 3 and in the conclusion is the same object as `$\mathcal I$`: a leftover from an
earlier draft (see §5, H18). "$\Theta$ has a solution in $\phi(a)$" means: read the tuple of
$\sigma_{x_i}$-blocks $\phi(a)$ as a reduction and ask for a solution inside it.

### 1.5 Lemma 37 = `LEMFindOneConsistentForAll` (§3.2, requested explicitly)

> **Lemma 37.** Suppose $D^{(1)}$ is a 1-consistent reduction of a **cycle-consistent** instance $\mathcal I$,
> $D^{(1)}\lll D$, $B<^{D_x}_TD^{(1)}_x$ for some variable $x$, and $T\in\{\mathrm{BA},\mathrm C,\mathrm{PC}\}$.
> Then there exists a **nonempty** 1-consistent reduction $D^{(2)}\lll D^{(1)}$ such that $D_x^{(2)}\le B$. Moreover
> 1. if $T\in\{\mathrm{BA},\mathrm C\}$ then $D^{(2)}\le_TD^{(1)}$;
> 2. if $T=\mathrm{PC}$ and $D_y^{(1)}$ is S-free for every $y$, then $D^{(2)}\le_{\mathcal M\mathrm{PC}}D^{(1)}$.
>
> *Proof.* Put $D^{(\top)}_x=B$, $D^{(\top)}_y=D^{(1)}_y$ otherwise, and let $D^{(2)}$ be the inclusion-maximal
> 1-consistent reduction $\le D^{(\top)}$. Lemma 35 gives tree-coverings $\Upsilon_y$ with
> $\Upsilon_y^{(\top)}(y)=D_y^{(2)}$. If some $D_y^{(2)}=\varnothing$, then $\Upsilon_y^{(\top)}$ has no
> solutions; its solution set is subdirect (1-consistency of $\mathcal I$), so Corollary 22 forces **two**
> children of $x$ to be restricted — impossible for a tree-covering of a cycle-consistent instance. Hence
> $D^{(2)}$ is nonempty; the "moreover" parts follow from Lemma 19 (BA/C) resp. Corollary 18(rm) (PC),
> applied to the solution set of $\Upsilon_y$.

**This lemma is the workhorse**: it is the only route from "a strong subuniverse exists somewhere" to
"a *global*, 1-consistent, strong reduction exists". It is invoked in Thm 41 (Case 1 and the
$\mathcal B_0=\varnothing$ case), Thm 42 and Thm 43.

### 1.6 The other §3.2 statements consumed by §3.3–3.4

| # | label | statement (compressed) | used in |
|---|---|---|---|
| 30 | `LEMExpandedConsistencyLemma` | $\mathcal I$ cycle-consistent irreducible, $\mathcal I'\in\mathrm{Expanded}(\mathcal I)$ $\Rightarrow$ $\mathcal I'$ cycle-consistent irreducible. **[33, Lemma 6.1] — external** | everywhere (implicitly, via (p7)) |
| 31 | `LEMMinimalPCLinearReductionIsConsistent` | $D^{(1)}$ 1-consistent for $\mathcal I$, each $D_x^{(1)}$ S-free, $T\in\{\mathrm{PC},\mathrm L,\mathrm D\}$, $D^{(1)}\lll D$, each $D_x^{(2)}\le_{\mathcal MT}D_x^{(1)}$ a **minimal** $\mathcal MT$-subuniverse $\Rightarrow$ either some $C^{(2)}=\varnothing$, or $\mathcal I^{(2)}$ is 1-consistent | Thm 41 Case 2; Thm 44 |
| 32 | `LEMCrucialMeansIrreducible` | $R(\bar x)$ rectangular constraint of a 1-consistent instance, crucial in $D^{(\top)}$ $\Rightarrow$ every $\mathrm{Con}(R,i)$ is an irreducible congruence | inside Lemma 38; needed (implicitly) for "connected" |
| 33 | `LEMBridgeFromRelation` | $R\le_{sd}\prod\mathbf A_i$, first and last variables rectangular, a "parallelogram failure" between coordinates 1 and $n$ $\Rightarrow$ a bridge from $\mathrm{Con}(R,1)$ to $\mathrm{Con}(R,n)$ with $\widetilde\delta=\mathrm{proj}_{1,n}(R)$ | inside Lemma 34 |
| 34 | `LEMConnectedProperties` | $\mathcal I$ cycle-consistent **connected** $\Rightarrow$ (a) any two constraints with a common variable are adjacent; (b) for any path from $x_1\in\mathrm{Var}(C_1)$ to $x_2\in\mathrm{Var}(C_2)$ there is a bridge $\mathrm{Con}(C_1,x_1)\to\mathrm{Con}(C_2,x_2)$ with $\widetilde\delta\supseteq$ all pairs connected by the path; **(p)** if $\mathcal I$ is also **linked** then every $\mathrm{Con}(C,x)$ is a **perfect linear congruence** | Thm 41 (2)(1c); Thm 42 (1c); Thm 44 |
| 35 | `LEMExistenceOfTreeCoverings` | $D^{(\bot)}$ inclusion-maximal 1-consistent reduction $\le D^{(\top)}$ $\Rightarrow$ for every $y$ there is a tree-covering $\Upsilon_y$ with $\Upsilon_y^{(\top)}(y)=D_y^{(\bot)}$. **[34, Lemma 5.6] — external** | Lemma 37, Thm 41 Case 2, Thm 42 |
| 36 | `CORExistenceOfTreeCoverings` | same setting, $D^{(\top)}\lll D$, $D^{(\bot)}$ nonempty $\Rightarrow D^{(\bot)}\lll^DD^{(\top)}\lll D$ | supplies "$\lll D$" for $D^{(B,\bot)}$ |
| 38 | `LEMParalPropertyFromCrucialInMultiType` | $D^{(1)}$ 1-consistent for the single constraint $R(x_1,\dots,x_n)$, $T\in\{\mathrm L,\mathrm{PC},\mathrm D\}$, $D^{(2)}\le_{\mathcal MT}^DD^{(1)}\lll D$, $R$ crucial **as the whole instance** in $D^{(2)}$ $\Rightarrow$ $R$ has the parallelogram property, and each $\mathrm{Con}(R,i)$ is a congruence of type $T$ with $\mathrm{Con}(R,i)^*\supseteq(D_{x_i}^{(1)})^2$; moreover if $T=\mathrm{PC}$ then $n=2$ | Thm 41 Case 2 Subcase 2; Thm 44 Case 1 |
| 39 | `LEMGetABridgeFromSubdirectPCLinearInstance` | see below | the central §3.2 tool |
| 40 | `CORSameTypeReductionAndConstraint` | $\mathcal I$ has subdirect solution set, $\mathcal I^{(1)}$ has a solution, $D^{(2)}\le_T^DD^{(1)}\lll D$ with $T\in\{\mathrm{BA},\mathrm C,\mathrm S\}$, $C\in\mathcal I$ of **linear** type $\Rightarrow$ $C$ is **not** crucial in $D^{(2)}$ | Thm 41 part (2), case (1b) |

> **Lemma 39.** Suppose (1) $\mathcal I$ has a **subdirect solution set**; (2) $D^{(1)}$ is a reduction with
> $D_x^{(1)}\lll D_x$ for every $x$; (3) $C\in\mathcal I$ is a constraint of type $T\in\{\mathrm{PC},\mathrm L\}$;
> (4) $B<^{D_z}_{\mathcal T(\xi)}D_z^{(1)}$ for some variable $z$, $\mathcal T\in\{\mathrm{BA},\mathrm C,\mathrm S,\mathrm{PC},\mathrm L\}$;
> (5) if $T=\mathrm{PC}$ then $\mathcal T\in\{\mathrm{PC},\mathrm L\}$; (6) $\mathcal I^{(1)}$ has a solution;
> (7) $\mathcal I^{(1)}$ has no solutions with $z\in B$; (8) weakening $C$ in $\mathcal I$ gives an instance with
> a solution in $D^{(1)}$ and $z\in B$.
> **Then $\mathcal T=T$**, and for any variable $x$ of $C$ there is a bridge $\delta$ from $\xi$ to
> $\mathrm{Con}(C,x)$ with $\widetilde\delta\supseteq\mathcal I(z,x)$.

This is the "bridges appear naturally from strong/linear subuniverses" mechanism advertised in the
introduction (L494–501): a *failure of a reduction* is converted into a *bridge*. Almost every
connectivity argument in Thm 41 goes through it.

§2 statements consumed (directly by §3.3–3.4): **Lemma 13** (Ubiquity), **Lemma 19** ([34]; BA/central
propagation through relations), **Lemma 23** (`LEMMultiTypeStillStable`: $C\le_{\mathcal MT}^AB\Rightarrow C\lll^AB$),
**Corollary 22** (`CORMainStableIntersection`), **Lemma 11** (`LEMLInearOnTheTopIsEasy`), **Lemma 29**
(`LEMNoAbsCenterPCInLinearAlgebra`: no BA/central subuniverse inside a power of $\mathbf Z_p$),
**Lemma 8** (no bridge between linear and non-linear congruences), and — via §3.2 — Lemmas 14–18, 24, 25, 27, 28.

---

## 2. Proof digests

Legend for the flags: **[§2]** invokes a §2 property; **[§3.2]** invokes a §3.2 lemma; **[ext]** invokes an
external result; **[IH]** invokes the induction hypothesis; **[same-level]** invokes part (2) of Thm 41 at
the *same* value of the induction measure; **⚠** gap / implicit step / ambiguity (cross-referenced to §5).

### 2.1 Theorem 41, part **(2)** (proved first)

Assume for contradiction $\mathcal I^{(2)}$ has no solutions.

1. Weaken $\mathcal I$ (the text says "weaken $\mathcal I^{(2)}$" ⚠H1) until it is crucial in $D^{(2)}$; call it $\mathcal I'$. Legitimate by Remark 2; terminates ⚠H5.
2. **[IH]** applied to $(\mathcal I',D^{(2)})$: $\mathcal I'$ satisfies (1a) and (1b) or (1c).
   *Side conditions silently re-established*: $\mathcal I'$ is a weakening, hence an expanded covering (p2), hence cycle-consistent and irreducible **[ext, Lemma 30]**; $D^{(2)}$ is 1-consistent for $\mathcal I'$ (weakenings preserve 1-consistency ⚠H29); $D^{(2)}\lll D$ from $D^{(2)}\le_{\mathcal T}D^{(1)}\lll D$; the measure drops ⚠H4.
3. **Case (1c) for $\mathcal I'$.** Get $\mathcal J\in\mathrm{Expanded}(\mathcal I')$, crucial in $D^{(2)}$, with a linked connected subinstance $\Upsilon$.
   - Pick $C\in\Upsilon$, $x\in\mathrm{Var}(C)$. **[§3.2, Lemma 34(p)]**: $\mathrm{Con}(C,x)$ is a *perfect linear congruence*. (Requires $\Upsilon$ cycle-consistent: inherited from $\mathcal J$ by taking a subinstance ⚠H29.)
   - Take the witnessing $\zeta\subseteq\mathbf D_x\times\mathbf D_x\times\mathbf Z_p$ ($(y_1,y_2,0)\in\zeta\Leftrightarrow(y_1,y_2)\in\mathrm{Con}(C,x)$, $\mathrm{proj}_{1,2}\zeta=\mathrm{Con}(C,x)^*$).
   - Build $\Theta$: in $\mathcal J$, rename the occurrence of $x$ in $C$ to $x'$, add $\zeta(x,x',z)$ with a **new** variable $z$ over $\mathbf Z_p$. Extend both reductions by $D^{(1)}_{x'}=D^{(2)}_{x'}=D_{x'}=D_x$ (and, implicitly, $D^{(1)}_z=D^{(2)}_z=\mathbf Z_p$).
   - $E_i:=\{$values of $z$ realized by solutions of $\Theta^{(i)}\}$. **[§2, Lemma 19]** gives $E_2\le_{\mathcal T}E_1$ ⚠H27.
   - $\Theta^{(2)}$ has a solution (weakening $C$ modulo $\mathrm{Con}(C,x)^*$ is *one of* the weakenings guaranteed by cruciality of $\mathcal J$ in $D^{(2)}$), but none with $z=0$ (that would be a solution of $\mathcal J^{(2)}$, using rectangularity of $C$ at $x$).
   - $\mathcal I^{(1)}$ has a solution $\Rightarrow$ $\mathcal J^{(1)}$ has one (p3) $\Rightarrow$ $\Theta^{(1)}$ has one with $z=0$.
   - So $0\in E_1$, $\varnothing\ne E_2\subseteq E_1\setminus\{0\}$, hence $|E_1|\ge2$; since $\mathbf Z_p$ has no proper subalgebra of size $>1$ ⚠H28, $E_1=\mathbf Z_p$; then $E_2<_{\mathcal T}\mathbf Z_p$ contradicts **[§2, Lemma 29]**.
4. **Case (1b) for $\mathcal I'$.** $\mathcal I'$ is a connected *linear-type* instance with subdirect solution set; $\mathcal I'^{(1)}$ has a solution; $D^{(2)}\le_{\mathcal T}D^{(1)}\lll D$ with $\mathcal T\in\{\mathrm{BA},\mathrm C\}$; every constraint of $\mathcal I'$ is crucial in $D^{(2)}$ and of linear type. **[§3.2, Corollary 40]** says a linear-type constraint cannot be crucial. Contradiction.

### 2.2 Theorem 41, part **(1)**: preamble

Some $|D_x^{(1)}|>1$: otherwise 1-consistency of $\mathcal I^{(1)}$ with singleton nonempty domains would
produce a solution, contradicting cruciality. (Nonemptiness comes from $D^{(1)}\lll D$.)

**Case 1: some $D_x^{(1)}$ has a nontrivial BA or central subuniverse.**

1. **[§3.2, Lemma 37]** gives a 1-consistent $D^{(2)}\le_TD^{(1)}$, $T\in\{\mathrm{BA},\mathrm C\}$, with $D_x^{(2)}\subseteq B\subsetneq D_x^{(1)}$.
2. $\mathcal I$ is crucial in $D^{(2)}$: for a one-constraint weakening $\mathcal J$ of $\mathcal I$, $\mathcal J^{(1)}$ has a solution, and **[same-level]** part (2) applied to $(\mathcal J,D^{(1)},D^{(2)})$ gives a solution of $\mathcal J^{(2)}$. ⚠H3 (the paper calls this "the inductive assumption", but the measure has *not* decreased — this is part (2) at the same level). $\mathcal I^{(2)}\subseteq\mathcal I^{(1)}$ has no solutions.
3. **[IH]** applied to $(\mathcal I,D^{(2)})$ yields (1a) and ((1b) or (1c)) **relative to $D^{(2)}$**. (1a),(1b) are reduction-free so they transfer verbatim; **(1c) does not** ⚠**H2** — the paper says "we derive the required conditions" and stops. The missing argument: if $\mathcal J$ is the expanded covering crucial in $D^{(2)}$, then $\mathcal J^{(1)}$ has no solutions (else **[same-level]** part (2), applied to $\mathcal J$ — cycle-consistent irreducible by (p7), $D^{(2)}$ 1-consistent for it by (p8) — would give a solution of $\mathcal J^{(2)}$), and any single-constraint weakening of $\mathcal J$ has a solution in $D^{(2)}\subseteq D^{(1)}$; hence $\mathcal J$ is crucial in $D^{(1)}$.

**Case 2: no $D_x^{(1)}$ has a nontrivial BA or central subuniverse.**
Then in particular every $D_x^{(1)}$ is S-free (needed by Lemmas 31/37) ⚠(implicit but immediate).
**[§2, Lemma 13 (Ubiquity)]** applied to $D_z^{(1)}\lll D_z$ with $|D_z^{(1)}|>1$: there are $z$, $T\in\{\mathrm{PC},\mathrm L\}$, $\sigma$, $E$ with $E<^{D_z}_{T(\sigma)}D_z^{(1)}$.

#### 2.2.1 Proof of (1a) in Case 2

Fix a constraint $C\in\mathcal I$. By cruciality, weakening $C$ gives a solution $s$ of the weakened
instance in $D^{(1)}$. For each variable $x$ let $D_x^{(2)}$ be the **minimal** $\mathcal MT$-subuniverse of
$D_x^{(1)}$ containing $s(x)$ (i.e. the intersection of all $T$-subuniverses of $D^{(1)}_x$ containing $s(x)$).

- **[§2, Lemma 23]** $D^{(2)}\lll^DD^{(1)}$ (hence $\lll D$).
- **[§3.2, Lemma 31]** gives two subcases. ⚠**H20**: Lemma 31 needs each $D_x^{(2)}$ to be a *minimal* $\mathcal MT$-subuniverse, whereas the construction only makes it minimal *among those containing $s(x)$*; the bridging lemma (`LEMMinimalContainingIsMinimal`) is **commented out** of the source at L1864–1870 and its citation is commented out at L2527. It is true (distinct blocks of the same congruence are disjoint), but must be re-proved.
- **Subcase 1** ($\mathcal I^{(2)}$ 1-consistent): $\mathcal I^{(2)}$ has no solutions, so weaken to crucial in $D^{(2)}$; $C$ survives (weakening $C$ already yields a solution in $D^{(2)}$, and weaker instances only gain solutions). **[IH]** applied to (that instance, $D^{(2)}$) gives (1a), in particular for $C$.
- **Subcase 2** (some $C'^{(2)}=\varnothing$): necessarily $C'=C$ (since $s$ witnesses $C''^{(2)}\ne\varnothing$ for $C''\ne C$). **[§3.2, Lemma 38]** applied to the single constraint $C$ (crucial as a one-constraint instance in $D^{(2)}$, using $s$) gives the parallelogram property.

Since $C$ was arbitrary, (1a) holds. Note that $D^{(2)}$ **depends on $C$**.

#### 2.2.2 Proof of ((1b) or (1c)) in Case 2

Set $\mathcal B=\{B\mid B<^{D_z}_{T(\sigma)}D^{(1)}_z\}$ — **same $z$, same $T$, same $\sigma$**. ⚠**H7**: the
proof uses, without saying so, that $\mathcal B$ is exactly the set of nonempty traces
$D_z^{(1)}\cap E$ of $\sigma$-blocks $E$, i.e. a **partition of $D_z^{(1)}$ with $|\mathcal B|\ge2$**
(the conditions "$(D^{(1)}_z)^2\subseteq\sigma^*$" and "$D^{(1)}_z/\sigma$ BA- and center-free" do not
depend on the block).

For each $B\in\mathcal B$: $D^{(B,\top)}$ = $D^{(1)}$ except $D_z^{(B,\top)}=B$; $D^{(B,\bot)}$ = the maximal
(possibly empty) 1-consistent reduction $\le D^{(B,\top)}$ ⚠H6. **[ext, Lemma 35]** gives tree-coverings
$\Upsilon_{B,x}$ with $\Upsilon_{B,x}^{(B,\top)}(x)=D_x^{(B,\bot)}$, and one puts
$\Upsilon_x:=\bigwedge_{B\in\mathcal B}\Upsilon_{B,x}$ (glued along $x$) ⚠**H9**, claiming
$\Upsilon_x^{(B,\top)}(x)=D_x^{(B,\bot)}$ for **all** $B$ simultaneously.
$\mathcal B_0:=\{B\in\mathcal B\mid D_x^{(B,\bot)}\ne\varnothing\}$ ⚠**H8** (free variable $x$).

**Case 2a: $\mathcal B_0=\varnothing$.**

1. Take a tree-covering $\Upsilon$ (i.e. some $\Upsilon_x$) with $\Upsilon^{(B,\top)}$ unsolvable for all $B$; its solution set is subdirect by (p4).
2. $T\ne\mathrm{PC}$, because **[§3.2, Lemma 37]** with $T=\mathrm{PC}$ produces a nonempty 1-consistent reduction below $D^{(B,\top)}$, i.e. $D^{(B,\bot)}\ne\varnothing$. Hence $T=\mathrm L$.
3. Weaken $\Upsilon$ maximally keeping "$\Upsilon^{(B,\top)}$ unsolvable for every $B\in\mathcal B$"; call it $\Upsilon'$.
4. **Claim** (⚠**H10**, proof omitted; the source's commented-out justification is at L3599–3600): $\Upsilon'$ still contains every constraint relation of $\mathcal I$. Reconstruction: if all children of $C\in\mathcal I$ had been weakened, $\Upsilon'$ would be an expanded covering of "$\mathcal I$ with $C$ weakened", which has a solution $s$ in $D^{(1)}$ by cruciality; by (p3) $\Upsilon'$ has a solution in $D^{(1)}$; and by H7 the value $s(z)$ lies in *some* $B\in\mathcal B$, so $\Upsilon'^{(B,\top)}$ is solvable — contradiction. **This uses H7 essentially.**
5. For $C_1,C_2\in\mathcal I$ sharing a variable $x$: **[§3.2, Lemma 39]** applied to $\Upsilon'$ gives bridges $\mathrm{Con}(C_1,x)\to\sigma$ and $\sigma\to\mathrm{Con}(C_2,x)$; compose **[ext, Lemma 28]**. The composite is reflexive because $\Upsilon$ is a tree-covering and the child-of-$x$ → child-of-$z$ → back path projects to a closed walk in the cycle-consistent $\mathcal I$. Lemma 39 also yields that all congruences in $\mathrm{Congruences}(\mathcal I)$ are linear. ⚠**H11**: hypotheses (6)–(8) of Lemma 39 are not verified, and $D^{(B,\top)}$ restricts *all* children of $z$ whereas Lemma 39 restricts a *single* variable.
6. Conclude: $\mathcal I$ connected; then (1b) if its solution set is subdirect, (1c) otherwise ⚠**H14**.

**Case 2b: $\mathcal B_0\ne\varnothing$.** For an expanded covering $\mathcal J$ of $\mathcal I$, put
$\mathrm{Sol}(\mathcal J):=\{B\in\mathcal B_0\mid \mathcal J^{(B,\bot)}$ has a solution$\}$.

*Construction of $\Omega$.* A finite set of instances with
1. every member is a weakening of $\mathcal I$;
2. $\bigcap_{\mathcal J\in\Omega}\mathrm{Sol}(\mathcal J)=\varnothing$;
3. replacing any member by all weaker instances destroys 2;
4. for every $\mathcal J\in\Omega$ there is $B\in\mathcal B_0$ with (a) $\mathcal J$ crucial in $D^{(B,\bot)}$ and (b) $B\in\mathrm{Sol}(\mathcal J')$ for all $\mathcal J'\in\Omega\setminus\{\mathcal J\}$.

Start with $\Omega=\{\mathcal I\}$ (2 holds because $\mathcal I^{(1)}$ has no solutions and $D^{(B,\bot)}\le D^{(1)}$);
repair 3 by replacing; terminate ⚠H5; then 4 follows from 3 by taking
$B\in\bigcap_{\mathcal J'\ne\mathcal J}\mathrm{Sol}(\mathcal J')\cap\bigcap_{C\in\mathcal J}\mathrm{Sol}(\mathcal J_C)$
(with $\mathcal J_C$ = $\mathcal J$ with $C$ weakened) ⚠H23, H24.

Two derived operators: $\bot(\mathcal J):=\mathcal J\wedge\bigwedge_{x\in\mathrm{Var}(\mathcal J)}\Upsilon_x$
(renamed so $\Upsilon_x$ meets $\mathcal J$ only in $x$) and $\Delta(\mathcal J)$ := $\mathcal J$ plus
$\sigma(z',z'')$ for every pair of variables with parent $z$ ⚠H22. (The $\sigma(z',z'')$ constraints are
legal in an expanded covering because $\sigma$ is reflexive.)

**[IH]** For every weakening $\mathcal J$ of $\mathcal I$ and $B\in\mathcal B_0$ with $\mathcal J$ crucial in
$D^{(B,\bot)}$: $\mathcal J$ satisfies (1b) or (1c). (Measure drops: $D^{(B,\bot)}_z\subseteq B\subsetneq D_z^{(1)}$;
$\lll D$ from **[§3.2, Cor 36]**.)

*Subcase 1: some $\mathcal I'\in\Omega$ fails (1b).*
Put $\Omega'=\{\mathcal I'_C\mid C\in\mathcal I'\}\cup(\Omega\setminus\{\mathcal I'\})$ and
$\mathcal B_1=\bigcap_{\mathcal J\in\Omega'}\mathrm{Sol}(\mathcal J)\ne\varnothing$ (by 3). Every $B\in\mathcal B_1$
makes $\mathcal I'$ crucial in $D^{(B,\bot)}$. Iterate **[IH]** to produce $\mathcal J_1,\dots,\mathcal J_s$
(expanded coverings of $\mathcal I'$, each crucial in some $D^{(B,\bot)}$, each carrying a connected
subinstance with non-subdirect solution set) with
$\mathcal B_1\cap\bigcap_{i\in[s]}\mathrm{Sol}(\mathcal J_i)=\varnothing$; the chain
$\mathcal B_1\supsetneq\mathcal B_2\supsetneq\dots$ is strictly decreasing because
$B\notin\mathrm{Sol}(\mathcal J_i)$ for the $B$ used at step $i$. (Index typo "$\mathrm{Sol}(\mathcal J_s)$"
for "$\mathrm{Sol}(\mathcal J_i)$" ⚠H21.)
Put $\Theta=\Delta\bigl((\bigwedge_{\mathcal J\in\Omega'}\bot(\mathcal J))\wedge(\bigwedge_{i=1}^s\bot(\mathcal J_i))\bigr)$.
$\Theta$ is an expanded covering of $\mathcal I$ with no solution in $D^{(1)}$ (a solution would put all children
of $z$ in one $B\in\mathcal B$ — by the $\Delta$-constraints — and then $B$ would be in every $\mathrm{Sol}$,
contradicting emptiness of the intersection; **uses H7 again**). Weaken to $\Theta'$ crucial in $D^{(1)}$; the
$\mathcal J_s$-part survives ⚠**H25**; hence (1c).

*Subcase 2: every $\mathcal J\in\Omega$ satisfies (1b).*
Then each $\bot(\mathcal J)$ has a subdirect solution set. If $\Omega=\{\mathcal I\}$, then $\mathcal I$
satisfies (1b) and we are done. Otherwise every $\mathcal J\in\Omega$ is a proper weakening, so
$\mathcal J^{(1)}$ and $\bot(\mathcal J)^{(1)}$ have solutions. **[§3.2, Lemma 39]** applied to $\bot(\mathcal J)$
(whose crucial constraints are linear-type by (1b)) forces $T=\mathrm L$ ⚠**H12**, ⚠H11.
Then connectivity of $\mathcal I$: fix $C\in\mathcal I$, $x\in\mathrm{Var}(C)$, put
$\Theta=\Delta(\bigwedge_{\mathcal J\in\Omega}\bot(\mathcal J))$ and weaken all constraints except the
$\sigma(z',z'')$ to get $\Theta'$ crucial in $D^{(1)}$. A child of $C$ survives (else $\Theta'$ would be an
expanded covering of a $C$-weakened $\mathcal I$, which has a solution in $D^{(1)}$; use (p3)). Let $\Theta'_{\mathcal J}$
be the $\bot(\mathcal J)$-part containing it, $B$ the block witnessing its cruciality, and $\mathcal M$ a minimal
set of children of $z$ that must be restricted to $B$ to kill all solutions of $\Theta_{\mathcal J}'^{(1)}$.
- *Subsubcase 1* (the child of $C$ lives inside a $\Upsilon_y$): $\mathcal M$ meets that $\Upsilon_y$ (tree-covering + 1-consistency); **[§3.2, Lemma 39]** gives a bridge $\sigma\to\mathrm{Con}(C,x)$ and that $\mathrm{Con}(C,x)$ is linear.
- *Subsubcase 2* (the child of $C$ lives in the $\mathcal J$-part): pick $y$ such that some variable of $\mathcal M$ lies in a child of $\Upsilon_y$ ⚠**H13**; **[Lemma 39]** gives a bridge $\sigma\to\xi$ for some $\xi\in\mathrm{Congruences}(\mathcal J,y)$, then **[§3.2, Lemma 34(b)]** (using connectedness of $\mathcal J$ from (1b)) gives $\xi\to\mathrm{Con}(C,x)$; compose. The paper explicitly notes that the direct bridge would *not* have a big enough $\widetilde\delta$ — the two-step detour is needed to keep $\widetilde\delta\supseteq$ a path relation $z\rightsquigarrow x$ in $\mathcal I$.

Finally: for $C_1,C_2$ sharing $x$, compose the two bridges to $\sigma$ and back; cycle-consistency makes the
composite reflexive; hence $C_1,C_2$ adjacent, $\mathcal I$ connected (rectangularity from (1a),
irreducibility of the $\mathrm{Con}$'s from **[§3.2, Lemma 32]** ⚠H15), all $\mathrm{Con}$'s linear
(**[§2, Lemma 8]** from the bridge to the linear $\sigma$). Then (1b) if the solution set is subdirect, (1c)
otherwise ⚠**H14**.

### 2.3 Theorem 42 (`THMPCDoesnotKillAllSolutions`)

For $G<^{D_y}_{\mathrm{PC}(\sigma)}D_y$ write $D^{(G,\top)}$ for the reduction that is $G$ at $y$ (typo: the
source writes $D_z^{(G,\top)}$ ⚠H17) and full elsewhere; $\mathrm{Sol}(\mathcal J)=\{G\in D_y/\sigma\mid\mathcal J^{(G,\top)}$ solvable$\}$
(so $G$ ranges over *all* $\sigma$-blocks — same H7 phenomenon, here trivially true since the ambient is
the full domain).

1. Assume no solution with $y\in B$. Choose $\mathcal B\subsetneq D_y/\sigma$ inclusion-maximal among sets of the form $\mathrm{Sol}(\mathcal J)$, $\mathcal J\in\mathrm{Expanded}(\mathcal I)$ (nonvacuous: $\mathcal J=\mathcal I$ works). Fix a witness $\mathcal J$ and pick $G\notin\mathcal B$.
2. **[§3.2, Lemma 37]** ($T=\mathrm{PC}$) gives a nonempty 1-consistent reduction $\le D^{(G,\top)}$ for $\mathcal I$; by (p8) the maximal 1-consistent $D^{(G,\bot)}\le D^{(G,\top)}$ *for $\mathcal J$* is nonempty. **[ext, Lemma 35]** gives tree-coverings $\Upsilon_x$ of $\mathcal J$ with $\Upsilon_x^{(G,\top)}(x)=D_x^{(G,\bot)}$.
3. Weaken $\mathcal J$ to $\mathcal J'$ crucial in $D^{(G,\bot)}$ (possible since $G\notin\mathrm{Sol}(\mathcal J)$). **[§3.3, Theorem 41]** applied to $(\mathcal J',D^{(G,\bot)})$: (1b) or (1c). Side conditions: $\mathcal J'$ is an expanded covering of $\mathcal I$ (p2,p6) hence cycle-consistent irreducible **[ext, Lemma 30]**; $D^{(G,\bot)}\lll D$ by **[§3.2, Cor 36]**.
4. **(1b) branch**: $\mathcal J'':=\mathcal J'\wedge\bigwedge_x\Upsilon_x$ is an expanded covering of $\mathcal I$ with subdirect solution set; it has a solution (as $\mathcal I$ does); $\mathcal J''^{(G,\top)}$ has none; weakening any constraint coming from $\mathcal J'$ gives a solution in $D^{(G,\top)}$. **[§3.2, Lemma 39]** then forces $\mathrm{PC}=\mathcal T=T=\mathrm L$ — contradiction. ⚠H11 (again: $D^{(G,\top)}$ restricts *every* child of $y$).
5. **(1c) branch**: take $\Theta\in\mathrm{Expanded}(\mathcal J')$ crucial in $D^{(G,\bot)}$ with linked connected $\Upsilon\subseteq\Theta$, and $\Theta'=\Theta\wedge\bigwedge_{x\in\mathrm{Var}(\Theta)}\Upsilon_x$ (needs $\Upsilon_x$ for children too — implicit ⚠H22). The paper says $\Theta'$ "has a subdirect solution set": **that is false** ⚠**H16**, but it is never used.
   - $x\in\mathrm{Var}(C)$, $C\in\Upsilon$; **[§3.2, Lemma 34(p)]**: $\mathrm{Con}(C,x)=:\omega$ is perfect linear with witness $\zeta$.
   - $\Theta''$ := $\Theta'$ with the occurrence of $x$ in $C$ renamed $x'$ and $\zeta(x,x',z)$ added ($z$ new over $\mathbf Z_p$); $\Theta'''$ := $\Theta''$ with $\zeta(x,x',z)$ replaced by $\omega^*(x,x')$ (i.e. $z$ projected out).
   - $\Theta'''$ is an expanded covering of $\mathcal J$, so $\mathrm{Sol}(\Theta''')\supseteq\mathrm{Sol}(\mathcal J)=\mathcal B$; cruciality of $C$ in $\Theta$ gives $G\in\mathrm{Sol}(\Theta''')$; maximality of $\mathcal B$ forces $\mathrm{Sol}(\Theta''')=D_y/\sigma$.
   - $R:=\{(F,j)\mid\Theta''$ has a solution in $D^{(F,\top)}$ with $z=j\}\le_{sd}(D_y/\sigma)\times\mathbf Z_p$, $(G,0)\notin R$, $(G,j)\in R$ for some $j$.
   - **[§2, Corollary 22]** applied to $R$, $\{G\}<_{\mathrm{PC}}D_y/\sigma$, $\{0\}<_{\mathrm L}\mathbf Z_p$: every admissible outcome requires $T_1=T_2$; PC $\ne$ L. Contradiction.

### 2.4 Theorem 43 (`THMCSPDReductionsAreSafe`)

- $T=\mathrm{PC}$: **[Theorem 42]**.
- $T\in\{\mathrm{BA},\mathrm C\}$: **[§3.2, Lemma 37]** with the *trivial* reduction $D$ as $D^{(1)}$ (1-consistent because $\Theta$ is, and $D\lll D$) gives a 1-consistent $D'\le_TD$ with $D'_x\subseteq B$; **[Theorem 41(2)]** with $D^{(1)}:=D$, $D^{(2)}:=D'$ and "$\Theta^{(1)}=\Theta$ has a solution" gives a solution of $\Theta^{(1)}$, i.e. of $\Theta$ with $x\in B$.

Three lines of text; the entire content is in Thm 41 and Thm 42. (Name collision: the lemma's $D^{(1)}$ and
the theorem's $D^{(1)}$ are different objects.)

### 2.5 Theorem 44 (`THMCodimensionOneTheorem`)

1. If $\Delta$ is full, done. Else pick $(b_1,\dots,b_k)\notin\Delta$; $D^{(1)}:=\phi(b)$ read as a reduction. Condition 7 $\Rightarrow$ $\mathcal I$ is crucial in $D^{(1)}$ (each single-constraint weakening is solvable in $\phi(b)$; $\mathcal I^{(1)}$ is not) ⚠H24.
2. **Goal:** find $C\in\mathcal I$, $x\in\mathrm{Var}(C)$ with $\mathrm{Con}(C,x)$ a *perfect linear congruence*.
   **[§3.2, Lemma 31]** (with the *ambient* reduction $D$, $T=\mathrm L$, $D^{(2)}:=\phi(b)$; needs $\phi(b)_x$ to be a minimal $\mathcal M\mathrm L$-subuniverse of $D_x$ — see ⚠H19/H20) gives:
   - **Case 1** ($C_0^{(1)}=\varnothing$): cruciality forces $\mathcal I=\{C_0\}$, $C_0=R(y_1,\dots,y_t)$. **[§3.2, Lemma 38]**: $R$ has the parallelogram property and $\mathrm{Con}(R,1)$ is a *linear* congruence with $\mathrm{Con}(R,1)^*=D_{y_1}^2$. **[§2, Lemma 11]**: $\mathbf D_{y_1}/\mathrm{Con}(R,1)\cong\mathbf Z_p$ (source writes "$/\delta$" ⚠H18). The homomorphism $\psi$ yields $\zeta=\{(a_1,a_2,b)\mid\psi(a_1)-\psi(a_2)=b\}$, so $\mathrm{Con}(R,1)$ is perfect linear.
   - **Case 2** ($D^{(1)}$ 1-consistent for $\mathcal I$): **[§3.3, Theorem 41]** gives (1a) and (1b)/(1c).
     - (1c): $\Theta\in\mathrm{Expanded}(\mathcal I)$ crucial in $D^{(1)}$ with linked connected $\Upsilon$, $\mathrm{Sol}(\Upsilon)$ not subdirect. Because of condition **3** (the source says "condition 4" ⚠H18), $\Upsilon$ must use an *un-weakened* constraint relation of $\mathcal I$; then **[§3.2, Lemma 34(p)]** gives a perfect linear $\mathrm{Con}(C,x)$ for the corresponding parent constraint.
     - (1b): $\mathcal I$ is connected, and *linked* by hypothesis 1, so **[§3.2, Lemma 34(p)]** applies directly.
3. Add a new variable $z$ over $\mathbf Z_p$, rename $x$ in $C$ to $x'$, add $\zeta(x,x',z)$; call it $\mathcal I'$. Let $L=\{(a_1,\dots,a_k,b)\mid\mathcal I'$ has a solution with $z=b$ in $\phi(a)\}$; it is a subalgebra of $\mathbf Z_{q_1}\times\dots\times\mathbf Z_{q_k}\times\mathbf Z_p$ (pp-definable).
4. Condition 7 $\Rightarrow$ $\mathrm{proj}_{1..k}(L)$ full (projecting $z$ out of $\zeta$ gives $\omega^*$, i.e. $C$ weakened at $x$); $(b_1,\dots,b_k,0)\notin L$ ($z=0$ recovers $\mathcal I$). Hence $L$ is the graph of an affine map $a\mapsto z=\ell(a)$ ("dimension $k$, one linear equation").
5. If $\ell\equiv c\ne0$ then $\Delta=\varnothing$; otherwise $\Delta=\{a\mid\ell(a)=0\}$ is an affine subspace of codimension 1 (it is proper since $b\notin\Delta$).

---

## 3. The main induction, reconstructed

The paper says exactly one sentence about it: *"We prove the claim by induction on the size of $D^{(1)}$."*
(L3432). Everything below is reconstruction.

### 3.1 What is being inducted on

Let, for an instance $\mathcal I$ and a reduction $D^{(1)}$ for it,

$$\mu(\mathcal I,D^{(1)}):=\sum_{x\in\mathrm{Var}(\mathcal I)}\bigl|D^{(1)}_x\bigr|\in\mathbb N .$$

The statement proved by strong induction on $m=\mu(\mathcal I,D^{(1)})$ is

> **P(m):** for **every** instance $\mathcal I$ and reduction $D^{(1)}$ with $\mu(\mathcal I,D^{(1)})=m$ satisfying
> $H_0$ := [$\mathcal I$ irreducible and cycle-consistent; $D^{(1)}$ is a 1-consistent reduction for $\mathcal I$; $D^{(1)}\lll D$]:
>   **(A)** $\mathcal I$ crucial in $D^{(1)}$ $\Rightarrow$ (1a) $\wedge$ ((1b) $\vee$ (1c));
>   **(B)** $\forall\mathcal T\in\{\mathrm{BA},\mathrm C\}$, $\forall D^{(2)}\le_{\mathcal T}D^{(1)}$ 1-consistent for $\mathcal I$: $\mathcal I^{(1)}$ solvable $\Rightarrow\mathcal I^{(2)}$ solvable.

The quantification over **all** $\mathcal I$ at a given $m$ is essential: several appeals change the instance
while keeping the same reduction.

### 3.2 The two-phase structure inside one induction step

Inside the step for $m$, the order of business is:

* **first prove (B) for all $\mathcal I$ at level $m$**, using only $\mathrm{P}(m')$ for $m'<m$;
* **then prove (A) for all $\mathcal I$ at level $m$**, using $\mathrm{P}(m')$ for $m'<m$ **and (B) at level $m$**.

That is a legitimate strong induction on $m$ of the conjunction $(A_m\wedge B_m)$ — no lexicographic
gadget is needed — but the *proof text does not say this*, and it calls both kinds of appeal "the
inductive assumption".

### 3.3 Every appeal, and why the measure drops

| # | where | instance passed | reduction passed | which part | measure argument |
|---|---|---|---|---|---|
| 1 | (2), step 1 | $\mathcal I'$ = weakening of $\mathcal I$, crucial in $D^{(2)}$ | $D^{(2)}$ | (A) | $D^{(2)}\le_{\mathcal T}D^{(1)}$; if $D^{(2)}=D^{(1)}$ then $\mathcal I^{(2)}=\mathcal I^{(1)}$ *is* solvable, contradiction ⇒ strict at some $x$. **Not stated in the paper.** |
| 2 | Case 1, "$\mathcal J^{(2)}$ has a solution" | $\mathcal J$ = one-constraint weakening of $\mathcal I$ | $(D^{(1)},D^{(2)})$ | **(B) at the SAME level** | none needed — this is *not* the IH. **The paper calls it the inductive assumption.** |
| 3 | Case 1, "Again applying…" | $\mathcal I$ | $D^{(2)}$ from Lemma 37 | (A) | $D_x^{(2)}\subseteq B\subsetneq D_x^{(1)}$ |
| 4 | Case 2, (1a), Subcase 1 | weakening of $\mathcal I$ crucial in $D^{(2)}$ | $D^{(2)}$ = minimal $\mathcal MT$ containing $s$ | (A), only (1a) used | $D_z^{(2)}\subseteq E\subsetneq D_z^{(1)}$ because $E<_{T(\sigma)}^{D_z}D_z^{(1)}$ exists |
| 5 | Case 2b, "For any weakening $\mathcal J$…" | weakenings $\mathcal J$ of $\mathcal I$ | $D^{(B,\bot)}$ | (A), only (1b)/(1c) used | $D^{(B,\bot)}_z\subseteq B\subsetneq D^{(1)}_z$ |
| 6 | Case 2b, Subcase 1 chain | $\mathcal I'\in\Omega$ (a weakening) | $D^{(B,\bot)}$, varying $B$ | (A), (1c) | same as 5 |

Observations:

* **The variable set never grows** in an IH appeal. Weakenings can *shrink* $\mathrm{Var}$ (a weaker constraint may have fewer variables), which only decreases $\mu$. Expanded coverings — which *do* add variables — appear only in *conclusions* ((1c)), never as IH inputs. This is what makes $\mu$ work; if the induction ever had to be applied to a covering, $\mu$ would be the wrong measure.
* Every IH target satisfies $D^{(\text{new})}_x\subseteq D^{(1)}_x$ for all $x$. So an equally good (and in Lean, more convenient) well-founded relation is **componentwise strict inclusion of reductions over a fixed finite variable set**, or the pair (finite set of variables, reduction) ordered lexicographically. The paper's phrase "the size of $D^{(1)}$" is best read as $\mu$.
* The side conditions $H_0$ must be re-established at every appeal. Two of them are nontrivial and are never mentioned:
  * *irreducible + cycle-consistent for the new instance* — always via **(p2) weakening = expanded covering** + **Lemma 30 [ext]**;
  * *$D^{(\text{new})}\lll D$* — via transitivity of $\lll$, plus **Corollary 36** for the $D^{(B,\bot)}$'s (this is why Cor 36 exists).
* Strictness of the decrease in appeal #1 is the one place where the proof would break if it were not argued; the argument is one line but is absent.

### 3.4 Is the measure well-founded, and is it explicit?

Well-founded: yes ($\mu$ lands in $\mathbb N$, and each appeal strictly decreases it). Explicit: **no**.
The paper states neither $\mu$, nor the strictness at each appeal, nor the (A)-uses-(B)-at-the-same-level
phase structure, nor the "for all instances at this level" quantification. A formalization must make all
four explicit; they are the load-bearing part of the whole theorem.

---

## 4. The three Informal Claims (L518–565) vs. the formal statements

The introduction (L505–511) says: *"Three main statements that imply the correctness are formulated in
Section 'Correctness of the algorithm' in [33]. Below we formulate informal analogues of these statements,
and the formal statements can be found in Section 3.4."*

| Informal Claim | Formal counterpart | Where | Fidelity |
|---|---|---|---|
| **IC1** `ICExistenceStrong`: each $D_x$ with $\|D_x\|\ge2$ has a strong subset, or an equivalence $\sigma$ with $D_x/\sigma\cong\mathbb Z_p$ | **Lemma 13** (`LEMUbiquity`) + **Lemma 11** (`LEMLInearOnTheTopIsEasy`) + **Lemma 12** (`LEMPCOnTheTopIsEasy`) | **§2**, *not* §3.4 | Lemma 13 gives $C<_T^AB$ with $T\in\{\mathrm{BA},\mathrm C,\mathrm L,\mathrm{PC}\}$ for $B\lll A$, $\|B\|>1$. With $B=A=D_x$: BA/central = "strong subset"; $T=\mathrm L$ + Lemma 11 gives $D_x/\sigma\cong\mathbf Z_p$; $T=\mathrm{PC}$ + Lemma 12 gives $D_x/\sigma$ a PC algebra, whose $\sigma$-blocks are the "PC strong subsets" of the original proof. **The intro's pointer to §3.4 is wrong for IC1.** |
| **IC2** `ICReductionTOStrong`: cycle-consistent+irreducible $\mathcal I$ with a solution, $B$ a strong subset of $D_x$ $\Rightarrow$ a solution with $x\in B$ | **Theorem 43** (`THMCSPDReductionsAreSafe`) | §3.4 | Exact, once "strong subset" is unfolded as $B<^{D_x}_TD_x$ with $T\in\{\mathrm{BA},\mathrm C,\mathrm{PC}\}$. Note the formal version is an "iff" and drops the explicit "$\Gamma$ preserved by a WNU" (absorbed into $\mathbf D_x\in\mathcal V_n$). |
| **IC3** `ICCodimensionOne`: … $\Rightarrow$ $\{a\mid\mathcal I$ solvable in $\varphi(a)\}$ is empty, full, or of dimension $m-1$ | **Theorem 44** (`THMCodimensionOneTheorem`) | §3.4 | Matches, with three discrepancies (below). |

IC3 vs Thm 44, clause by clause:

| IC3 clause | Thm 44 clause | comment |
|---|---|---|
| 2. "consistent enough (cycle-consistent + irreducible + **another one**)" | 1. linked cycle-consistent irreducible; 3. weakening *all* constraints yields a subdirect solution set | the "another one" is condition 3 |
| 3. "$D_{x_i}$ has **no strong subsets**" | 2. "$D_{x_i}$ is **S-free**" | ⚠**H19** — these are *not* the same; S-free is much weaker (it only forbids simultaneously-BA-and-central subuniverses). The commented-out gloss at L4009 says "there does not exist a nontrivial binary absorbing subuniverse or a nontrivial center on $D_{x_i}$", i.e. the informal reading. The proof needs the strong version (see §5). |
| 4. "$\mathcal I$ is linked" (given as an explicit graph-connectivity definition) | 1. "linked" | same |
| 5. $\sigma_{x_i}$ minimal with $D_{x_i}/\sigma_{x_i}\cong\mathbb Z_{q_1}\times\dots$ | 4. $\sigma_{x_i}=\bigcap\{$linear congruences $\sigma$ with $\sigma^*=D_{x_i}^2\}$ | the formal version is the *definition that is actually usable*; the equivalence with the informal one is not proved anywhere in this paper (it follows from Lemma 11 + the classification of linear congruences, but is left to the reader) |
| 6. $\varphi$ a "linear map" | 6. $\phi$ a homomorphism of $\mathcal V_n$-algebras | same thing here |
| 7. removing any constraint leaves a solution in every $\varphi(\alpha)$ | 7. **weakening** any constraint … | *weakening* is strictly stronger than *removal*; the algorithm (`SolveLinear`, L698–703) removes constraints. Reconciling the two is left implicit. |
| conclusion "dimension $m-1$" | "codimension 1" | same |

Where the claims are used by the algorithm (L593–755): IC1 justifies that `Solve` always finds either a
strong subset or a linear quotient; IC2 justifies `ReduceDomain`; IC3 justifies the dimension-reduction
loop inside `SolveLinear` (steps (p1)–(p3)). **The algorithm itself is not in this paper** — it is in
[33]/[32]; §3.4 only supplies the three correctness statements. A blueprint therefore needs [33]'s
algorithm + the reduction of "CSP(Γ) in P" to Thms 43/44 as a separate, currently un-sourced component.

---

## 5. Formalization hazards

Ordered roughly by how much damage they do.

**H2 (real gap, must be filled).** Thm 41, Case 1: "Again applying the inductive assumption to $D^{(2)}$ we
derive the required conditions." The IH delivers (1c) *relative to $D^{(2)}$*, but the goal is (1c) *relative
to $D^{(1)}$*, and (1c) is the one alternative that mentions the reduction. The transport step (given in
§2.2 above) needs part (2) at the same level plus (p7)/(p8). Two lines, but they are not in the paper.

**H14 (real gap).** Both endgames close with "… satisfies (1b) if its solution set is subdirect, or (1c)
otherwise". (1c) demands a **linked** connected subinstance with non-subdirect solution set; what has been
proved is only *connected* and *non-subdirect*. The missing argument goes through **irreducibility**:
$\mathcal I$ itself is an admissible $\mathcal I'$ in the definition of irreducible, so $\mathcal I$ is
fragmented or linked; in the fragmented case one must descend to a non-fragmented fragment with
non-subdirect (possibly empty) solution set and check that it is still connected. Also note the degenerate
case where $\mathcal I$ has *no* solutions at all over the full domains (legitimate when $D^{(1)}=D$), where
"non-subdirect" is vacuous.

**H4 (well-foundedness).** No measure is written down; strictness is never argued; in appeal #1 it needs the
observation "$D^{(2)}=D^{(1)}$ contradicts the case assumption". See §3.

**H3 (quantifier structure).** "The inductive assumption" denotes two different things (IH at smaller
measure; part (2) at the same measure). A Lean formalization must split Thm 41 into two named statements
and be explicit about the phase order.

**H11 (multi-child restriction).** Lemma 39 restricts a **single** variable $z$ to $B$; but $D^{(B,\top)}$
(and $D^{(G,\top)}$ in Thm 42) restricts **every child of $z$** in an expanded covering. The proof of Thm 41
Case 2b handles this by taking "a minimal set $\mathcal M$ of children of $z$ we need to restrict"; the
Case 2a and Thm 42 applications do not, and simply say "applying Lemma 39". Either Lemma 39 must be
restated for a family of coordinates, or each application must be preceded by the minimal-set reduction
(and, for $|\mathcal M|\ge2$, by Corollary 22 to collapse to one). This recurs at least four times.

**H10 ("must contain every constraint relation").** Asserted with no proof (the source's own justification
is commented out at L3599–3600 and, as written, would be wrong). It is repairable only via H7.

**H7 ($\mathcal B$ is the block partition).** The proof silently uses that
$\mathcal B=\{B\mid B<^{D_z}_{T(\sigma)}D_z^{(1)}\}$ is the set of *all* nonempty traces of $\sigma$-blocks
on $D_z^{(1)}$ — i.e. a partition — so that any value of $z$ in $D^{(1)}_z$ lands in some $B\in\mathcal B$.
Used at least three times (H10; "no solution of $\Theta$ in $D^{(1)}$"; the $\Delta(\cdot)$ construction).
Should be an explicit lemma.

**H19/H20 (Theorem 44's hypothesis 2).** Two coupled problems:
* For $\phi(b)_x$ (an intersection of blocks of linear congruences with $\sigma^*=D_x^2$) to be an $\mathcal M\mathrm L$-subuniverse — hence $\lll D_x$, hence usable in Lemma 31 and Thm 41 — one needs each such $\sigma$ to satisfy "$\mathbf D_x/\sigma$ is BA and center free". **S-free does not give this**; "no nontrivial BA or central subuniverse on $D_x$" does (pull back along $D_x\to D_x/\sigma$ using Lemma 14(bt)). So hypothesis 2 as printed appears too weak, and the commented-out gloss is the intended one.
* Lemma 31 also needs the $D^{(2)}_x$ to be **minimal** $\mathcal M\mathrm L$-subuniverses. In Thm 41 the same requirement is met by "minimal containing $s(x)$", and the lemma that these coincide (`LEMMinimalContainingIsMinimal`) is **commented out of the source** (L1864–1870, citation commented at L2527). It is true — distinct blocks of one congruence are disjoint, so any $\mathcal MT$-subuniverse meeting the minimal one contains it — but must be re-proved.

**H5 (termination of weakening).** "We cannot weaken forever" (L3648); also "weaken $\mathcal I$ to make it
crucial" (Remark 2), "weaken $\Upsilon$ while we can", "weaken $\Theta$ to make … crucial". Each replaces
one constraint by *all* strictly weaker ones, so the constraint multiset grows. Termination needs the
multiset extension of the (well-founded, because everything is finite) strict "is weaker than" order. Four
distinct instances of this pattern.

**H6 (maximal 1-consistent sub-reduction).** Used as if obviously existing and unique. The set-theoretic
union of two 1-consistent reductions *is* 1-consistent (easy) but need not be subuniverse-valued; the
correct construction is the propagation fixpoint $D_z\mapsto\mathrm{proj}_z(C\cap\prod D_x)$, which stays
subuniverse-valued and dominates every 1-consistent reduction below $D^{(\top)}$. Needs to be a lemma.

**H9 (the "universal tree-covering" $\Upsilon_x=\bigwedge_B\Upsilon_{B,x}$).** Three unstated obligations:
(i) a definition of conjunction-with-renaming of instances; (ii) a glue-at-one-variable of tree-instances is
a tree-instance; (iii) $\Upsilon_x^{(B,\top)}(x)=D_x^{(B,\bot)}$ for *every* $B$, which needs
$\Upsilon_{B',x}^{(B,\top)}(x)\supseteq D_x^{(B,\bot)}$ for $B'\ne B$ — true because $D^{(B,\bot)}$ is
1-consistent and tree-coverings of 1-consistent instances have subdirect solution sets (p4).

**H12.** "Since $\bot(\mathcal J)$ is crucial in $D^{(B,\top)}$ (property 4(a) of $\Omega$)": property 4(a)
says $\mathcal J$ is crucial in $D^{(B,\bot)}$, and $\bot(\mathcal J)$ is *not* crucial in the defined sense
(its $\Upsilon_x$-part constraints are not crucial). What is true and needed: $\bot(\mathcal J)^{(B,\top)}$
is unsolvable and weakening any $\mathcal J$-constraint makes it solvable. Lemma 39's hypotheses (7),(8)
only need that; but the wording must be repaired.

**H13.** Subsubcase 2: "Let $y$ be the variable of $\Theta'_{\mathcal J}$ such that some variable from
$\mathcal M$ appears in a child of $\Upsilon_y$" — existence is asserted, not proved. $\mathcal M$ consists
of children of $z$, which could conceivably all lie in the $\mathcal J$-part.

**H16.** Thm 42, (1c) branch: "$\Theta'$ is an expanded covering of $\mathcal I$ with a subdirect solution
set" is **false** ($\Theta'\subseteq\Theta\supseteq\Upsilon$ and $\Upsilon$'s solution set is not subdirect,
and subdirectness only shrinks when constraints are added). Harmless: the statement is never used; the
subdirectness that *is* used later is that of $R\le(D_y/\sigma)\times\mathbf Z_p$.

**H23 ("all weaker instances").** Condition 3 of $\Omega$ says "replace any instance in $\Omega$ by all
weaker instances"; the verification of condition 4 uses only $\{\mathcal J_C\mid C\in\mathcal J\}$
(one-constraint weakenings). These are different sets; the proof needs the latter reading.

**H8.** "$\mathcal B_0$ = all $B\in\mathcal B$ such that $D_x^{(B,\bot)}$ is not empty" — $x$ is free. "for
every $x$" and "for some $x$" coincide unless the instance is fragmented (emptiness propagates along
constraints), which is not excluded.

**H26 (using Corollary 22).** Cor 22 needs single-step $C_i<_{T_i}B_i$; the reductions in play are $\lll$
chains. The paper's idiom is "consider a minimal reduction $D^{(\top)}$ such that …, then choose
$G<_{\mathcal T_0(\nu)}D_y^{(\top)}$" (Lemma 39, Cor 40). That idiom deserves to be a reusable lemma
("extract one dividing step from a $\lll$ chain at the first place where a property fails").

**H27.** "By Lemma 19 $E_2\le_{\mathcal T}E_1$": Lemma 19 concludes $\mathrm{proj}_1(R\cap\prod C_i)\dot\le_TA_1$,
so one must instantiate $A_1:=E_1$, i.e. take $R$ = the solution relation of $\Theta^{(1)}$ with the
$z$-coordinate first (making it subdirect in that coordinate). Trivial, but the instantiation is not written.

**H29 (hereditary consistency).** Used repeatedly and never stated: 1-consistency and cycle-consistency are
inherited by **subinstances** (fewer constraints, same domains) and by **weakenings** (weaker constraints
have larger projections). Needed to apply Lemma 34 to subinstances $\Upsilon$ and to feed weakenings to the IH.

**H30 (the meaning of "subdirect").** "The solution set of $\mathcal I$ is subdirect" is always relative to
the **full** domains $D_x$, never to the current reduction. Getting this wrong silently breaks Lemma 39
(hypothesis 1) and (1b).

**H24 ("no dummy variables").** Cruciality carries this side condition; it is never re-verified for the many
instances built by weakening, $\bot(\cdot)$, $\Delta(\cdot)$, or covering. Remark 2 promises the weakening
process only introduces constraints without dummy variables.

**H1, H17, H18, H21, H22 (typos / notation debt).** Individually harmless but they force a formalizer to
guess:
* L3436–3438 "Weaken $\mathcal I^{(2)}$ to make it crucial in $D^{(2)}$" — one weakens $\mathcal I$.
* L3874 "$D_z^{(G,\top)}=G$" — should be $D_y^{(G,\top)}=G$.
* L4011 "constraints of $\Theta$" and the conclusion's "$\Theta$" in Thm 44 — should be $\mathcal I$.
* L4084 "By condition 4" — should be condition 3.
* L4070 "$\mathbf D_{y_1}/\delta$" — should be $\mathbf D_{y_1}/\mathrm{Con}(R,1)$.
* L3729/L3733 "$\mathrm{Sol}(\mathcal J_s)$" / "$\bot(\mathcal J_s)$" inside $\bigcap_{i\in[s]}$/$\bigwedge_{i=1}^s$ — should be $\mathcal J_i$.
* §3.1 definitions: irreducible/fragmented "$\mathrm{Var}(C)\subseteq\mathbf X_1$ or $\mathrm{Var}(C)\subseteq\mathbf X_1$" (L2099–2100) — second should be $\mathbf X_2$; Expanded coverings written with $\Omega,\Omega'$ instead of $\mathcal I,\mathcal I'$ (L2171–2180); "crucial" definition contains a stray "Let $D_i'\subseteq D_i$ for every $i$" and refers to $C\in\Theta$ (L2136–2141).
* The instance operations $\wedge$ (conjunction with renaming), $\bot(\cdot)$, $\Delta(\cdot)$, and "$\Upsilon_{x'}$ = $\Upsilon_x$ with $x$ renamed to $x'$" are defined only in prose; the renaming discipline (which variables are shared) is the whole content and is stated informally.

**External imports** (each is a real formalization cost, not available in this paper):
* **Lemma 30** = [33, Lemma 6.1] — expanded coverings preserve cycle-consistency and irreducibility. Used *everywhere*; without it no IH appeal type-checks. (Present as Lemma 6.1 in `1704.01914.txt` L1225.)
* **Lemma 35** = [34, Lemma 5.6] — existence of tree-coverings witnessing the maximal 1-consistent reduction. (Present with a constructive proof in `2005.00593.txt` L911–935.) The backbone of Lemma 37, Thm 41 Case 2, Thm 42.
* **Lemma 19** = [34, Cor 6.1.2 & 6.9.2]; **Lemma 27** = [33, Cor 8.17.1]; **Lemma 28** = [33, Lemma 6.3]; **Lemma 6** = [34, Cor 6.11.1]; **Lemma 26** = [28, Lemma 4.7] (special WNU).

**Dependency summary for module architecture.** §3.3–3.4 is a thin layer:

```
Thm 43  ←  Thm 42, Thm 41(2), Lem 37
Thm 44  ←  Thm 41(1), Lem 31, Lem 38, Lem 34(p), Lem 11
Thm 42  ←  Thm 41(1), Lem 37, Lem 35[ext], Cor 36, Lem 34(p), Lem 39, Cor 22
Thm 41  ←  Lem 13, Lem 19[ext], Lem 23, Lem 29, Lem 8, Cor 22   (§2)
          Lem 30[ext], Lem 31, Lem 32, Lem 34, Lem 35[ext], Cor 36,
          Lem 37, Lem 38, Lem 39, Cor 40                        (§3.2)
          + (p1)–(p8) of expanded coverings, Remark 2           (§3.1)
```

so the formalization cost is concentrated in §2 (the strong/linear subuniverse theory, `StrongSubalgebras.tex`)
and §3.2 — with the *proof-engineering* cost concentrated in Theorem 41, whose 430 lines of prose contain
the six hazards H2, H7, H10, H11, H13, H14 that a Lean proof has to supply from scratch.
