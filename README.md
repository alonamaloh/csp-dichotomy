# The CSP Dichotomy Theorem — a formalization blueprint

CSP(Γ) over a finite constraint language is in P if Γ has a weak near-unanimity
polymorphism, and NP-complete otherwise. This repository rewrites Zhuk's *simplified*
proof ([arXiv:2404.01080](https://arxiv.org/abs/2404.01080)) as a blueprint for
formalization in Lean 4 / Mathlib.

The Lean development that consumes it is at [`../csp-lean`](../csp-lean).

## The document

| File | Pages | What it is |
| --- | --- | --- |
| [`csp.tex`](csp.tex) | 35 | The blueprint. Compiled PDF committed alongside. |

```sh
pdflatex csp.tex   # twice
```

## What it claims, and what it does not

It does **not** claim that the dichotomy has been formalized. The transitive closure of
what must be proved is on the order of 100–130 printed pages, which extrapolates to
35 000–60 000 lines of Lean — a multi-person-year project that no proof assistant has
attempted.

What it offers is the design: the route, the statements, a vocabulary pinned down where
the sources leave it loose, a list of the places the informal proof has latitude a formal
one does not, an inventory of the missing Mathlib layers, and a Lean development whose
foundations are complete and whose target theorems are stated.

## Layered targets

The dichotomy's statement is conditional on a model of computation, and Mathlib has none —
no P, no NP, no polynomial-time reduction, no SAT. Claiming the theorem verbatim would
mean building a complexity layer from scratch, and the mathematics would be a minority of
the work. So the blueprint separates:

| | Statement | Mentions a machine? |
|---|---|---|
| **T0** | the algebraic core: existence of strong subuniverses, safety of reductions, the codimension-one theorem | no |
| **T1** | `Solve(I) = true ↔ I has a solution`, for Zhuk's algorithm written as a function | no |
| **T2** | `Solve` runs in polynomial time | **yes** |
| **H0** | no WNU ⟹ Γ pp-interprets NAE-3-SAT | no |
| **H1** | pp-interpretation ⟹ poly-time reduction ⟹ NP-hard | **yes** |

The blueprint is written for T0, T1 and H0. T2 and H1 are stated precisely, costed, and
left unbuilt — see §9.

## The route

Among the available proofs:

- **Zhuk 2404.01080** — the spine. The only complete, recent, rigorously written proof
  whose author has already removed the local-to-global induction that made its 2020
  predecessor unformalizable. Its innovation is that every domain reduction is either
  *strong* or *global*, and that the types of the intermediate steps need not be tracked —
  only that a chain exists, written `C ⋘ B`.
- **Brady's notes** ([arXiv:2210.07383](https://arxiv.org/abs/2210.07383)) — the source for
  several imported prerequisites, and the clearest prose in the subject. Stops short of the
  dichotomy, so it cannot be the spine.
- **Zhuk's JACM 2020 proof** — superseded by its author, but the sole source of the
  algorithm itself and of five results 2404 imports.
- **Minimal Taylor algebras** — Zhuk's own remark that they would simplify his §2 is true
  but a bad trade: it simplifies none of §3 and imports the cyclic term theorem, which this
  route does not otherwise need.
- **Bulatov's proof** — needs tame congruence theory and centralizer theory, neither
  formalized anywhere. Ranked last.

Section 4 of 2404 (XY-symmetric operations) is an independent second result and is cut.

## Structure

1. **§1 What is being proved** — the layered targets and why they are separated.
2. **§2–3 Conventions and vocabulary** — the standing hypotheses as a labelled convention
   with an audit of where each is consumed; algebras, subuniverses, relations,
   rectangularity, congruences, irreducibility, `σ*`, bridges.
3. **§4 The six types** — `BA`, `C`, `S`, `D`, `L`, `PC`, the multi-types, and `⋘`.
4. **§5 Instances** — instances, reductions, consistency, weakening, cruciality, coverings,
   `Con₁`, connectedness.
5. **§6 Properties of strong subuniverses** — the interface between the algebra and the CSP
   argument: propagation forward and backward, and the stable-intersection theorem, which
   is the sole source of bridges.
6. **§7 The main statements** — the single induction and the three theorems the algorithm
   consumes.
7. **§8–9 The algorithm and the hard half.**
8. **§10–11 The complexity layer and the formalization plan.**

## Formalization notes

Throughout, marked environments record where the informal proof has latitude a formal one
does not. A sample of what writing the statements down carefully turned up:

- **`Z_p ∈ 𝒱ₙ` only when `p | n−1`.** The operation `x₁+…+xₙ mod p` is idempotent exactly
  when `n ≡ 1 (mod p)`. The source asserts `Z_p ∈ 𝒱ₙ` unconditionally, so every "for some
  prime `p`" in the paper carries a silent divisibility side condition.
- **`σ*` need not be a congruence.** It is a subuniverse of `A²` stable under `σ`, nothing
  more; that it *is* a congruence is a separate hypothesis in the definition of a linear
  congruence, which would be redundant otherwise.
- **Images do not commute with intersection**, and one propagation clause needs them to —
  it gets equality from a saturation hypothesis. A content step, not notation.
- **"We cannot weaken forever"** occurs three times and needs a measure that is not the
  obvious one, because the *scope* of a constraint may shrink as well as its relation.
- **The main induction quantifies over the instance *inside*.** Every appeal to the
  inductive hypothesis changes the instance — to a weakening, or to an expanded covering
  with *more* variables. An induction that fixes the instance does not go through.
- **Two different things are called "linked"** — a binary relation, and a CSP instance —
  and both appear in one proof, where the passage from one to the other is the crux.

None of these is an error in the source. All of them are work.

## Relation to the source

Zhuk's paper is not redistributed. Statement labels in the blueprint are its own; the
concordance with `main.tex`, `StrongSubalgebras.tex` and `XYSymmetric.tex` is by section
number in the text.

## License

[CC BY 4.0](LICENSE).
