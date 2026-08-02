# The CSP Dichotomy Theorem

CSP(Γ) over a finite constraint language is in P if Γ has a weak near-unanimity
polymorphism, and NP-complete otherwise. This repository is a corrected exposition of
Zhuk's *simplified* proof ([arXiv:2404.01080](https://arxiv.org/abs/2404.01080)),
together with the record of where our rendering departs from it.

## Three documents

| File | Pages | What it is | For |
| --- | --- | --- | --- |
| [`csp-proof.tex`](csp-proof.tex) | 57 | The theorem, the vocabulary, the strong-subalgebra theory with its proofs, the main statements, the algorithm and the hard half. Corrections are made silently. | a mathematical reader |
| [`csp-audit.tex`](csp-audit.tex) | 28 | Every departure from the source: what it has, quoted; why it cannot be transcribed; the repair; and the proof paper's label that carries it. | anyone checking our claims against Zhuk |
| [`csp-blueprint.tex`](csp-blueprint.tex) | 9 | Lean representations, the layers Mathlib lacks, order of attack, and what governs the schedule. | the formalization |

They are compiled separately and share no cross-reference machinery, deliberately, so
that neither can be read as evidence for another. The join key is a statement's label:
the audit and the blueprint refer to `lem:foo` in typewriter, and that label is defined
exactly once, in the proof paper.

```sh
./check.sh                       # build all three; fails on anything a reviewer would call an error
./check.sh csp-proof             # just one
python3 make_standalone.py       # regenerate the single-file versions for review
```

`check.sh` is the build gate. It rejects TeX errors, undefined references, undefined
citations, multiply-defined labels, overfull boxes over 10 pt, `\ref` inside `\cite`, and
any `\ref` to a label defined in a *different* document — plus, for the proof paper,
any repair marker, any commentary on the source, and any mention of a proof assistant.

## What is proved, and what is not

**Read [`§Status and imports`](ch11-status.tex) before relying on anything.** Every
statement in the proof paper is marked *proved*, *imported* (with an exact citation and
the hypotheses as the source states them), *outlined*, *stated only*, or *open*.

The algebraic core of the strong-subuniverse theory is in the best shape: thirty
statements proved, eleven imported, seven outlined, four stated only, one open. The main
statements are not: the lemma that produces bridges from an instance is stated without
proof, and part (1) of the main induction is an outline whose measure is not yet well
founded across expanded coverings.

Six items block the rest:

1. **`lem:maximal-mult`** — open. The maximal multi-type extension.
2. The **reflexivisation of a bridge**, used twice with no lemma behind it.
3. The expansion of **`lem:intersection-good`**, on which much of the bridge theory
   rests, and the rewrite of `lem:multiply-all-linear`.
4. **`lem:no-cross-bridge`** and **`lem:bridge-to-pc`**, consumed by stable intersection.
5. The **induction measure** across expanded coverings, and the **termination of
   weakening** — whose obvious measure points the wrong way.
6. The **linear algebra** of the codimension-one theorem, and the **common binary
   absorption witness** at the call site of `lem:ba-center-implies`.

The dependency order among the three large statements is

```
thm:stable-intersection  →  lem:bridge-from-instance  →  thm:main-inductive
```

Stable intersection is the sole source of bridges; bridge-from-instance is the only thing
that turns them into instance-level structure; the main induction consumes that. Nothing
runs in the reverse direction.

## The audit

Fifteen substantive defects in the source, of which fourteen are repaired and none of
those repairs needs new mathematics: three needed a citation the later paper dropped, one
was a typographical slip, two were statements false as printed, and the rest were omitted
steps. Ten readings are legislated, two of which turn out to be theorems rather than
choices. Four hedges in §5 of the source, all four honest.

Three claims raised here have been published, reviewed, and turned out to be wrong: a
citation cycle in §5 (refuted by a parser in minutes), a recursion-depth bound (the
precondition was in the prose above the pseudocode, not in it), and the published repair
of `lem:maximal-mult` (which walked into the image-versus-intersection trap this very
document catalogues). All three are in the audit, with what went wrong. The evidentiary
standard that followed is: a claim counts as checked only when the cited lines *and the
prose around them* have been read, and the passage can be quoted.

## Relation to the source

Zhuk's paper is not redistributed. Statement labels in the proof paper are its own; the
audit is keyed to `main.tex` and `StrongSubalgebras.tex` of the v2 arXiv source by line
number, obtainable from `arxiv.org/e-print/2404.01080v2`.

Section 4 of that paper (XY-symmetric operations) is an independent second result and is
out of scope.

## License

[CC BY 4.0](LICENSE).
