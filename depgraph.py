#!/usr/bin/env python3
"""Proof-dependency graph of the proof paper, and a cycle check.

Attributes every `\\begin{proof}` block to a statement -- by the \\ref in its
optional argument if there is one, otherwise to the statement it follows -- and
draws an edge from that statement to every statement \\ref'd inside the block.
Reports cycles, and optionally the transitive closure of a named statement.

    python3 depgraph.py                     # cycle check, summary
    python3 depgraph.py --closure lem:foo   # what lem:foo rests on
    python3 depgraph.py --cluster lem:a lem:b ...   # induced subgraph
"""
import re, sys, pathlib
from collections import defaultdict

ROOT = pathlib.Path(__file__).parent
MAIN = "csp-proof.tex"

STMT = r"theorem|lemma|proposition|corollary|longtheorem|longlemma|longproposition|longcorollary"


def sources(main):
    t = (ROOT / main).read_text()
    return [main] + re.findall(r"(?m)^\s*\\input\{([^}]+)\}", t)


def optional_arg(s, i):
    """Read a bracketed optional argument starting at s[i] == '[', balanced."""
    if i >= len(s) or s[i] != "[":
        return "", i
    depth, j = 0, i
    while j < len(s):
        if s[j] == "[":
            depth += 1
        elif s[j] == "]":
            depth -= 1
            if depth == 0:
                return s[i + 1:j], j + 1
        j += 1
    return "", i


def parse():
    statements, proofs = [], []
    for f in sources(MAIN):
        text = (ROOT / f).read_text()
        last_stmt = None
        for m in re.finditer(r"\\begin\{(" + STMT + r"|proof)\}", text):
            kind, i = m.group(1), m.end()
            opt, i = optional_arg(text, i)
            if kind != "proof":
                lm = re.match(r"\s*\\label\{([^}]*)\}", text[i:])
                if lm:
                    last_stmt = lm.group(1)
                    statements.append((last_stmt, f))
                continue
            end = text.find(r"\end{proof}", i)
            body = text[i:end if end != -1 else len(text)]
            named = re.findall(r"\\ref\{([^}]*)\}", opt)
            proofs.append((named, last_stmt, body, f))
    labels = {s for s, _ in statements}
    # A proof belongs to the first *statement* its title names; a title that
    # names only non-statements (a Claim, a Caveat) does not steal the proof
    # from the statement it follows.  Attributing to a non-statement would
    # silently drop the proof's edges from the cycle and layer checks.
    edges, owner_of_proof = defaultdict(set), {}
    for named, last_stmt, body, f in proofs:
        owner = next((r for r in named if r in labels), last_stmt)
        if owner is None:
            continue
        owner_of_proof[owner] = f
        for r in re.findall(r"\\ref\{([^}]*)\}", body):
            if r != owner:
                edges[owner].add(r)
    edges = {a: {b for b in bs if b in labels} for a, bs in edges.items()}
    return labels, edges, set(owner_of_proof)


def find_cycle(labels, edges):
    WHITE, GREY, BLACK = 0, 1, 2
    color, stack = defaultdict(int), []

    def dfs(u):
        color[u] = GREY
        stack.append(u)
        for v in sorted(edges.get(u, ())):
            if color[v] == GREY:
                return stack[stack.index(v):] + [v]
            if color[v] == WHITE:
                c = dfs(v)
                if c:
                    return c
        stack.pop()
        color[u] = BLACK
        return None

    for u in sorted(labels):
        if color[u] == WHITE:
            c = dfs(u)
            if c:
                return c
    return None


def closure(edges, start):
    seen, frontier = set(), [start]
    while frontier:
        u = frontier.pop()
        for v in sorted(edges.get(u, ())):
            if v not in seen:
                seen.add(v)
                frontier.append(v)
    return seen


labels, edges, proved = parse()
n_edges = sum(len(v) for v in edges.values())

if "--closure" in sys.argv:
    target = sys.argv[sys.argv.index("--closure") + 1]
    if target not in labels:
        sys.exit(f"no such statement: {target}")
    c = closure(edges, target)
    print(f"{target} rests on {len(c)} statements:")
    for s in sorted(c):
        print("   ", s, "" if s in proved else "  [no proof here]")
    sys.exit(0)

if "--cluster" in sys.argv:
    members = sys.argv[sys.argv.index("--cluster") + 1:]
    print("induced subgraph:")
    for a in members:
        for b in sorted(edges.get(a, ())):
            if b in members:
                print(f"    {a} -> {b}")
    sys.exit(0)

cyc = find_cycle(labels, edges)
print(f"statements {len(labels)}, with proofs {len(proved)}, edges {n_edges}")
if cyc:
    print("FAIL  cycle: " + " -> ".join(cyc))
    sys.exit(1)
print("ok    proof-dependency graph is acyclic")
