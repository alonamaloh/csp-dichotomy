#!/usr/bin/env python3
"""Layer discipline for the proof paper.

`layers.tsv` assigns every theorem-like statement to a layer, L0 (foundations)
through L7 (complexity).  The intended discipline is Brady's: a layer is an
API, a statement in layer k may cite statements in layers <= k, and a citation
into a *higher* layer is a violation -- the analogue of a lower software layer
calling up into its consumers.

    python3 layercheck.py            # check; nonzero exit on violations
    python3 layercheck.py --api      # print each layer's exported interface
"""
import sys, pathlib
import depgraph as D

NAMES = {
    0: "foundations",
    1: "absorption",
    2: "congruences and bridges",
    3: "strong subuniverses",
    4: "instances",
    5: "main statements",
    6: "algorithm, hard half, assembly",
    7: "complexity",
}

def read_layers():
    layer = {}
    for line in pathlib.Path(__file__).with_name("layers.tsv").read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        lab, lay = line.split("\t")
        layer[lab] = int(lay)
    return layer

def main():
    layer = read_layers()
    labels, edges = D.labels, D.edges
    fail = 0

    unassigned = sorted(labels - set(layer))
    stale = sorted(set(layer) - labels)
    if unassigned:
        print(f"FAIL  statements without a layer ({len(unassigned)})")
        for s in unassigned:
            print("      ", s)
        fail = 1
    if stale:
        print(f"FAIL  layers.tsv entries naming no statement ({len(stale)})")
        for s in stale:
            print("      ", s)
        fail = 1

    up = [(a, b) for a, bs in edges.items() for b in bs
          if a in layer and b in layer and layer[b] > layer[a]]
    if up:
        print(f"FAIL  upward edges, proof cites a higher layer ({len(up)})")
        for a, b in sorted(up):
            print(f"       L{layer[a]} {a}  ->  L{layer[b]} {b}")
        fail = 1
    else:
        print("ok    no proof cites a higher layer")

    if "--api" in sys.argv:
        fan = {}
        for a, bs in edges.items():
            for b in bs:
                if a in layer and b in layer and layer[a] > layer[b]:
                    fan.setdefault(b, set()).add(a)
        for k in sorted(NAMES):
            members = sorted(s for s, l in layer.items() if l == k)
            api = sorted(s for s in members if s in fan)
            print(f"\nL{k} {NAMES[k]}: {len(members)} statements, "
                  f"{len(api)} exported")
            for s in api:
                print(f"    {s}   <- {', '.join(sorted(fan[s]))}")
    sys.exit(fail)

if __name__ == "__main__":
    main()
