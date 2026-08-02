#!/usr/bin/env python3
"""Inline a document and everything it \\input{}s into a single self-contained file.

The multi-file layout is what we work in; the standalone files are what get
sent out for review.  With no arguments, regenerates all three.

    python3 make_standalone.py                # all three
    python3 make_standalone.py csp-proof      # just one
"""
import re, subprocess, sys, datetime, pathlib

ROOT = pathlib.Path(__file__).parent
DOCUMENTS = {
    "csp-proof": "A corrected exposition of Zhuk's simplified CSP dichotomy proof.",
    "csp-audit": "Where that exposition departs from arXiv:2404.01080v2, and why.",
    "csp-blueprint": "The formalization companion: Lean representations and scope.",
}


def strip(text, name):
    # drop the TeX-root pragma; it is meaningless once inlined
    text = re.sub(r"(?m)^%!TeX root=.*\n", "", text)
    return f"%% ---------------------------------------------------------------- {name}\n{text.rstrip()}\n"


def inline(path, seen):
    if path.name in seen:
        sys.exit(f"cyclic input: {path.name}")
    seen.add(path.name)
    out = []
    for line in (ROOT / path).read_text().splitlines(keepends=True):
        m = re.match(r"\s*\\input\{([^}]+)\}\s*$", line)
        if m:
            out.append(inline(ROOT / m.group(1), seen))
        else:
            out.append(line)
    return strip("".join(out), path.name)


def rev():
    try:
        r = subprocess.run(["git", "rev-parse", "--short", "HEAD"], cwd=ROOT,
                           capture_output=True, text=True).stdout.strip()
        return r or "unknown"
    except Exception:
        return "unknown"


def build(job, blurb, revision, today):
    banner = (
        "%% =====================================================================\n"
        f"%%  {blurb}\n"
        "%%\n"
        "%%  GENERATED FILE -- do not edit.  Produced by make_standalone.py from\n"
        f"%%  {job}.tex and the per-section sources; edit those and regenerate.\n"
        "%%  Line references in a review should therefore be resolved back to the\n"
        "%%  section sources, whose names appear in the banners below.\n"
        f"%%  Generated from revision {revision} on {today}.\n"
        "%% =====================================================================\n\n"
    )
    out = ROOT / f"{job}-standalone.tex"
    out.write_text(banner + inline(ROOT / f"{job}.tex", set()))
    print(f"wrote {out.name}: {len(out.read_text().splitlines())} lines")


jobs = sys.argv[1:] or list(DOCUMENTS)
unknown = [j for j in jobs if j not in DOCUMENTS]
if unknown:
    sys.exit(f"unknown document(s): {', '.join(unknown)}; "
             f"expected one of {', '.join(DOCUMENTS)}")

revision, today = rev(), datetime.date.today().isoformat()
for job in jobs:
    build(job, DOCUMENTS[job], revision, today)
