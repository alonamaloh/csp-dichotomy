#!/usr/bin/env python3
"""Inline csp.tex and everything it \input{}s into a single self-contained file.

The multi-file layout is what we work in; csp-standalone.tex is what gets sent
out for review.  Regenerate with `python3 make_standalone.py` after any edit.
"""
import re, subprocess, sys, datetime, pathlib

ROOT = pathlib.Path(__file__).parent
MAIN = ROOT / "csp.tex"
OUT = ROOT / "csp-standalone.tex"

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
            child = ROOT / m.group(1)
            out.append(inline(child, seen))
        else:
            out.append(line)
    return strip("".join(out), path.name)

try:
    rev = subprocess.run(["git", "rev-parse", "--short", "HEAD"], cwd=ROOT,
                         capture_output=True, text=True).stdout.strip() or "unknown"
except Exception:
    rev = "unknown"

banner = (
    "%% =====================================================================\n"
    "%%  A corrected exposition of Zhuk's simplified CSP dichotomy proof.\n"
    "%%\n"
    "%%  GENERATED FILE -- do not edit.  Produced by make_standalone.py from\n"
    "%%  csp.tex and the per-section sources; edit those and regenerate.\n"
    f"%%  Generated from revision {rev} on "
    f"{datetime.date.today().isoformat()}.\n"
    "%% =====================================================================\n\n"
)

OUT.write_text(banner + inline(MAIN, set()))
print(f"wrote {OUT.name}: {len(OUT.read_text().splitlines())} lines")
