#!/bin/sh
# Build gate.  Usage: ./check.sh <jobname-without-.tex>
# Fails on anything that a reader or a reviewer would call an error, including
# the classes that a bare "grep for '^! '" silently misses.
set -u
JOB="${1:-csp}"
pdflatex -interaction=nonstopmode "$JOB.tex" >/dev/null 2>&1
pdflatex -interaction=nonstopmode "$JOB.tex" >/dev/null 2>&1
LOG="$JOB.log"
fail=0
report() { n=$(printf '%s' "$2" | grep -c . ); [ -n "$2" ] && { echo "FAIL  $1 ($n)"; printf '%s\n' "$2" | sed 's/^/      /' | head -12; fail=1; } || echo "ok    $1"; }

report "TeX errors"            "$(grep '^! ' "$LOG")"
report "undefined references"  "$(grep -o "Reference \`[^']*' on page" "$LOG" | sort -u)"
report "multiply-defined"      "$(grep -o "Label \`[^']*' multiply defined" "$LOG" | sort -u)"
report "undefined citations"   "$(grep -o "Citation \`[^']*' on page" "$LOG" | sort -u)"
report "overfull boxes >10pt"  "$(grep -o 'Overfull \\hbox ([0-9.]*pt' "$LOG" | awk -F'[( ]' '$4+0>10' | sort -u)"
report "ref-inside-cite"   "$(grep -rn 'cite\[[^]]*\\ref' ch*.tex csp.tex preamble.tex)"

# Every \label must be defined exactly once across the sources of this document.
dups=$(grep -rho '\\label{[^}]*}' ch*.tex csp.tex | sort | uniq -d)
report "duplicate \\label in sources" "$dups"

[ "$fail" -eq 0 ] && echo "PASS" || echo "BUILD REJECTED"
exit "$fail"
