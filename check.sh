#!/bin/sh
# Build gate.  Usage: ./check.sh [<jobname-without-.tex> ...]
# With no argument, checks all three documents.
#
# Fails on anything a reader or a reviewer would call an error, including the
# classes that a bare "grep for '^! '" silently misses.  The source list of a
# document is derived from the \input{} lines of its main file, so the
# duplicate-label and cross-document-\ref checks are exact rather than
# glob-approximate.
set -u

check_one() {
  JOB="$1"
  echo "=== $JOB"
  pdflatex -interaction=nonstopmode "$JOB.tex" >/dev/null 2>&1
  pdflatex -interaction=nonstopmode "$JOB.tex" >/dev/null 2>&1
  LOG="$JOB.log"
  fail=0
  report() {
    if [ -n "$2" ]; then
      n=$(printf '%s\n' "$2" | grep -c .)
      echo "FAIL  $1 ($n)"
      printf '%s\n' "$2" | sed 's/^/      /' | head -12
      fail=1
    else
      echo "ok    $1"
    fi
  }

  # The sources of this document: its main file plus everything it \input{}s.
  SRC=$(printf '%s\n' "$JOB.tex"; sed -n 's/^ *\\input{\([^}]*\)}.*/\1/p' "$JOB.tex")

  report "TeX errors"            "$(grep '^! ' "$LOG")"
  report "undefined references"  "$(grep -o "Reference \`[^']*' on page" "$LOG" | sort -u)"
  report "multiply-defined"      "$(grep -o "Label \`[^']*' multiply defined" "$LOG" | sort -u)"
  report "undefined citations"   "$(grep -o "Citation \`[^']*' on page" "$LOG" | sort -u)"
  report "overfull boxes >10pt"  "$(grep -o 'Overfull \\hbox ([0-9.]*pt' "$LOG" | awk -F'[( ]' '$4+0>10' | sort -u)"
  report "ref-inside-cite"       "$(grep -n 'cite\[[^]]*\\ref' $SRC 2>/dev/null)"

  # Every \label must be defined exactly once across this document's sources.
  report "duplicate \\label in sources" \
    "$(grep -rho '\\label{[^}]*}' $SRC 2>/dev/null | sort | uniq -d)"

  # Every \ref must resolve to a label defined in *this* document's sources.
  # A \ref to a label that exists only in another document is the failure mode
  # the three-way split introduces, and pdflatex reports it only as "undefined".
  defined=$(grep -rho '\\label{[^}]*}' $SRC 2>/dev/null | sed 's/\\label{\(.*\)}/\1/' | sort -u)
  used=$(grep -rho '\\\(ref\|autoref\|eqref\|ref\*\){[^}]*}' $SRC 2>/dev/null \
         | sed 's/.*{\(.*\)}/\1/' | sort -u)
  foreign=$(printf '%s\n' "$used" | while read -r r; do
              [ -n "$r" ] || continue
              printf '%s\n' "$defined" | grep -qxF "$r" || echo "$r"
            done)
  report 'ref to a label outside this document' "$foreign"

  # The proof paper must contain no repair markers, no source commentary, and
  # no material about a proof assistant.
  if [ "$JOB" = "csp-proof" ]; then
    report "repair markers in the proof paper" \
      "$(grep -n 'textbf{\[R\]}' $SRC 2>/dev/null)"
    report "source commentary in the proof paper" \
      "$(grep -n 'ZhukSimplified} writes\|ZhukSimplified} states\|the source writes\|the source says\|the source asserts\|the source does not\|the source omits' $SRC 2>/dev/null)"
    report "proof-assistant material in the proof paper" \
      "$(grep -n 'Lean\|Mathlib\|sorry-free\|texttt{sorry}\|ZhukLean\|typeclass\|formaliz' $SRC 2>/dev/null | grep -v '^preamble.tex:')"
  fi

  # Every \pkey{...} in the audit or blueprint must name a label the proof
  # paper actually defines.  These are the cross-document joins, and nothing
  # else checks them.
  if [ "$JOB" != "csp-proof" ] && [ -f csp-proof.tex ]; then
    psrc=$(printf '%s\n' "csp-proof.tex"; sed -n 's/^ *\\input{\([^}]*\)}.*/\1/p' csp-proof.tex)
    pdef=$(grep -rho '\\label{[^}]*}' $psrc 2>/dev/null | sed 's/\\label{\(.*\)}/\1/' | sort -u)
    pused=$(grep -rho '\\\(pkey\|inproof\){[^}]*}' $SRC 2>/dev/null \
            | sed 's/.*{\(.*\)}/\1/' | sed 's/\\brk//g' | grep ':' | sort -u)
    dangling=$(printf '%s\n' "$pused" | while read -r k; do
                 [ -n "$k" ] || continue
                 printf '%s\n' "$pdef" | grep -qxF "$k" || echo "$k"
               done)
    report 'pkey naming a label the proof paper does not define' "$dangling"
  fi

  [ "$fail" -eq 0 ] && echo "PASS  $JOB" || echo "BUILD REJECTED  $JOB"
  return "$fail"
}

# The proof paper's own proof-dependency graph must be acyclic.  This is not a
# LaTeX property, so it lives in its own parser; it is run once, not per-job.
depcheck() {
  out=$(python3 depgraph.py 2>&1) || { echo "$out"; return 1; }
  printf '%s\n' "$out" | sed 's/^/      /'
  return 0
}

rc=0
if [ "$#" -eq 0 ]; then
  set -- csp-proof csp-audit csp-blueprint
fi
for j in "$@"; do
  check_one "$j" || rc=1
done
case " $* " in
  *" csp-proof "*) echo "=== dependency graph"; depcheck || rc=1 ;;
esac
exit "$rc"
