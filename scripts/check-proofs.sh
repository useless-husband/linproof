#!/usr/bin/env bash
# Proof hygiene: no sorry/admit/native_decide/axiom in the verified library, no partial or
# unsafe definitions in it, a clean build, and only Lean's standard axioms behind the main
# theorems. Run from the repository root.
set -euo pipefail

fail=0

# 1. Forbidden keywords in the Lean library (comments included, to be strict).
if grep -nE '\b(sorry|admit|native_decide)\b' Linproof/*.lean Linproof.lean; then
  echo "error: sorry/admit/native_decide found"; fail=1
fi
if grep -nE '^\s*(axiom|unsafe|partial|@\[implemented_by|@\[extern)' Linproof/*.lean Linproof.lean; then
  echo "error: axiom/unsafe/partial/implemented_by/extern declaration found in the library"; fail=1
fi
if grep -nE 'set_option\s+debug\.|skipKernelTC' Linproof/*.lean Linproof.lean; then
  echo "error: a debug option that weakens checking is set in the library"; fail=1
fi

# 2. The build must not report any use of sorry.
log=$(mktemp)
lake build 2>&1 | tee "$log"
if grep -qE "declaration uses .sorry." "$log"; then
  echo "error: the build reports a declaration that uses sorry"; fail=1
fi
rm -f "$log"

# 3. Axioms of the main theorems.
out=$(lake env lean scripts/axioms.lean)
echo "$out"
n=$(printf '%s\n' "$out" | grep -c "depends on axioms" || true)
if [ "$n" -ne 9 ]; then
  echo "error: expected 9 axiom reports, got $n"; fail=1
fi
bad=$(printf '%s\n' "$out" | grep "depends on axioms" \
  | sed -E 's/.*depends on axioms: \[(.*)\]/\1/' | tr ',' '\n' | tr -d ' ' \
  | grep -vxE 'propext|Classical\.choice|Quot\.sound' || true)
if [ -n "$bad" ]; then
  echo "error: non-standard axioms: $bad"; fail=1
fi
if printf '%s\n' "$out" | grep -q "does not depend on any axioms\|sorryAx"; then
  if printf '%s\n' "$out" | grep -q sorryAx; then echo "error: sorryAx"; fail=1; fi
fi

if [ "$fail" -ne 0 ]; then exit 1; fi
echo "proof checks passed"
