#!/usr/bin/env bash
# Fails unless every checked theorem depends only on Lean's three standard axioms.
set -euo pipefail
out=$(lake env lean scripts/Axioms.lean 2>&1)
echo "$out"
expected="depends on axioms: [propext, Classical.choice, Quot.sound]"
n=$(grep -c "depends on axioms" <<<"$out" || true)
ok=$(grep -cF "$expected" <<<"$out" || true)
want=$(grep -c "^#print axioms" scripts/Axioms.lean)
if [ "$n" -ne "$want" ] || [ "$ok" -ne "$want" ]; then
  echo "Axiom check FAILED ($ok of $want theorems use only the standard axioms)." >&2
  exit 1
fi
echo "Axiom check passed: $ok of $want theorems use only propext, Classical.choice, Quot.sound."
