#!/usr/bin/env bash
# Fails unless every theorem listed in scripts/axioms.txt depends only on Lean's three standard
# axioms. The checking file is generated outside the repository, because Palomar requires every
# `.lean` file in the repository to be a module.
set -euo pipefail
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
{
  echo "import FormalConjecturesCheck"
  echo "import RegularPrimesCheck"
  echo "import Erdos291Check"
  sed 's/^/#print axioms /' scripts/axioms.txt
} > "$tmp/Axioms.lean"
out=$(lake env lean "$tmp/Axioms.lean" 2>&1)
echo "$out"
expected="depends on axioms: [propext, Classical.choice, Quot.sound]"
n=$(grep -c "depends on axioms" <<<"$out" || true)
ok=$(grep -cF "$expected" <<<"$out" || true)
want=$(grep -c . scripts/axioms.txt)
if [ "$n" -ne "$want" ] || [ "$ok" -ne "$want" ]; then
  echo "Axiom check FAILED ($ok of $want theorems use only the standard axioms)." >&2
  exit 1
fi
echo "Axiom check passed: $ok of $want theorems use only propext, Classical.choice, Quot.sound."
