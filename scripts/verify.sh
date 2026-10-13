#!/usr/bin/env bash
#
# Verification suite for the GeoDa Lean project.
#
#   1. `lake build` — type-check every definition, theorem and test.
#   2. no `sorry` / `admit` anywhere in the sources.
#   3. axiom audit — every main theorem must depend only on the standard
#      Lean/Mathlib axioms `propext`, `Classical.choice`, `Quot.sound`.
#
# Exits non-zero on the first failure, so it can be used directly as a CI step.
set -euo pipefail
cd "$(dirname "$0")/.."

EXPECTED_AXIOMS='[propext, Classical.choice, Quot.sound]'
EXPECTED_COUNT=12

echo "==> 1/3  lake build"
lake build

echo "==> 2/3  no sorry / admit"
if grep -rnE '(^|[^A-Za-z_])(sorry|admit)([^A-Za-z_]|$)' --include='*.lean' GeoDa.lean GeoDa GeoDaTest.lean GeoDaTest \
     | grep -v '^\S*:[0-9]*: *--' | grep -v 'sorryAx'; then
  echo "FAIL: found 'sorry' or 'admit' in the sources" >&2
  exit 1
fi
echo "     ok: no sorry/admit in any proof"

echo "==> 3/3  axiom audit"
audit="$(lake env lean GeoDaTest/Axioms.lean 2>&1 | grep 'depends on axioms' || true)"
if [ -z "$audit" ]; then
  echo "FAIL: the axiom audit produced no output" >&2
  exit 1
fi
count="$(printf '%s\n' "$audit" | grep -c 'depends on axioms' || true)"
if [ "$count" -ne "$EXPECTED_COUNT" ]; then
  echo "FAIL: expected $EXPECTED_COUNT audited theorems, got $count" >&2
  exit 1
fi
offending="$(printf '%s\n' "$audit" | grep -vF "depends on axioms: $EXPECTED_AXIOMS" || true)"
if [ -n "$offending" ]; then
  echo "FAIL: theorem(s) depend on unexpected axioms:" >&2
  printf '%s\n' "$offending" >&2
  exit 1
fi
printf '%s\n' "$audit"
echo "     ok: all $count theorems depend only on $EXPECTED_AXIOMS"

echo
echo "VERIFICATION SUCCEEDED"
