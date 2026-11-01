#!/usr/bin/env bash
# Each component may import only KaplaCore and itself (docs/WORKSPLIT.md §2).
# app/ and specs/ may import anything. KaplaCore may import no other component.
# Exception: physics/ may also import the human-owned physics rules in
# specs/KaplaSpecs/PhysicsRules/ (the definitions its theorems are about). Those rule
# files may import only KaplaCore and each other, never the engine or its proofs.
set -euo pipefail
cd "$(dirname "$0")/.."

fail=0
check() { # folder ownLib [allowed module prefix]
  local dir=$1 own=$2 extra=${3:-}
  while IFS= read -r hit; do
    mod=$(sed -E 's/.*import[[:space:]]+(Kapla[A-Za-z0-9_.]+).*/\1/' <<<"${hit#*:*:}")
    lib=${mod%%.*}
    if [[ "$lib" == "KaplaCore" || "$lib" == "$own" ]]; then continue; fi
    if [[ -n "$extra" && "$mod" == "$extra".* ]]; then continue; fi
    echo "::error::$hit  ($dir must not import $mod; only KaplaCore and itself${extra:+, plus $extra.*})"
    fail=1
  done < <(grep -rnE '^[[:space:]]*import[[:space:]]+Kapla' "$dir" --include='*.lean' || true)
}
check core      KaplaCore
check physics   KaplaPhysics KaplaSpecs.PhysicsRules
check semantics KaplaSemantics
check planner   KaplaPlanner
check web       KaplaWeb
# The physics rules are trusted: they must not depend on the engine or the proofs.
check specs/KaplaSpecs/PhysicsRules KaplaCore KaplaSpecs.PhysicsRules

[[ $fail == 0 ]] && echo "import rules: OK"
exit $fail
