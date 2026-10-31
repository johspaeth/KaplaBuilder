#!/usr/bin/env bash
# Each component may import only KaplaCore and itself (docs/WORKSPLIT.md §2).
# app/ and specs/ may import anything. KaplaCore may import no other component.
set -euo pipefail
cd "$(dirname "$0")/.."

fail=0
check() { # folder ownLib
  local dir=$1 own=$2
  while IFS= read -r hit; do
    lib=$(sed -E 's/.*import[[:space:]]+(Kapla[A-Za-z]+).*/\1/' <<<"${hit#*:*:}")
    if [[ "$lib" != "KaplaCore" && "$lib" != "$own" ]]; then
      echo "::error::$hit  ($own must not import $lib; only KaplaCore and itself)"
      fail=1
    fi
  done < <(grep -rnE '^[[:space:]]*import[[:space:]]+Kapla' "$dir" --include='*.lean' || true)
}
check core      KaplaCore
check physics   KaplaPhysics
check semantics KaplaSemantics
check planner   KaplaPlanner
check web       KaplaWeb

[[ $fail == 0 ]] && echo "import rules: OK"
exit $fail
