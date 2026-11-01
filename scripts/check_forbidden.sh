#!/usr/bin/env bash
# Reject escape hatches in code that is supposed to be proven (CLAUDE.md §7).
# specs/ is skipped for `sorry`: spec statements are left unproven on purpose. The
# physics rules in specs/KaplaSpecs/PhysicsRules/ are definitions, so they are checked.
# The build (--fail-level=warning) and `lake check` catch most of these too;
# this grep gives an early, readable error. Words inside comments also count:
# rephrase the comment.
set -euo pipefail
cd "$(dirname "$0")/.."

code_dirs=(core physics semantics planner web app)
fail=0
report() { # pattern message dirs...
  local pat=$1 msg=$2; shift 2
  local hits
  hits=$(grep -rnwE "$pat" "$@" --include='*.lean' || true)
  if [[ -n "$hits" ]]; then
    while IFS= read -r h; do echo "::error::$h  ($msg)"; done <<<"$hits"
    fail=1
  fi
}
report 'sorry|admit'            'unfinished proof'                       "${code_dirs[@]}" specs/KaplaSpecs/PhysicsRules
report 'axiom'                  'new axiom: use an opaque with a contract' "${code_dirs[@]}" specs
report 'native_decide'          'adds a compiler axiom; agree with the team first' "${code_dirs[@]}" specs
report 'debug\.skipKernelTC'    'skips the kernel check'                 "${code_dirs[@]}" specs
report 'maxHeartbeats 0'        'unbounded heartbeats'                   "${code_dirs[@]}" specs
report 'implemented_by|extern'  'swaps the compiled code; agree with the team first' "${code_dirs[@]}" specs
report 'unsafe'                 'unsafe code; agree with the team first' "${code_dirs[@]}" specs

[[ $fail == 0 ]] && echo "forbidden words: OK"
exit $fail
