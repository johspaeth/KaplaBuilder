#!/usr/bin/env bash
# The checks of .github/workflows/ci.yml, in the Linux container, on the live
# working tree. Stops at the first failure. Can be called from macOS.
# It does not test the merge with main, which CI does.
set -euo pipefail

if [[ ! -f /.dockerenv ]]; then
  exec "$(dirname "$0")/dev.sh" semantics/dev/ci.sh
fi

cd /workspace

# One lake process at a time. Close Lean files in any editor attached here.
if pgrep -x lake >/dev/null; then
  echo "ci.sh: lake is already running in this container; try again when it ends." >&2
  exit 1
fi

make check
lake check
shopt -s nullglob
for cfg in comparator/*.json; do
  echo "== comparator $cfg"
  lake comparator --config "$cfg"
done
echo "ci.sh: all checks passed"
