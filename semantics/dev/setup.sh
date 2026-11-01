#!/usr/bin/env bash
# Run once per clone: git hooks are not versioned, so this installs the guard.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
hooks="$(git -C "$here" rev-parse --git-path hooks)"
[[ "$hooks" = /* ]] || hooks="$here/$hooks"
mkdir -p "$hooks"
cp "$here/pre-commit" "$hooks/pre-commit"
chmod +x "$hooks/pre-commit"
echo "installed $hooks/pre-commit"
