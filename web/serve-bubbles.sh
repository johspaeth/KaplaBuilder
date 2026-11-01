#!/usr/bin/env bash
# Show bubble models in the browser, on this computer only. Usage: web/serve-bubbles.sh [PORT]
set -euo pipefail
cd "$(dirname "$0")/.."

port=${1:-8000}
out=.lake/bubble-view
lake build KaplaWeb
mkdir -p "$out"
lake env lean --run web/KaplaWeb/Dev/BubblePage.lean "$out/index.html"
cp semantics/fixtures/targets/*.json web/examples/bubbles/*.json "$out/"

echo "Open http://localhost:$port/?bubbles=egg.json&height=30"
exec python3 -m http.server "$port" --bind 127.0.0.1 --directory "$out"
