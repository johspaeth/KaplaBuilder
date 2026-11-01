#!/usr/bin/env bash
# What a judge does after `make install`, checked end to end, with no API key:
#   1. `kapla check` gives the documented verdict on every example blueprint.
#   2. `kapla view` writes a page.
#   3. `make run` serves the site: the page, the gallery, and a plan from the
#      stand-in planner that stands and is accepted.
# Run it after `make install` (or `lake build`). Needs curl and python3.
# KAPLA_SMOKE_PORT=N serves on port N with `kapla serve --port N` instead of `make run` (8000).
set -euo pipefail
cd "$(dirname "$0")/.."
unset ANTHROPIC_API_KEY

kapla=.lake/build/bin/kapla
[[ -x $kapla ]] || { echo "::error::$kapla not found: run make install first"; exit 1; }
fail=0
bad() { echo "::error::$*"; fail=1; }

# expect EXIT FILE GREP_TEXT ARGS...: `kapla ARGS` exits with EXIT and prints GREP_TEXT.
expect() {
  local want=$1 text=$2; shift 2
  local out code=0
  out=$("$kapla" "$@" 2>&1) || code=$?
  if [[ $code != "$want" ]]; then bad "kapla $*: exit $code, expected $want"; echo "$out"
  elif ! grep -qF -- "$text" <<<"$out"; then bad "kapla $*: no line with \"$text\""; echo "$out"
  else echo "ok: kapla $*"; fi
}

robust="solid after every block, for 3.9 mm placement errors"
nominal="at the planned positions only"

echo "== example blueprints (web/examples/)"
expect 0 "$robust"  check web/examples/house.json
expect 0 "$robust"  check web/examples/duck.json
expect 0 "$nominal" check web/examples/spiral.json
expect 1 "at most 10 allowed" check web/examples/duck.json --max 10
expect 1 "not shown"          check web/examples/spiral.json --robust-only
known="house.json duck.json spiral.json"
for f in web/examples/*.json; do
  [[ " $known " == *" $(basename "$f") "* ]] || bad "$f has no expected verdict in scripts/smoke_test.sh"
done

out=$(mktemp -d)
expect 0 "wrote" view web/examples/house.json --out "$out/house"
[[ -s $out/house/index.html ]] || bad "kapla view wrote no index.html"

echo "== the website"
port=${KAPLA_SMOKE_PORT:-8000}
url=http://127.0.0.1:$port
# Something else on the port would answer for us: refuse instead of testing the wrong server.
if curl -s -o /dev/null "$url/"; then
  echo "::error::port $port is already in use; stop that server or set KAPLA_SMOKE_PORT"; exit 1
fi
if [[ -n ${KAPLA_SMOKE_PORT:-} ]]; then "$kapla" serve --port "$port" >"$out/serve.log" 2>&1 &
else make run >"$out/serve.log" 2>&1 & fi
server=$!
trap 'kill $server 2>/dev/null; pkill -P $server 2>/dev/null || true' EXIT
for _ in $(seq 1 60); do curl -sf -o /dev/null "$url/" && break; sleep 1; done
kill -0 $server 2>/dev/null || { cat "$out/serve.log"; echo "::error::the server stopped"; exit 1; }

code=$(curl -s -o "$out/index.html" -w '%{http_code}' "$url/")
[[ $code == 200 ]] && echo "ok: GET /" || bad "GET / gave $code"; cat "$out/serve.log"

entries=$(curl -sf "$url/gallery" | python3 -c 'import json,sys; print(" ".join(json.load(sys.stdin)["entries"]))') \
  || bad "GET /gallery failed"
[[ -n $entries ]] && echo "ok: GET /gallery: $entries" || bad "the gallery is empty"
for e in $entries; do
  curl -sf -o /dev/null "$url/gallery/$e" && echo "ok: GET /gallery/$e" || bad "GET /gallery/$e failed"
done

# The offline demo: the stand-in planner on the egg must give a plan that stands and is accepted.
model=$(curl -sf "$url/gallery/egg" | python3 -c 'import json,sys; print(json.dumps(json.load(sys.stdin)["model"]))')
curl -sf -X POST -H "Origin: $url" \
  -d "{\"planner\": \"stand-in tower (test only)\", \"blocks\": 20, \"model\": $model}" "$url/plan" \
  | python3 -c '
import json, sys
p = json.load(sys.stdin)["proposal"]
assert p["stands"] is True, "stands is not true"
assert p["score"]["accepted"] is True, "not accepted"
print("ok: POST /plan (stand-in tower on the egg): stands, accepted, score", p["score"]["scoreRounded"])
' || bad "POST /plan with the stand-in planner did not give a plan that stands and is accepted"

[[ $fail == 0 ]] && echo "smoke test: OK"
exit $fail
