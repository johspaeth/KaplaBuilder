#!/usr/bin/env bash
# Fails if the soundness path uses any axiom beyond Lean's standard three.
set -euo pipefail
out=$(lake env lean scripts/AxiomAudit.lean 2>&1)
echo "$out"
bad=$(echo "$out" | grep -oE "[A-Za-z_.]+" | grep -E "sorryAx|ofReduceBool|ofReduceNat|trustCompiler" || true)
if [ -n "$bad" ]; then echo "axiom audit FAILED: $bad"; exit 1; fi
if echo "$out" | grep -q "error"; then echo "axiom audit FAILED (errors)"; exit 1; fi
# every line must mention only the allowed axioms
extra=$(echo "$out" | sed -n 's/.*depends on axioms: \[\(.*\)\]/\1/p' | tr ',' '\n' | tr -d ' ' \
  | grep -vE '^(propext|Classical.choice|Quot.sound)$' || true)
if [ -n "$extra" ]; then echo "axiom audit FAILED, unexpected axioms: $extra"; exit 1; fi
echo "axiom audit passed"
