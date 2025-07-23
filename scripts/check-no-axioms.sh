#!/usr/bin/env bash
set -euo pipefail
# Greps the exported JSON for any axioms other than `Classical.choice` & `propext`
lake build --no-build-lib --lean-args="--export-format=json" > /dev/null
if grep -R "\"kind\":\"axiom\"" .lake/build/export | \
   grep -v -E 'Classical\.choice|propext' ; then
  echo "🚨  Unexpected axiom found."; exit 1
fi
echo "✓  No unexpected axioms."