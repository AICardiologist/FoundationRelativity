#!/usr/bin/env bash
set -euo pipefail
echo "[no_sorry_p3] scanning..."
if grep -R --line-number --fixed-strings '\bsorry\b' Papers/P3_2CatFramework \
  | grep -v '/test/' ; then
  echo "[no_sorry_p3] ❌ found sorries in Paper 3 scope"
  exit 1
fi
echo "[no_sorry_p3] ✅ no sorries found in Paper 3 scope"