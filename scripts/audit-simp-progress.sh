#!/usr/bin/env bash
set -euo pipefail

echo "▶ Audit: no 'simp made no progress' (Riemann.lean)"
if lake build Papers.P5_GeneralRelativity.GR.Riemann 2>&1 | grep -q "simp.*made no progress"; then
  echo "  ❌ Found 'simp made no progress' occurrences"
  exit 1
else
  echo "  ✅ None found"
fi
