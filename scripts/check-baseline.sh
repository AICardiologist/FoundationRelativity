#!/usr/bin/env bash
set -euo pipefail

# Check that the Riemann.lean file maintains its baseline error count
ERRS=$(lake build Papers.P5_GeneralRelativity.GR.Riemann 2>&1 | grep -c "error:" || true)
if [ "$ERRS" -ne 50 ]; then
  echo "❌ Expected 50 errors (baseline), got $ERRS"
  exit 1
fi
echo "✅ Baseline OK (50 errors)."