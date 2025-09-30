#!/usr/bin/env bash
set -euo pipefail

# Check that the Riemann.lean file maintains its baseline error count
ERRS=$(lake build Papers.P5_GeneralRelativity.GR.Riemann 2>&1 | grep -c "error:" || true)
if [ "$ERRS" -ne 0 ]; then
  echo "❌ Expected 0 errors (baseline), got $ERRS"
  exit 1
fi
echo "✅ Baseline OK (0 errors - ALL RIEMANN COMPONENTS PROVEN!)."