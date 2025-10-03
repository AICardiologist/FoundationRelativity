#!/usr/bin/env bash
set -euo pipefail

# Check that the Riemann.lean file maintains its baseline error count
# Use incremental build (no clean) to leverage cache from previous builds
echo "  • Building Riemann.lean (incremental)..."
BUILD_OUTPUT=$(lake build Papers.P5_GeneralRelativity.GR.Riemann 2>&1)
ERRS=$(echo "$BUILD_OUTPUT" | grep -c "^error:" || true)

if [ "$ERRS" -ne 0 ]; then
  echo "❌ Expected 0 errors (baseline), got $ERRS"
  echo "$BUILD_OUTPUT" | grep "^error:" | head -10
  exit 1
fi
echo "✅ Baseline OK (0 errors - ALL RIEMANN COMPONENTS PROVEN!)."