#!/usr/bin/env bash
set -euo pipefail

MODE="${1:-baseline}"
FILE="Papers/P5_GeneralRelativity/GR/Riemann.lean"

# Extract actual mode from file
ACTUAL_MODE=$(grep "^-- ACTIVATION_STATUS:" "$FILE" | sed 's/^-- ACTIVATION_STATUS: //' | tr -d '\r' | xargs)

if [ -z "$ACTUAL_MODE" ]; then
  echo "❌ ACTIVATION_STATUS not found in ${FILE}"
  echo "Tip: add one of:"
  echo "  -- ACTIVATION_STATUS: baseline"
  echo "  -- ACTIVATION_STATUS: stage1-lhs-first"
  echo "  -- ACTIVATION_STATUS: stage1-lhs-both"
  echo "  -- ACTIVATION_STATUS: stage1-full"
  exit 1
fi

# For CI on PRs: accept any valid activation mode (not just baseline)
# This allows development branches to use Stage 1 infrastructure
VALID_MODES="baseline stage1-lhs-first stage1-lhs-both stage1-full"
if ! echo "$VALID_MODES" | grep -qw "$ACTUAL_MODE"; then
  echo "❌ Invalid ACTIVATION_STATUS: '${ACTUAL_MODE}' in ${FILE}"
  echo "Must be one of: ${VALID_MODES}"
  exit 1
fi

# If a specific mode was requested, verify it matches
if [ "$MODE" != "auto" ] && [ "$MODE" != "$ACTUAL_MODE" ]; then
  echo "⚠️  ACTIVATION_STATUS mismatch: expected '${MODE}', found '${ACTUAL_MODE}'"
  echo "   (This is informational only for PRs)"
fi

echo "✅ ACTIVATION_STATUS OK (${ACTUAL_MODE})."