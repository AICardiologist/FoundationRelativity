#!/usr/bin/env bash
set -euo pipefail

MODE="${1:-baseline}"
FILE="Papers/P5_GeneralRelativity/GR/Riemann.lean"

if ! grep -q "^-- ACTIVATION_STATUS: ${MODE}$" "$FILE"; then
  echo "❌ ACTIVATION_STATUS mismatch. Expected: '${MODE}' in:"
  echo "    ${FILE}"
  echo "Tip: set it to one of:"
  echo "  -- ACTIVATION_STATUS: baseline"
  echo "  -- ACTIVATION_STATUS: stage1-lhs-first"
  echo "  -- ACTIVATION_STATUS: stage1-lhs-both"
  echo "  -- ACTIVATION_STATUS: stage1-full"
  exit 1
fi

echo "✅ ACTIVATION_STATUS OK (${MODE})."