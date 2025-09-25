#!/usr/bin/env bash
set -euo pipefail

# Mode-aware budget checker for activation
# Tracks unsolved goals (UG) and other errors (OE) separately

# Get the current activation mode
MODE="$(grep "^-- ACTIVATION_STATUS:" Papers/P5_GeneralRelativity/GR/Riemann.lean | \
        sed 's/^-- ACTIVATION_STATUS:\s*//' | tr -d ' ' | head -1)"

if [ -z "${MODE:-}" ]; then
  MODE="baseline"
fi

# Build and count errors
BUILD_OUTPUT=$(lake build Papers.P5_GeneralRelativity.GR.Riemann 2>&1 || true)
UG=$(echo "$BUILD_OUTPUT" | grep -c "unsolved goals" || true)
TOTAL_ERR=$(echo "$BUILD_OUTPUT" | grep -c "error:" || true)
OE=$((TOTAL_ERR - UG))

echo "Mode: $MODE"
echo "Unsolved goals: $UG"
echo "Other errors: $OE"
echo "Total errors: $TOTAL_ERR"

# Define thresholds per mode
case "$MODE" in
  baseline)
    MAX_UG=51
    MAX_OE=2
    ;;
  stage1-lhs-first)
    MAX_UG=48
    MAX_OE=12
    ;;
  stage1-lhs-both)
    MAX_UG=45  # Current achievement
    MAX_OE=10  # Current other errors
    ;;
  stage1-full)
    MAX_UG=40
    MAX_OE=15
    ;;
  *)
    echo "❌ Unknown activation mode: $MODE"
    exit 1
    ;;
esac

# Check against thresholds
if [ "$UG" -gt "$MAX_UG" ]; then
  echo "❌ Unsolved goals ($UG) exceeds budget ($MAX_UG)"
  exit 1
fi

if [ "$OE" -gt "$MAX_OE" ]; then
  echo "❌ Other errors ($OE) exceeds budget ($MAX_OE)"
  exit 1
fi

echo "✅ Within budget (UG: $UG ≤ $MAX_UG, OE: $OE ≤ $MAX_OE)"