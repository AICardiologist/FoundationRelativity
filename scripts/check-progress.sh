#!/usr/bin/env bash
# Simple progress tracker for FoundationRelativity Phase 4-6 work
# Created: October 18, 2025
# Purpose: Track sorry and axiom counts during commit

set -euo pipefail

RIEMANN_FILE="Papers/P5_GeneralRelativity/GR/Riemann.lean"

# Count sorries and axioms
# Note: Using || true to avoid pipefail issues when grep finds no matches
SORRY_COUNT=$(grep "sorry" "$RIEMANN_FILE" | wc -l | tr -d ' ' || true)
AXIOM_COUNT=$(grep "^axiom " "$RIEMANN_FILE" | wc -l | tr -d ' ' || true)

echo ""
echo "📊 Progress: $SORRY_COUNT sorries, $AXIOM_COUNT axioms"

if [ "$AXIOM_COUNT" -gt 0 ]; then
  echo "⚠️  Warning: Axioms detected! Target is 0."
  exit 1
fi

if [ "$SORRY_COUNT" -eq 0 ] && [ "$AXIOM_COUNT" -eq 0 ]; then
  echo "🎉 Perfect! All proven!"
elif [ "$SORRY_COUNT" -lt 20 ]; then
  echo "🎯 Almost there! Less than 20 sorries remaining."
elif [ "$SORRY_COUNT" -lt 25 ]; then
  echo "🎯 Good progress! Working toward Phases 4-6 completion."
fi

echo ""
