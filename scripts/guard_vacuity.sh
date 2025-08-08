#!/bin/bash
# Guard against vacuity regressions in Paper 3 framework
set -euo pipefail

paths="Papers/P3_2CatFramework"
excludes="--exclude-dir=communications --exclude-dir=documentation --exclude-dir=expert-session --exclude-dir=.lake --exclude-dir=build --exclude='*.md'"
includes="--include=*.lean"

echo "Checking for vacuity regressions in $paths (excluding docs)..."

# Trivially true/false propositions
if grep -a -R -n $includes $excludes -E '\: *Prop *:= *(True|False)' $paths; then
  echo "❌ ERROR: Found trivial propositions."
  exit 1
fi

# Vacuous implications from empty placeholders
if grep -a -R -n $includes $excludes -E \
   '(AssocHolds|UnitorHolds|CategoricalObstruction|PentagonHolds|WitnessElimination|BiCatCoherence) *(→|->)' \
   $paths; then
  echo "⚠️  WARNING: Found implications from empty inductives - verify non-vacuity."
fi

# Check CategoricalObstruction remains non-trivial (should have no constructors)
if grep -a -R -n $includes $excludes -E 'CategoricalObstruction.*where|CategoricalObstruction.*:=.*mk' $paths; then
  echo "❌ ERROR: CategoricalObstruction has constructors - should be empty inductive."
  exit 1
fi

echo "✅ Vacuity guard passed."