#!/usr/bin/env bash
set -euo pipefail

echo "[verify-no-sorry] Checking sorry-free stable modules only ..."

# Check only the specific modules that should be sorry-free
SORRY_FREE_MODULES=(
  "Papers/P3_2CatFramework/Paper3A_Main.lean"
  "Papers/P3_2CatFramework/Paper3B_Main.lean" 
  "Papers/P3_2CatFramework/Phase1_Simple.lean"
  "Papers/P3_2CatFramework/Phase2_UniformHeight.lean"
  "Papers/P3_2CatFramework/Phase2_API.lean"
  "Papers/P3_2CatFramework/Phase3_Positive.lean"
  "Papers/P4_SpectralGeometry/Smoke.lean"
  "Papers/P4_SpectralGeometry/Spectral"
)

FOUND_SORRY=false
for module in "${SORRY_FREE_MODULES[@]}"; do
  if [[ -e "$module" ]]; then
    echo "Checking $module ..."
    if grep -r --line-number -E "\bsorry\b" --include="*.lean" "$module" | grep -v -E "^[^:]*:[^:]*:.*--.*sorry" | grep -v -E "no.*sorry|sorry.*free"; then
      echo "ERROR: Found 'sorry' in $module!"
      FOUND_SORRY=true
    fi
  fi
done

if $FOUND_SORRY; then
  exit 1
fi

echo "✓ No sorry found in stable modules"