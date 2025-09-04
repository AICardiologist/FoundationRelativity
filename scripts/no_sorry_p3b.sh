#!/usr/bin/env bash
set -euo pipefail
echo "[no_sorry_p3b] Scanning Paper 3B core modules..."

# Check core Paper 3B modules only
# Filter out comment lines and "sorry-free" mentions
MODULES=(
  "Papers/P3_2CatFramework/Paper3B_Main.lean"
  "Papers/P3_2CatFramework/P4_Meta/Meta_Ladders.lean"
  "Papers/P3_2CatFramework/P4_Meta/IndependenceRegistry.lean"  
  "Papers/P3_2CatFramework/P4_Meta/PartV_Collision.lean"
)

for module in "${MODULES[@]}"; do
  if [ -f "$module" ] && grep "\bsorry\b" "$module" 2>/dev/null | grep -v "sorry-free" | grep -v "^--"; then
    echo "[no_sorry_p3b] ❌ Found sorries in $module"
    exit 1
  fi
done

echo "[no_sorry_p3b] ✅ No sorries found in Paper 3B core modules"