#!/usr/bin/env bash
set -euo pipefail
echo "[no_sorry_p3a] Scanning Paper 3A core modules..."

# Check core Paper 3A modules only
# Filter out comment lines and "sorry-free" mentions
MODULES=(
  "Papers/P3_2CatFramework/Paper3A_Main.lean"
  "Papers/P3_2CatFramework/P4_Meta/FT_UCT_MinimalSurface.lean"
  "Papers/P3_2CatFramework/P4_Meta/DCw_Frontier.lean"
  "Papers/P3_2CatFramework/P4_Meta/StoneWindow_SupportIdeals.lean"
)

for module in "${MODULES[@]}"; do
  if [ -f "$module" ] && grep "\bsorry\b" "$module" 2>/dev/null | grep -v "sorry-free" | grep -v "^--"; then
    echo "[no_sorry_p3a] ❌ Found sorries in $module"
    exit 1
  fi
done

echo "[no_sorry_p3a] ✅ No sorries found in Paper 3A core modules"