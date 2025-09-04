#!/usr/bin/env bash
set -euo pipefail
echo "[no_sorry_p3] Scanning Paper 3 framework..."

# Check all core Paper 3 modules (excluding tests and archives)  
# Using \b for word boundary to match sorry as a tactic, not in comments
if grep -r "\bsorry\b" Papers/P3_2CatFramework --include="*.lean" \
               --exclude-dir=test --exclude-dir=archive 2>/dev/null | grep -v "sorry-free"; then
  echo "[no_sorry_p3] ❌ Found sorries in Paper 3 framework"
  exit 1
fi

echo "[no_sorry_p3] ✅ No sorries found in Paper 3 framework"