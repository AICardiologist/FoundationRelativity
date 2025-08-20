#!/usr/bin/env bash
set -euo pipefail

# No-sorry guard for Paper 2 minimal target
# Ensures the minimal build remains sorry-free

echo "Checking for sorries in P2_Minimal target files..."

# Check only files reachable from the minimal target
FILES=(
    "Papers/P2_BidualGap/HB/OptionB/CorePure.lean"
    "Papers/P2_BidualGap/HB/OptionB/Instances.lean"
    "Papers/P2_BidualGap/P2_Minimal.lean"
)

FOUND_SORRY=0

for file in "${FILES[@]}"; do
    if [ -f "$file" ]; then
        # Detect 'sorry' as a term or as 'by sorry' (avoid matches in comments/strings)
        if grep -nE '(^|[^-])\bby\s+sorry\b|^\s*sorry\b' "$file" > /dev/null 2>&1; then
            echo "❌ Found 'sorry' statement in $file:"
            grep -nE '(^|[^-])\bby\s+sorry\b|^\s*sorry\b' "$file"
            FOUND_SORRY=1
        fi
    fi
done

if [ $FOUND_SORRY -eq 0 ]; then
    echo "✅ No sorries found in P2_Minimal target files"
    exit 0
else
    echo "❌ P2_Minimal target contains sorries!"
    exit 1
fi