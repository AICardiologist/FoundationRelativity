#!/bin/bash

# Paper 1 Minimal Target Sorry Check
# Ensures that all files imported by P1_Minimal contain no sorries

set -e

echo "🔍 Checking Paper 1 minimal target for sorries..."

# Files that are part of the P1 minimal target
FILES=(
    "Papers/P1_GBC/RankOneToggle/Projection.lean"
    # Add more files here as they become sorry-free
    # "Papers/P1_GBC/RankOneToggle/Toggle.lean"
    # "Papers/P1_GBC/RankOneToggle/ShermanMorrison.lean"
)

FOUND_SORRY=0

for file in "${FILES[@]}"; do
    if [ -f "$file" ]; then
        # Check for 'sorry' in the file (excluding comments)
        if grep -q "^[^/]*\bsorry\b" "$file" 2>/dev/null; then
            echo "❌ Found 'sorry' in $file"
            grep -n "^[^/]*\bsorry\b" "$file" | head -5
            FOUND_SORRY=1
        else
            echo "✅ $file is sorry-free"
        fi
    else
        echo "⚠️  File not found: $file"
    fi
done

if [ $FOUND_SORRY -eq 1 ]; then
    echo ""
    echo "❌ Paper 1 minimal target contains sorries!"
    exit 1
else
    echo ""
    echo "✅ Paper 1 minimal target is sorry-free!"
    exit 0
fi