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
        # Strip line comments and block-comment regions, then look for token 'sorry'
        # This is a lightweight filter; good enough for CI and our code style.
        stripped=$(awk '
            BEGIN { blk=0 }
            { line=$0 }
            # toggle block comments
            /\/\-/ { blk=1 }
            /-\// { blk=0; next }
            # drop line comments
            { gsub(/--.*/, "", line) }
            { if (blk==0) print line }
        ' "$file")
        
        if echo "$stripped" | grep -n -E '(^|[^A-Za-z])sorry([^A-Za-z]|$)' >/dev/null; then
            echo "❌ Found 'sorry' in $file (after stripping comments):"
            echo "$stripped" | grep -n -E '(^|[^A-Za-z])sorry([^A-Za-z]|$)'
            FOUND_SORRY=1
        fi
        
        # Also check for 'admit'
        if echo "$stripped" | grep -n -E '(^|[^A-Za-z])admit([^A-Za-z]|$)' >/dev/null; then
            echo "❌ Found 'admit' in $file (after stripping comments):"
            echo "$stripped" | grep -n -E '(^|[^A-Za-z])admit([^A-Za-z]|$)'
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