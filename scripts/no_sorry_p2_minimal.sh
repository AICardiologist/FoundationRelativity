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
        # Strip line comments and nested block comments, then look for token 'sorry'
        # Lightweight and portable: handles inline and nested /- ... -/
        # NOTE: nested block comments are rare in this repo; this filter handles basic nesting
        stripped=$(awk '
            BEGIN { depth=0 }
            {
                line=$0
                # remove line comments
                sub(/--.*/, "", line)
                out=""
                i=1
                while (i <= length(line)) {
                    two = substr(line,i,2)
                    if (two == "/-") { depth++; i+=2; continue }
                    if (two == "-/") { if (depth>0) depth--; i+=2; continue }
                    if (depth == 0) { out = out substr(line,i,1) }
                    i++
                }
                if (length(out) > 0) print out
            }
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