#!/usr/bin/env bash
set -euo pipefail

# No-sorry guard for Paper 1 minimal target
# Ensures the P1 minimal build remains sorry-free

echo "Checking for sorries in P1_Minimal target files..."

# Check only files reachable from the P1 minimal target
# Currently only Core.lean is imported, add more as they become sorry-free
FILES=(
    "Papers/P1_GBC/P1_Minimal.lean"
    "Papers/P1_GBC/Core.lean"
    # Future additions when sorry-free:
    # "Papers/P1_GBC/RankOneToggle/Projection.lean"
    # "Papers/P1_GBC/RankOneToggle/Toggle.lean"
    # "Papers/P1_GBC/RankOneToggle/ShermanMorrison.lean"
    # "Papers/P1_GBC/RankOneToggle/Resolvent.lean"
    # "Papers/P1_GBC/RankOneToggle/Spectrum.lean"
    # "Papers/P1_GBC/RankOneToggle/Fredholm.lean"
)

FOUND_SORRY=0

for file in "${FILES[@]}"; do
    if [ -f "$file" ]; then
        # Strip line comments and nested block comments, then look for token 'sorry'
        # Lightweight and portable: handles inline and nested /- ... -/
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
    echo "✅ No sorries found in P1_Minimal target files"
    exit 0
else
    echo "❌ P1_Minimal target contains sorries!"
    exit 1
fi