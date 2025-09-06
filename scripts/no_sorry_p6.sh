#!/bin/bash

# No-sorry verification script for Paper 6: Heisenberg Uncertainty Principle
# Ensures all Paper 6 modules are sorry-free

set -e

echo "[Paper 6 No-Sorry Guard] Checking Heisenberg uncertainty modules..."

# Check main Axioms modules
echo "Checking Papers/P6_Heisenberg/Axioms/*.lean ..."
# Look for actual sorry statements (not in comments) - pattern: sorry as a standalone statement
if rg '^\s*sorry\s*$|:=\s*sorry\s*$|\bby\s+sorry\s*$' Papers/P6_Heisenberg/Axioms/ --glob "*.lean" --no-heading --line-number; then
    echo "❌ Found sorry in Paper 6 axioms modules!"
    exit 1
fi

# Check HUP analysis modules  
echo "Checking Papers/P6_Heisenberg/HUP/*.lean ..."
if rg '^\s*sorry\s*$|:=\s*sorry\s*$|\bby\s+sorry\s*$' Papers/P6_Heisenberg/HUP/ --glob "*.lean" --no-heading --line-number; then
    echo "❌ Found sorry in Paper 6 HUP modules!"
    exit 1
fi

# Check smoke test
echo "Checking Papers/P6_Heisenberg/Smoke.lean ..."
if rg '^\s*sorry\s*$|:=\s*sorry\s*$|\bby\s+sorry\s*$' Papers/P6_Heisenberg/Smoke.lean --no-heading --line-number; then
    echo "❌ Found sorry in Paper 6 smoke test!"
    exit 1
fi

echo "✓ No sorry found in Paper 6 (Heisenberg) modules"
echo "✓ Paper 6 sorry-free verification passed"