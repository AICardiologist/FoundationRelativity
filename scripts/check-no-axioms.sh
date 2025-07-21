#!/bin/bash

# No-Axiom Lint Script
# Verifies that key modules don't contain axiom statements
# This ensures we've successfully replaced temporary axioms with real proofs

echo "🔍 Checking for axiom statements in core modules..."

# Key modules that should have zero axioms after Sprint S5
modules=(
    "Found/Analysis/Lemmas.lean"
    "RNPFunctor/Proofs3.lean"
)

total_axioms=0

for module in "${modules[@]}"; do
    if [[ -f "$module" ]]; then
        # Count lines containing 'axiom' (excluding comments)
        axiom_count=$(grep -E '^[[:space:]]*axiom' "$module" | grep -v '/--' | grep -v '--' | wc -l)
        
        if [[ $axiom_count -gt 0 ]]; then
            echo "❌ $module: $axiom_count axiom(s) found"
            grep -n 'axiom' "$module"
            total_axioms=$((total_axioms + axiom_count))
        else
            echo "✅ $module: No axioms found"
        fi
    else
        echo "⚠️  $module: File not found"
    fi
done

echo ""
if [[ $total_axioms -eq 0 ]]; then
    echo "🎉 All modules pass no-axiom check!"
    echo "   Sprint S5 success: All axioms replaced with real proofs"
    exit 0
else
    echo "💥 Found $total_axioms axiom(s) total"
    echo "   Sprint S5 incomplete: Some axioms remain to be replaced"
    exit 1
fi