#!/usr/bin/env bash
# Axiom budget guard for Paper 3B
# Ensures all axioms are declared within namespace Ax blocks

set -euo pipefail

echo "🔍 Checking axiom namespace discipline..."

# Scan Lean sources in Paper 3B ProofTheory modules
files=$(git ls-files "Papers/P3_2CatFramework/P4_Meta/ProofTheory/*.lean" 2>/dev/null || find Papers/P3_2CatFramework/P4_Meta/ProofTheory -name "*.lean" 2>/dev/null || echo "")

if [ -z "$files" ]; then
  echo "⚠️  No ProofTheory files found to check"
  exit 0
fi

bad=0
for f in $files; do
  if [ -f "$f" ]; then
    awk '
      /^[[:space:]]*namespace[[:space:]]+Ax\b/ { depth++ }
      /^[[:space:]]*end[[:space:]]+Ax\b/       { if (depth>0) depth-- }
      /^[[:space:]]*axiom\b/ && depth==0 {
        print FILENAME ":" FNR ": axiom outside namespace Ax -> " $0
        bad=1
      }
      END { exit bad }
    ' "$f" || bad=1
  fi
done

if [[ $bad -ne 0 ]]; then
  echo "❌ Axioms found outside namespace Ax."
  echo "   All axioms must be declared within 'namespace Ax ... end Ax' blocks."
  exit 1
fi

echo "✅ Axiom namespace guard passed (all axioms inside namespace Ax)."

# Count total axioms and enforce budget
echo "📊 Counting total axioms..."
axiom_count=0
for f in $files; do
  if [ -f "$f" ]; then
    count=$(grep -c "^[[:space:]]*axiom\b" "$f" 2>/dev/null || true)
    if [ -z "$count" ]; then count=0; fi
    axiom_count=$((axiom_count + count))
  fi
done

MAX_AXIOMS=30  # 21 Paper 3B specific + 9 base theory axioms
echo "   Current axiom count: $axiom_count"
echo "   Maximum allowed: $MAX_AXIOMS"

if [[ $axiom_count -gt $MAX_AXIOMS ]]; then
  echo "❌ AXIOM BUDGET EXCEEDED!"
  echo "   The axiom count ($axiom_count) exceeds the budget of $MAX_AXIOMS."
  echo "   Future PRs must reduce axioms, not increase them."
  exit 1
fi

echo "✅ Axiom budget check passed ($axiom_count ≤ $MAX_AXIOMS)."

# Check for any sorry or admit (as proof terms, not in comments)
echo "🔍 Checking for sorries..."
# Look for sorry/admit as proof terms, not in comments or as part of words
if grep -r "^\s*sorry\s*$\|:=\s*sorry\|by\s*sorry\|^\s*admit\s*$\|:=\s*admit\|by\s*admit" Papers/P3_2CatFramework/P4_Meta/ProofTheory/*.lean 2>/dev/null; then
  echo "❌ Found sorry/admit instances!"
  echo "   No sorries are allowed in Paper 3B ProofTheory modules."
  exit 1
fi

echo "✅ No sorries found in ProofTheory modules."