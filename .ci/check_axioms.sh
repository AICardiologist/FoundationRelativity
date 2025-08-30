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

echo "✅ Axiom guard passed (all axioms inside namespace Ax)."