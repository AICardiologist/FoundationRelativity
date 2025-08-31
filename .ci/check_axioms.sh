#!/usr/bin/env bash
# Axiom budget guard for Paper 3B
# Ensures all axioms are declared within namespace Ax blocks
#
# Notes:
# - Requires bash (uses [[ ]], functions, etc.)
# - Grep is POSIX ERE only (no -P), works on GNU/BSD.

set -euo pipefail
export LC_ALL=C

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

# Read "BUDGET LOCKED AT <N>" from AXIOM_INDEX.md
INDEX_FILE="Papers/P3_2CatFramework/documentation/AXIOM_INDEX.md"
if [[ -f "$INDEX_FILE" ]]; then
  MAX_AXIOMS=$(grep -Eo "BUDGET LOCKED AT[[:space:]]+[0-9]+" "$INDEX_FILE" | grep -Eo "[0-9]+" | head -1)
fi
if [[ -z "${MAX_AXIOMS:-}" ]]; then
  echo "⚠️  Could not parse budget from AXIOM_INDEX.md; falling back to default 30."
  MAX_AXIOMS=30
fi

# Allow a developer override of the budget without editing AXIOM_INDEX.md
if [[ -n "${MAX_AXIOMS_OVERRIDE:-}" ]]; then
  echo "ℹ️  Using MAX_AXIOMS_OVERRIDE=$MAX_AXIOMS_OVERRIDE (ignoring parsed budget)."
  MAX_AXIOMS="$MAX_AXIOMS_OVERRIDE"
fi

# Helper functions
count_axioms_file() {
  local f="$1"
  if [[ ! -f "$f" ]]; then printf '0'; return; fi
  if grep -q -E '^[[:space:]]*axiom\b' -- "$f" 2>/dev/null; then
    grep -E -c '^[[:space:]]*axiom\b' -- "$f" 2>/dev/null || printf '0'
  else
    printf '0'
  fi
}

echo "   Current axiom count: $axiom_count"
echo "   Maximum allowed: $MAX_AXIOMS (from AXIOM_INDEX.md)"

if [[ $axiom_count -gt $MAX_AXIOMS ]]; then
  echo "❌ AXIOM BUDGET EXCEEDED!"
  echo "   The axiom count ($axiom_count) exceeds the budget of $MAX_AXIOMS."
  echo "   Future PRs must reduce axioms, not increase them."
  echo ""
  # GitHub Actions annotation for PR UI
  if [[ -n "${GITHUB_ACTIONS:-}" ]]; then
    echo "::group::📊 Axiom budget details"
  fi
  echo "📊 Files contributing axioms:"
  tmp_report="$(mktemp)"
  for f in $files; do
    if [ -f "$f" ]; then
      cnt="$(count_axioms_file "$f")"
      if [[ "$cnt" -gt 0 ]]; then
        printf "%02d %s\n" "$cnt" "${f#Papers/P3_2CatFramework/P4_Meta/ProofTheory/}" >> "$tmp_report"
      fi
    fi
  done
  if [[ -s "$tmp_report" ]]; then
    sort -rn "$tmp_report" | sed -E 's/^([0-9]{2}) (.*)$/  \1 axioms in \2/'
  fi
  rm -f "$tmp_report"
  # GitHub Actions annotation
  if [[ -n "${GITHUB_ACTIONS:-}" ]]; then
    echo "::error title=Axiom budget exceeded::${axiom_count} > ${MAX_AXIOMS}. See 'Axiom budget details' for per-file counts."
    echo "::endgroup::"
  fi
  exit 1
fi

echo "✅ Axiom budget check passed ($axiom_count ≤ $MAX_AXIOMS)."

# Check for any sorry or admit (as proof terms, not in comments)
echo "🔍 Checking for sorries..."
# Look for sorry/admit as proof terms, skipping comments
sorry_pattern='(^[[:space:]]*(by[[:space:]]*)?sorry[[:space:]]*$)|(:=[[:space:]]*sorry\b)|(^[[:space:]]*(by[[:space:]]*)?admit[[:space:]]*$)|(:=[[:space:]]*admit\b)'
sorry_files=""
for f in $files; do
  if [ -f "$f" ]; then
    # Check if file contains sorry/admit (not in comments)
    if grep -qE "$sorry_pattern" "$f" 2>/dev/null; then
      # Basic filter: skip if entire match is in a comment line
      # (More sophisticated comment filtering would need proper parsing)
      if ! grep -E "$sorry_pattern" "$f" 2>/dev/null | grep -q '^[[:space:]]*--'; then
        sorry_files="${sorry_files}${f}\n"
      fi
    fi
  fi
done

if [[ -n "$sorry_files" ]]; then
  echo "❌ Found sorry/admit instances!"
  echo "   No sorries are allowed in Paper 3B ProofTheory modules."
  echo ""
  # GitHub Actions annotation for PR UI
  if [[ -n "${GITHUB_ACTIONS:-}" ]]; then
    echo "::group::📊 Sorry/admit details"
  fi
  echo "📊 Files containing sorries:"
  tmp_sorry="$(mktemp)"
  echo -e "$sorry_files" | while read -r f; do
    if [[ -n "$f" ]]; then
      cnt=$(grep -cE "$sorry_pattern" "$f" 2>/dev/null || echo "0")
      if [[ "$cnt" -gt 0 ]]; then
        printf "%02d %s\n" "$cnt" "${f#Papers/P3_2CatFramework/P4_Meta/ProofTheory/}" >> "$tmp_sorry"
      fi
    fi
  done
  if [[ -s "$tmp_sorry" ]]; then
    sort -rn "$tmp_sorry" | sed -E 's/^([0-9]{2}) (.*)$/  \1 sorries in \2/'
  fi
  rm -f "$tmp_sorry"
  # GitHub Actions annotation
  if [[ -n "${GITHUB_ACTIONS:-}" ]]; then
    echo "::error title=Sorries detected::Remove sorry/admit proof placeholders. See 'Sorry/admit details'."
    echo "::endgroup::"
  fi
  exit 1
fi

echo "✅ No sorries found in ProofTheory modules."