#!/usr/bin/env bash
set -euo pipefail

# SchematicAudit.sh - Ensure True placeholders only appear in whitelisted schematic files
# This preserves the "no-sorry" bar while allowing schematic scaffolds in specific modules

ALLOW_RE='(GR/(Schwarzschild|EPSCore)|Smoke)\.lean'

echo "Checking for non-schematic True placeholders in Paper 5..."

violations=$(rg -n ":\s*True\s*:=" Papers/P5_GeneralRelativity | \
  grep -vE "$ALLOW_RE" || true)

if [ -n "$violations" ]; then
  echo "❌ Non-schematic True placeholders found:"
  echo "$violations"
  echo ""
  echo "True placeholders should only appear in explicitly whitelisted schematic files:"
  echo "  - Papers/P5_GeneralRelativity/GR/Schwarzschild.lean"
  echo "  - Papers/P5_GeneralRelativity/GR/EPSCore.lean"
  exit 1
fi

echo "✅ Schematic placeholders restricted to whitelisted files."