#!/usr/bin/env bash
set -euo pipefail
echo "SchematicAudit: checking 'True' placeholders are confined to whitelist..."

# Whitelist of files that may intentionally contain schematic True/True.intro.
allow_re='(Papers/P5_GeneralRelativity/GR/Schwarzschild\.lean|Papers/P5_GeneralRelativity/GR/EPSCore\.lean|Papers/P5_GeneralRelativity/GR/Certificates\.lean|Papers/P5_GeneralRelativity/Main\.lean|Papers/P5_GeneralRelativity/Smoke\.lean)'

hits="$(grep -Rns --include='*.lean' -E '\bTrue\.intro\b|:\s*True\s*:=' Papers/P5_GeneralRelativity || true)"
# Also exclude backup directories (frozen snapshots)
violations="$(echo "${hits}" | grep -vE "${allow_re}" | grep -vE '_backup_' || true)"

if [[ -n "${violations}" ]]; then
  echo "❌ SchematicAudit: 'True' placeholders found in non-whitelisted files:"
  echo "${violations}"
  exit 1
fi

echo "✅ SchematicAudit: placeholders confined to whitelist."