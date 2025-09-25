#!/usr/bin/env bash
# Informational: list all `sorry` occurrences under Paper 5, grouped by file.
set -euo pipefail
echo "▶ Audit (info): mapping 'sorry' occurrences under Papers/P5_GeneralRelativity"
if ! command -v rg >/dev/null 2>&1; then
  echo "  (ripgrep not found; skipping map)"
  exit 0
fi
FOUND=$(rg -n --glob 'Papers/P5_GeneralRelativity/**' '\bsorry\b' 2>/dev/null || true)
if [ -z "$FOUND" ]; then
  echo "  ✅ No 'sorry' tokens found in Paper 5 (informational)"
  exit 0
fi
echo "  Summary by file (count of sorries):"
echo "$FOUND" | awk -F: '{print $1}' | sort | uniq -c | sort -nr \
  | sed 's/^/  • /'
echo
echo "  Full list:"
echo "  ----------------------------------------------------------------"
echo "$FOUND" | sed 's/^/    /'
echo "  ----------------------------------------------------------------"
echo "  (This audit is informational and does not enforce anything.)"