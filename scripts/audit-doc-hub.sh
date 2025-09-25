#!/usr/bin/env bash
set -euo pipefail
HUB="Papers/P5_GeneralRelativity/GR/README.md"
must=(
  "ACTIVATION_TRACKING.md"
  "ACTIVATION_QUICKREF.md"
  "ROADMAP_Schwarzschild_Vacuum.md"
  "PR_TEMPLATES.md"
  "ISSUES_TO_OPEN.md"
)
echo "▶ Audit: GR docs hub links"
for m in "${must[@]}"; do
  if ! rg -n --fixed-strings "$m" "$HUB" >/dev/null; then
    echo "  ❌ Missing link to $m in GR/README.md"
    exit 1
  fi
done
echo "  ✅ Hub links present"