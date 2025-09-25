#!/usr/bin/env bash
set -euo pipefail

FILE="Papers/P5_GeneralRelativity/GR/Riemann.lean"

echo "▶ Audit: Stage-1 lemma signatures present"
needles=(
  "namespace Stage1LHS"
  "lemma Hc_one"
  "lemma Hd_one"
  "lemma Hc2_one"
  "lemma Hd2_one"
  "lemma dCoord_add4"
  "lemma dCoord_add4_flat"
  "lemma dCoord_sumIdx_via_funext"
  "lemma dCoord_sumIdx_via_local_expand"
)
for n in "${needles[@]}"; do
  if ! rg -n --fixed-strings "$n" "$FILE" >/dev/null; then
    echo "  ❌ Missing or renamed: $n"
    exit 1
  fi
done
echo "  ✅ Stage-1 invariants found"

echo "▶ Audit: Activation marker present"
if ! rg -n '^-- ACTIVATION_STATUS:' "$FILE" >/dev/null; then
  echo "  ❌ Missing ACTIVATION_STATUS marker at top of Riemann.lean"
  exit 1
fi
echo "  ✅ Marker present"

echo "▶ Audit: ActivationDemo remains commented"
# Check if ActivationDemo section exists and is preceded by comment marker
if grep -B1 "section ActivationDemo" "$FILE" 2>/dev/null | grep -q '^/-'; then
  echo "  ✅ Demo remains commented (baseline-safe)"
elif grep -q "section ActivationDemo" "$FILE" 2>/dev/null; then
  echo "  ❌ Found uncommented ActivationDemo section"
  exit 1
else
  echo "  ⚠️ ActivationDemo section not found (may have been removed)"
fi