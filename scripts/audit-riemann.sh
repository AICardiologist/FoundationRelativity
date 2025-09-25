#!/usr/bin/env bash
set -euo pipefail

echo "▶ Audit: global [simp] on sumIdx_expand (should be none)"
# Look for non-commented lines with [simp] and sumIdx_expand in Lean files only
# Check if any non-commented lines exist after filtering
FOUND=$(rg --no-filename -t lean 'attribute\s*\[simp\].*sumIdx_expand' Papers 2>/dev/null | grep -v '^\s*--' | grep -v '^\s*//' || true)
if [ -n "$FOUND" ]; then
  echo "  ⚠ Found potential global [simp] for sumIdx_expand"; exit 1
else
  echo "  ✅ None found"
fi

echo "▶ Audit: RHS sections enabled?"
if rg -n 'section\s+Stage1_RHS' Papers >/dev/null 2>&1; then
  echo "  ⚠ RHS sections present."
  if ! rg -n '^\s*def\s+gInv\s*\(' Papers/P5_GeneralRelativity/GR/Riemann.lean >/dev/null 2>&1; then
    echo "  ❌ gInv not enabled but RHS present"; exit 1
  else
    echo "  ✅ gInv defined; RHS enablement is consistent"
  fi
else
  echo "  ✅ RHS sections not enabled (as expected for baseline)"
fi

echo "▶ Audit complete."