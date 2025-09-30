#!/usr/bin/env bash
set -euo pipefail

echo "▶ Audit: no global [simp] on RHS μ-expander"
if grep -nR "^\s*attribute\s*\[simp\].*sumIdx_expand_local_rhs" Papers/P5_GeneralRelativity >/dev/null 2>&1; then
  echo "  ❌ Found global [simp] on RHS μ-expander" >&2
  exit 1
fi
echo "  ✅ None found"