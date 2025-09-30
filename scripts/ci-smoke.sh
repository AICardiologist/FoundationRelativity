#!/usr/bin/env bash
# scripts/ci-smoke.sh - Fast subset for PR validation
set -euo pipefail

echo "=== CI Smoke Test (fast subset) ==="
echo

# 1. Check dependencies
echo "▶ Checking dependencies..."
./scripts/check-deps.sh

# 2. Activation status
echo
echo "▶ Checking activation status..."
./scripts/check-activation.sh baseline

# 3. Run all audits (fast, no compilation)
echo
echo "▶ Running audit suite..."
make audit

# 4. Summary
echo
echo "=== Smoke Test Summary ==="
echo "✅ Dependencies available"
echo "✅ Activation marker valid"
echo "✅ All audits passed"
echo
echo "For full validation including Lean compilation, run:"
echo "  lake build Papers.P5_GeneralRelativity.Smoke"
echo "  make baseline"