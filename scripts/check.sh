#!/usr/bin/env bash
set -euo pipefail
MODE="${1:-baseline}"
./scripts/check-activation.sh "$MODE"
./scripts/check-baseline.sh
echo "✅ All checks passed (mode=$MODE)."