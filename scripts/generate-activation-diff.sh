#!/usr/bin/env bash
set -euo pipefail

MODE="${1:-stage1-lhs-both}"
FILE="Papers/P5_GeneralRelativity/GR/Riemann.lean"
OUT="Papers/P5_GeneralRelativity/GR/activation-diff-${MODE}.patch"

echo "▶ Generating activation diff against current index (mode=${MODE})"

# Ensure deps
./scripts/check-deps.sh >/dev/null 2>&1

# Remember current marker
CURRENT=$(sed -n 's/^-- ACTIVATION_STATUS:\s*\(.*\)$/\1/p' "$FILE" | head -1)
if [ -z "${CURRENT:-}" ]; then
  echo "❌ Could not read ACTIVATION_STATUS marker in $FILE" >&2
  exit 2
fi

echo "  Current mode: $CURRENT"
echo "  Target mode: $MODE"

# Stash only working-tree changes to the file (keep index clean)
STASHED=false
if ! git diff --quiet -- "$FILE"; then
  git stash push -k -u -m "activation-diff-generator" -- "$FILE" >/dev/null
  STASHED=true
fi

# Setup cleanup trap to always restore state
restore() {
  # Best-effort: restore marker + stash
  ./scripts/set-activation.sh "$CURRENT" >/dev/null 2>&1 || true
  if [ "$STASHED" = true ]; then
    git stash pop -q >/dev/null 2>&1 || true
  fi
}
trap restore EXIT

# Flip to requested mode (mutates working tree)
./scripts/set-activation.sh "$MODE" >/dev/null

# Produce a patch relative to the index (not HEAD)
git --no-pager diff -- "$FILE" > "$OUT"

# Count the changes
LINES_CHANGED=$(git diff --stat -- "$FILE" | awk '{print $(NF-1)}')

echo "✅ Wrote activation diff to: $OUT"
echo "  (${LINES_CHANGED:-0} insertions/deletions)"
echo
echo "To apply this diff in another branch:"
echo "  git apply $OUT"