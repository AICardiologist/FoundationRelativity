#!/usr/bin/env bash
set -euo pipefail
MODE="${1:-baseline}"
FILE="Papers/P5_GeneralRelativity/GR/Riemann.lean"

# Confirm the marker exists
if ! grep -qE '^-- ACTIVATION_STATUS:' "$FILE"; then
  echo "❌ ACTIVATION_STATUS marker not found in $FILE" >&2
  exit 2
fi

# Cross-platform in-place sed
case "$(uname -s)" in
  Darwin) SED=(sed -i '') ;;
  *)      SED=(sed -i)     ;;
esac

# Update the marker
"${SED[@]}" -E "s/^-- ACTIVATION_STATUS:.*/-- ACTIVATION_STATUS: ${MODE}/" "$FILE"

# Verify with your guards
./scripts/check-activation.sh "$MODE"
./scripts/check-baseline.sh

echo "✅ Marker set to '${MODE}', checks passed."

# Optional: Update badge in README files
update_badge() {
  local mode="$1"
  # Map mode → color
  case "$mode" in
    baseline)         color=blue ;;
    stage1-lhs-first) color=yellow ;;
    stage1-lhs-both)  color=orange ;;
    stage1-full)      color=brightgreen ;;
    *)                color=lightgrey ;;
  esac

  for f in "Papers/P5_GeneralRelativity/GR/README.md" "README.md"; do
    [ -f "$f" ] || continue
    # Replace the shields badge line if present
    if grep -q 'Riemann%20Activation-' "$f" 2>/dev/null; then
      "${SED[@]}" -E "s|(Riemann%20Activation-)[^-]*-[a-zA-Z]+|\1${mode}-${color}|g" "$f"
      echo "  Updated badge in $f"
    fi
  done
}

# Uncomment to enable badge updates
# update_badge "$MODE"