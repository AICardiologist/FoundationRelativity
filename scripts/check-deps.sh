#!/usr/bin/env bash
set -euo pipefail

need() {
  command -v "$1" >/dev/null 2>&1 || {
    echo "❌ Missing dependency: $1" >&2
    exit 1
  }
}

need python3
need rg

# sed is everywhere, but make sure we can do in-place edits on both BSD/GNU
if sed --version >/dev/null 2>&1; then
  # GNU sed
  true
else
  # macOS/BSD sed doesn't have --version; a simple smoke test:
  TMP_FILE="/tmp/_sed_test_$$.txt"
  echo "test" > "$TMP_FILE"
  if sed -i '' -e 's/test/pass/' "$TMP_FILE" 2>/dev/null; then
    rm -f "$TMP_FILE"
  else
    echo "❌ sed in-place edit not supported as expected" >&2
    rm -f "$TMP_FILE"
    exit 1
  fi
fi

echo "✅ Dependencies OK"