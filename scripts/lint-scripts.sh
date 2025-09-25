#!/usr/bin/env bash
set -euo pipefail
echo "▶ Linting repo scripts (best-effort)"

# Track if any linters were found
FOUND_ANY=false

# Check for shellcheck
if command -v shellcheck >/dev/null 2>&1; then
  echo "  • Running shellcheck on shell scripts..."
  FOUND_ANY=true
  # Find all .sh files and check them
  find scripts -name "*.sh" -type f -print0 | \
    xargs -0 -I {} sh -c 'echo "    Checking {}..." && shellcheck {} || true'
else
  echo "  • shellcheck not found (skipping)"
fi

# Check for Python linters
if command -v python3 >/dev/null 2>&1; then
  # Try pyflakes
  if python3 -c 'import pyflakes' 2>/dev/null; then
    echo "  • Running pyflakes on Python scripts..."
    FOUND_ANY=true
    python3 -m pyflakes scripts/*.py 2>/dev/null || true
  else
    echo "  • pyflakes not available (skipping)"
  fi

  # Try pylint as alternative
  if python3 -c 'import pylint' 2>/dev/null; then
    echo "  • Running pylint on Python scripts..."
    FOUND_ANY=true
    python3 -m pylint --disable=all --enable=E,F scripts/*.py 2>/dev/null || true
  elif [ "$FOUND_ANY" = false ]; then
    echo "  • pylint not available (skipping)"
  fi
else
  echo "  • python3 not found (skipping Python checks)"
fi

# Summary
if [ "$FOUND_ANY" = true ]; then
  echo "  ✅ Linting complete (informational only)"
else
  echo "  ⚠️ No linters found - consider installing shellcheck and/or pyflakes"
fi

# Always exit 0 since this is optional
exit 0