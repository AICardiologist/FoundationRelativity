#!/usr/bin/env bash
set -euo pipefail

# Count sorries in Paper 5 tree, ignoring commented "-- sorry"
files=$(find Papers/P5_GeneralRelativity -name "*.lean" -type f)
count=0

for file in $files; do
  # Check for non-comment sorries
  if grep -q "sorry" "$file" 2>/dev/null; then
    # Count actual non-comment sorries in this file
    file_count=$(grep "sorry" "$file" | (grep -vE "^[[:space:]]*--" || true) | wc -l | tr -d ' ')
    count=$((count + file_count))
  fi
done

if [ "$count" != "0" ]; then
  echo "ERROR: found $count sorries in Paper 5."
  exit 1
fi
echo "No sorries in Paper 5 ✓"