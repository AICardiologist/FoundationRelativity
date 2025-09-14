#!/usr/bin/env bash
set -euo pipefail

# Count sorries in Paper 5 tree, ignoring commented "-- sorry"
count=$(grep -R "sorry" Papers/P5_GeneralRelativity/*.lean Papers/P5_GeneralRelativity/*/*.lean \
        2>/dev/null | grep -vE "^\s*--\s*sorry" | wc -l | tr -d ' ')
if [ "$count" != "0" ]; then
  echo "ERROR: found $count sorries in Paper 5."
  exit 1
fi
echo "No sorries in Paper 5 ✓"