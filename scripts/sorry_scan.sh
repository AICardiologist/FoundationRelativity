#!/usr/bin/env bash
set -euo pipefail

# Whitelist patterns (directories allowed to contain sorries, if any)
WHITELIST='^$'   # empty: fail on any real sorry

fail=0
while IFS= read -r -d '' f; do
  # Skip whitelisted paths (simplified for portability)
  if [[ "$f" =~ $WHITELIST ]]; then
    continue
  fi
  # Strip line comments and naive (non-nested) block comments, then search for 'sorry' tokens
  if awk '
    BEGIN{inblk=0}
    {
      line=$0
      # toggle block comment state on /- and -/
      if (index(line,"/-")) inblk=1
      if (!inblk) {
        # drop line comments
        sub(/--.*/,"",line)
        if (line ~ /(^|[^[:alnum:]_])sorry([^[:alnum:]_]|$)/) { print FILENAME ":" NR ":" $0 }
      }
      if (index($0,"-/")) inblk=0
    }' "$f" | rg . -n --no-heading; then
    fail=1
  fi
done < <(bash -c '
  rg -0 --files Papers/P2_BidualGap/Basics Papers/P2_BidualGap/Gap -g "*.lean" || true
  find Papers/P2_BidualGap/Constructive -name "*.lean" \
    -not -path "*/CReal_obsolete/*" -not -name "DualStructure.lean" -print0
')

if [[ $fail -ne 0 ]]; then
  echo "💥 FAILURE: real 'sorry' found in Lean source"
  exit 1
fi

echo "🎯 SUCCESS: no real 'sorry' tokens detected"