#!/usr/bin/env bash
if grep -R --exclude="*Test.lean" -E "sorry\b" Found Gap2 APFunctor RNPFunctor; then 
  echo "ERROR: Found 'sorry' in core modules!"
  exit 1
fi
echo "✓ No sorry found in core modules"