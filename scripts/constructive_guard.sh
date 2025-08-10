#!/usr/bin/env bash
set -euo pipefail

out="$(lake env lean --run Scripts/ConstructiveGuard.lean || true)"
echo "$out"

# Fail if a compat axiom or sorryAx shows up in any core theorem (check axiom lines only)
if echo "$out" | rg '^'"'"'Papers\.P2\.Constructive\.' | rg -q 'Papers\.P2\.Compat\.Axioms|sorryAx'; then
  echo "💥 FAILURE: forbidden axioms detected in core constructive theorems"
  exit 1
fi

# Also fail if any Constructive file imports Compat.*
if rg -n '^import .*Compat\.' Papers/P2_BidualGap/Constructive -S | rg .; then
  echo "💥 FAILURE: Constructive files import Compat.*"
  exit 1
fi

# Forbid Constructive importing Gap (keeps the pipeline acyclic & pure)
if rg -n '^import .*Papers\.P2_BidualGap\.Gap\.' Papers/P2_BidualGap/Constructive -S | rg .; then
  echo "💥 FAILURE: Constructive files import Gap.*"
  exit 1
fi

# Forbid Compat importing Constructive (prevents sneaky cycles)
if rg -n '^import .*Papers\.P2_BidualGap\.Constructive\.' Papers/P2_BidualGap/Compat -S | rg .; then
  echo "💥 FAILURE: Compat files import Constructive.*"
  exit 1
fi

# Forbid 'axiom' declarations in Paper 2 outside the quarantined file
if rg -n '^\s*axiom\s+[a-zA-Z_]' --hidden -S \
     -g '!Papers/P2_BidualGap/Compat/Axioms.lean' \
     Papers/P2_BidualGap | rg .; then
  echo "💥 FAILURE: 'axiom' declaration in Paper 2 outside Compat/Axioms.lean"
  exit 1
fi

# Forbid BigOperators binder and projection-style .sum in §2 basics (actual code only)
# ∑ binder check (actual code only)
if awk -f Scripts/strip_lean_comments.awk Papers/P2_BidualGap/Basics/FiniteCesaro.lean \
   | rg -n '[∑]' -S | rg .; then
  echo "💥 FAILURE: Found ∑ binder in FiniteCesaro.lean code (use Finset.sum function style)"
  exit 1
fi

# projection-style .sum check (exclude Finset.sum)
if awk -f Scripts/strip_lean_comments.awk Papers/P2_BidualGap/Basics/FiniteCesaro.lean \
   | rg -n '\.\s*sum\b' -S | rg -v 'Finset\.sum' | rg .; then
  echo "💥 FAILURE: Found projection-style s.sum in code (use Finset.sum)"
  exit 1
fi

echo "🎯 SUCCESS: core constructive theorems axiom‑clean; no Compat imports."