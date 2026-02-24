#!/bin/bash
FILE="Riemann.lean"
for LINE in 6081 7533 7835 8637 8787 8802 8819 8823 8852 9000 9015 9033 9037 9078 9249 9464 9533 9644; do
  START=$((LINE - 10))
  END=$((LINE + 10))
  if [ $START -lt 1 ]; then START=1; fi
  echo "### Context for line $LINE (lines $START-$END)"
  sed -n "${START},${END}p" "$FILE" | cat -n
  echo ""
done
