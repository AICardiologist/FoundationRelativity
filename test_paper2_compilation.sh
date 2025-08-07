#!/bin/bash

echo "Testing Paper 2 Compilation..."
echo "=============================="

# Test core files that should compile
echo -e "\nTesting core files:"
for file in "Papers.P2_BidualGap.Basic" \
            "Papers.P2_BidualGap.Logic.WLPOBasic" \
            "Papers.P2_BidualGap.MainTheoremSimple" \
            "Papers.P2_BidualGap.Tactics" \
            "Papers.P2_BidualGap.WLPO_Equiv_Gap"
do
    echo -n "Building $file... "
    if lake build "$file" 2>&1 | grep -q "Build completed successfully"; then
        echo "✓ SUCCESS"
    else
        echo "✗ FAILED"
    fi
done

echo -e "\nPaper 2 Core Compilation Test Complete"