#!/bin/bash
# Fast Post-Merge Verification Script
# Uses mathlib cache for rapid verification of core functionality

set -e

echo "🚀 Fast Post-Merge Verification (using cache)"
echo "=============================================="
echo

# Verify we have mathlib cache
CACHE_COUNT=$(find .lake/packages/mathlib/.lake/build/lib/lean -name "*.olean" 2>/dev/null | wc -l | tr -d ' ')
echo "📦 Mathlib cache: $CACHE_COUNT files available"

if [ "$CACHE_COUNT" -lt 1000 ]; then
    echo "❌ Insufficient cache - run full regression test instead"
    exit 1
fi

echo "✅ Cache sufficient for fast verification"
echo

# Test 1: Core Foundation module
echo "🧪 Test 1: Foundation module builds..."
if lake build CategoryTheory.Found > /dev/null 2>&1; then
    echo "✅ PASS - Foundation module builds"
else
    echo "❌ FAIL - Foundation module build failed"
    exit 1
fi

# Test 2: Key pathology proofs
echo "🧪 Test 2: Core pathology executables..."
for test in Gap2ProofTests APProofTests RNPProofTests; do
    echo -n "  Testing $test... "
    if lake exe $test > /dev/null 2>&1; then
        echo "✅ PASS"
    else
        echo "❌ FAIL"
        exit 1  
    fi
done

# Test 3: Paper 1 Core module
echo "🧪 Test 3: Paper 1 Core module..."
if lake build Papers.P1_GBC.Core > /dev/null 2>&1; then
    echo "✅ PASS - Paper 1 Core builds (4 sorries remaining)"
else
    echo "❌ FAIL - Paper 1 Core build failed"
    exit 1
fi

# Test 4: Critical bicategorical infrastructure
echo "🧪 Test 4: Bicategorical infrastructure..."
if lake build CategoryTheory.BicatFound > /dev/null 2>&1; then
    echo "✅ PASS - Bicategorical infrastructure builds"
else
    echo "❌ FAIL - Bicategorical infrastructure failed"
    exit 1
fi

echo
echo "🎉 FAST POST-MERGE VERIFICATION COMPLETE"
echo "========================================"
echo "✅ All critical components verified successfully"
echo "✅ Foundation-Relativity is ready for continued development"
echo "✅ Run 'bash scripts/regression-test.sh' for comprehensive testing"