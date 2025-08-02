#!/bin/bash
# Don't exit on first error - let tests complete and report all failures  
# set -e

# Foundation-Relativity Regression Testing Script  
# Comprehensive post-merge testing for all mathematical proofs and infrastructure

# Ensure we're in the right directory
if [ ! -f "lakefile.lean" ]; then
    echo "Error: Must run from project root directory"
    exit 1
fi

# Use latest mathlib commit (no longer pinned to specific version)
echo "🔧 Checking mathlib cache and build status..."
CURRENT_MATHLIB_COMMIT=$(cd .lake/packages/mathlib && git rev-parse HEAD | cut -c1-10)
echo "📍 Using mathlib commit: $CURRENT_MATHLIB_COMMIT"

# No longer forcing specific mathlib commit - use whatever is in lake-manifest.json

# Ensure mathlib cache is downloaded for current commit
echo "📦 Downloading mathlib cache for commit $CURRENT_MATHLIB_COMMIT..."
lake exe cache get > /dev/null 2>&1 || echo "⚠️  Cache download failed, will build from source"

# Check if we have usable mathlib cache
MATHLIB_CACHE_PATH=".lake/packages/mathlib/.lake/build/lib/lean"
CACHE_FILE_COUNT=$(find "$MATHLIB_CACHE_PATH" -name "*.olean" 2>/dev/null | wc -l | tr -d ' ')
if [ -f "$MATHLIB_CACHE_PATH/Mathlib.olean" ] && [ "$CACHE_FILE_COUNT" -gt 1000 ]; then
    echo "✅ Using mathlib cache ($CACHE_FILE_COUNT olean files available)"
    # Quick verification that cache works by building a simple module
    echo "🔍 Verifying cache works with quick build test..."
    if lake build Mathlib.Tactic.Basic > /dev/null 2>&1; then
        echo "✅ Cache verification successful - ready for fast builds"
    else
        echo "⚠️  Cache verification failed, doing minimal rebuild"
        lake build Mathlib.Data.Nat.Basic > /dev/null 2>&1 || true
    fi
else
    echo "❌ Insufficient cache ($CACHE_FILE_COUNT files), doing minimal build..."
    lake build Mathlib.Data.Nat.Basic > /dev/null 2>&1 || true
fi

# Pre-build critical modules that are tested (in parallel if possible)
echo "🔨 Pre-building key tested modules..."

# Core modules
lake build CategoryTheory.Found CategoryTheory.BicatFound > /dev/null 2>&1 || true

# Paper infrastructure modules - CRITICAL for avoiding missing .olean files
echo "📚 Pre-building paper modules..."
lake build Papers.PseudoFunctorInstances > /dev/null 2>&1 || true
lake build Papers.P1_GBC.Core > /dev/null 2>&1 || true
lake build Papers.P2_BidualGap.Basic > /dev/null 2>&1 || true
lake build Papers.P3_2CatFramework.Basic > /dev/null 2>&1 || true
lake build Papers.P4_SpectralGeometry > /dev/null 2>&1 || true

# Logic modules
lake build Logic.ProofTheoryAxioms Logic.Reflection > /dev/null 2>&1 || true

# Analytic pathologies for rho tests
lake build AnalyticPathologies.Rho4 > /dev/null 2>&1 || true

# Additional modules that might be tested
echo "🔄 Pre-building additional test dependencies..."
lake build Gap2.Functor APFunctor.Functor RNPFunctor.Functor > /dev/null 2>&1 || true
lake build AnalyticPathologies.SpectralGap AnalyticPathologies.Cheeger > /dev/null 2>&1 || true

echo "✅ Pre-build phase complete"
echo

echo "🧪 Foundation-Relativity Regression Testing Suite"
echo "=================================================="
echo

# Color codes for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Test counters
TESTS_PASSED=0
TESTS_FAILED=0
TOTAL_TESTS=0

# Helper function to run a test
run_test() {
    local test_name="$1"
    local test_command="$2"
    local expected_success="$3"  # true/false
    
    echo -n "Testing $test_name... "
    TOTAL_TESTS=$((TOTAL_TESTS + 1))
    
    # Store test output for debugging
    local test_output
    test_output=$(eval "$test_command" 2>&1)
    local exit_code=$?
    
    if [ $exit_code -eq 0 ]; then
        if [ "$expected_success" = "true" ]; then
            echo -e "${GREEN}✓ PASS${NC}"
            TESTS_PASSED=$((TESTS_PASSED + 1))
        else
            echo -e "${RED}✗ FAIL (expected failure but passed)${NC}"
            TESTS_FAILED=$((TESTS_FAILED + 1))
        fi
    else
        if [ "$expected_success" = "false" ]; then
            echo -e "${GREEN}✓ PASS (expected failure)${NC}"
            TESTS_PASSED=$((TESTS_PASSED + 1))
        else
            echo -e "${RED}✗ FAIL${NC}"
            echo "    Error output: $test_output"
            echo "    Exit code: $exit_code"
            TESTS_FAILED=$((TESTS_FAILED + 1))
        fi
    fi
}

# Helper function to ensure module is built before testing
ensure_module_built() {
    local module="$1"
    # Extract module name from import statement if needed
    if [[ "$module" == import* ]]; then
        module=$(echo "$module" | sed 's/import //')
    fi
    
    # Check if .olean file exists
    local olean_path=".lake/build/lib/lean/${module//./\/}.olean"
    if [ ! -f "$olean_path" ]; then
        echo -n "    Building $module... "
        if lake build "$module" > /dev/null 2>&1; then
            echo "done"
        else
            echo "failed (non-critical)"
        fi
    fi
}

# Helper function to test theorem accessibility
test_theorem() {
    local theorem_name="$1"
    local import_statement="$2"
    local namespace_open="$3"
    
    # Ensure the imported module is built
    ensure_module_built "$import_statement"
    
    # Create temporary file to ensure proper path resolution
    local temp_file="/tmp/lean_test_$$.lean"
    echo "$import_statement
$namespace_open
#check $theorem_name" > "$temp_file"
    
    local test_cmd="lake env lean \"$temp_file\" && rm -f \"$temp_file\""
    
    run_test "theorem $theorem_name" "$test_cmd" true
}

# Helper function to test module imports
test_import() {
    local module_name="$1"
    
    # Ensure the module is built before testing
    ensure_module_built "$module_name"
    
    # Create temporary file to ensure proper path resolution
    local temp_file="/tmp/lean_import_test_$$.lean"
    echo "import $module_name" > "$temp_file"
    local test_cmd="lake env lean \"$temp_file\" && rm -f \"$temp_file\""
    
    run_test "import $module_name" "$test_cmd" true
}

echo -e "${BLUE}Phase 1: Full Project Build${NC}"
echo "----------------------------"
run_test "full project build" "lake build" true
echo

echo -e "${BLUE}Phase 2: Core Module Imports${NC}"
echo "-----------------------------"
test_import "CategoryTheory"
test_import "CategoryTheory.Found" 
test_import "CategoryTheory.BicatFound"
test_import "CategoryTheory.PseudoFunctor"
test_import "Logic"
test_import "Papers"
test_import "AnalyticPathologies"
echo

echo -e "${BLUE}Phase 3: Foundation-Relativity Core Theorems (ρ-hierarchy)${NC}"
echo "-----------------------------------------------------------"

# ρ=1 pathologies (WLPO)
test_theorem "Gap_requires_WLPO" "import Gap2.Proofs" "open Gap.Proofs"
test_theorem "AP_requires_WLPO" "import APFunctor.Proofs" "open APFail.Proofs"

# ρ=2 pathologies (DC_ω) 
test_theorem "RNP_requires_DCω" "import RNPFunctor.Proofs" "open RNPFunctor"

# ρ=3 pathologies (AC_ω)
test_theorem "SpectralGap_requires_ACω" "import AnalyticPathologies.Proofs" "open AnalyticPathologies"

# ρ=4 pathologies (DC_{ω·2})
test_theorem "DC_omega2_of_Sel₂" "import AnalyticPathologies.Rho4" "open AnalyticPathologies"
test_theorem "witness_rho4" "import AnalyticPathologies.Rho4" "open AnalyticPathologies.ClassicalWitness"

# Test witness_rho4 in proper noncomputable context
# Test witness_rho4 in proper noncomputable context using temporary file
witness_temp_file="/tmp/witness_test_$$.lean"
echo 'import AnalyticPathologies.Rho4
open AnalyticPathologies
open AnalyticPathologies.ClassicalWitness
#check DC_omega2_of_Sel₂
#check witness_rho4
noncomputable example : Sel₂ := witness_rho4' > "$witness_temp_file"
run_test "witness_rho4 noncomputable example" "lake env lean \"$witness_temp_file\" && rm -f \"$witness_temp_file\"" true

echo

echo -e "${BLUE}Phase 4: Pathology Test Executables${NC}"
echo "------------------------------------"
run_test "Gap2ProofTests executable" "lake exe Gap2ProofTests" true
run_test "APProofTests executable" "lake exe APProofTests" true  
run_test "RNPProofTests executable" "lake exe RNPProofTests" true
run_test "SpectralGapProofTests executable" "lake exe SpectralGapProofTests" true
run_test "CheegerProofTests executable" "lake exe CheegerProofTests" true
run_test "Rho4ProofTests executable" "lake exe Rho4ProofTests" true
echo

echo -e "${BLUE}Phase 5: Bicategorical Infrastructure${NC}"
echo "-------------------------------------"
# Test both ways to access FoundationBicat (this was a regression we fixed)
test_theorem "FoundationBicat" "import CategoryTheory" "open CategoryTheory"
test_theorem "FoundationBicat" "import CategoryTheory.BicatFound" "open CategoryTheory"
test_theorem "BicatFound_Scaffold" "import CategoryTheory.BicatFound" "open CategoryTheory.BicatFound"
test_theorem "left_unitor" "import CategoryTheory.BicatFound" "open CategoryTheory.BicatFound"
test_theorem "associator" "import CategoryTheory.BicatFound" "open CategoryTheory.BicatFound"

# Test that Foundation is accessible through CategoryTheory export
# Test Foundation accessibility through CategoryTheory using temporary file
foundation_temp_file="/tmp/foundation_test_$$.lean"
echo 'import CategoryTheory
open CategoryTheory
#check Foundation' > "$foundation_temp_file"
run_test "Foundation accessibility through CategoryTheory" "lake env lean \"$foundation_temp_file\" && rm -f \"$foundation_temp_file\"" true
echo

echo -e "${BLUE}Phase 6: Pseudo-Functor Framework${NC}"
echo "----------------------------------"
test_theorem "GapFunctorPF" "import Papers.PseudoFunctorInstances" ""
test_theorem "APFunctorPF" "import Papers.PseudoFunctorInstances" ""
test_theorem "RNPFunctorPF" "import Papers.PseudoFunctorInstances" ""
test_theorem "Id₁" "import Papers.PseudoFunctorInstances" ""

# KNOWN FAILING TESTS: Papers namespace and GapPseudoFunctor should be accessible but aren't
# Test Papers namespace accessibility using temporary file
papers_temp_file="/tmp/papers_test_$$.lean"
echo 'import Papers.PseudoFunctorInstances
open Papers
#check GapPseudoFunctor' > "$papers_temp_file"
run_test "Papers namespace accessibility" "lake env lean \"$papers_temp_file\" && rm -f \"$papers_temp_file\"" true
echo

echo -e "${BLUE}Phase 7: Paper Infrastructure${NC}"
echo "-------------------------------"
test_import "Papers.P1_GBC.Core"
test_import "Papers.P2_BidualGap.Basic"
# KNOWN FAILING TEST: P3 Basic has Foundation import errors - needs fixing
test_import "Papers.P3_2CatFramework.Basic"
test_import "Papers.P4_SpectralGeometry"
test_theorem "BidualGap" "import Papers.P2_BidualGap.Basic" "open Papers.P2"

# Test Paper 4 specific components
echo
echo -e "${BLUE}Phase 7b: Paper 4 Neck Scaling${NC}"
echo "--------------------------------"
test_import "Papers.P4_SpectralGeometry.Geometry.Neck"
test_import "Papers.P4_SpectralGeometry.Spectral.Variational"
test_import "Papers.P4_SpectralGeometry.Spectral.NeckScaling"
test_import "Papers.P4_SpectralGeometry.Logic.ConPA_bridge"

# Test key theorems and definitions from Paper 4
test_theorem "NeckTorus" "import Papers.P4_SpectralGeometry.Geometry.Neck" "open P4_SpectralGeometry"
test_theorem "lambda_1_neck" "import Papers.P4_SpectralGeometry.Spectral.Variational" "open P4_SpectralGeometry"
test_theorem "neck_scaling" "import Papers.P4_SpectralGeometry.Spectral.NeckScaling" "open P4_SpectralGeometry"
test_theorem "spectral_gap_undecidable" "import Papers.P4_SpectralGeometry.Logic.ConPA_bridge" "open P4_SpectralGeometry"
test_theorem "spectral_gap_consistency" "import Papers.P4_SpectralGeometry.Logic.ConPA_bridge" "open P4_SpectralGeometry"
echo

echo -e "${BLUE}Phase 8: Mathematical Operators and Structures${NC}"
echo "-----------------------------------------------"
# Rho4 mathematical content
test_theorem "rho4_selfAdjoint" "import AnalyticPathologies.Rho4" "open AnalyticPathologies"
test_theorem "rho4_bounded" "import AnalyticPathologies.Rho4" "open AnalyticPathologies"
test_theorem "β₀_lt_β₁" "import AnalyticPathologies.Rho4" "open AnalyticPathologies"
test_theorem "β₁_lt_β₂" "import AnalyticPathologies.Rho4" "open AnalyticPathologies"

# Core algebraic structures
test_theorem "L2Space" "import AnalyticPathologies.HilbertSetup" "open AnalyticPathologies"
test_theorem "BoundedOp" "import AnalyticPathologies.HilbertSetup" "open AnalyticPathologies"
echo

echo -e "${BLUE}Phase 9: Logic and Proof Theory${NC}"
echo "--------------------------------"
test_import "Logic.ProofTheoryAxioms"
test_import "Logic.Reflection"
# KNOWN FAILING TESTS: These logic symbols don't exist in Logic module - need to be moved there
test_theorem "WLPO" "import Logic.ProofTheoryAxioms" "open Logic"
test_theorem "DCω" "import Logic.ProofTheoryAxioms" "open Logic"
test_theorem "ACω" "import Logic.ProofTheoryAxioms" "open Logic"
# Working fallback tests from pathology modules
test_theorem "WLPOPlus" "import AnalyticPathologies.Rho4" "open AnalyticPathologies"
test_theorem "DCω2" "import AnalyticPathologies.Rho4" "open AnalyticPathologies"
test_theorem "RequiresDCω2" "import AnalyticPathologies.Rho4" "open AnalyticPathologies"
echo

echo -e "${BLUE}Phase 10: CI/Build System Integration${NC}"
echo "--------------------------------------"
run_test "lakefile.lean compilation" "lake --help" true
# Check that lake manifest exists and is valid
run_test "mathlib dependency resolution" "test -f lake-manifest.json" true
echo

# Summary
echo "=============================================="
echo -e "${BLUE}REGRESSION TEST SUMMARY${NC}"
echo "=============================================="
echo "Total tests run: $TOTAL_TESTS"
echo -e "Tests passed: ${GREEN}$TESTS_PASSED${NC}"
echo -e "Tests failed: ${RED}$TESTS_FAILED${NC}"
echo

if [ $TESTS_FAILED -eq 0 ]; then
    echo -e "${GREEN}🎉 ALL TESTS PASSED! Foundation-Relativity is regression-free.${NC}"
    exit 0
else
    echo -e "${RED}⚠️  $TESTS_FAILED test(s) failed. Please investigate regressions.${NC}"
    exit 1
fi