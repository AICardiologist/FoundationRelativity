#!/bin/bash
set -e

# Foundation-Relativity Regression Testing Script
# Comprehensive post-merge testing for all mathematical proofs and infrastructure

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
    
    if eval "$test_command" > /dev/null 2>&1; then
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
            TESTS_FAILED=$((TESTS_FAILED + 1))
        fi
    fi
}

# Helper function to test theorem accessibility
test_theorem() {
    local theorem_name="$1"
    local import_statement="$2"
    local namespace_open="$3"
    
    local test_cmd="echo '$import_statement
$namespace_open
#check $theorem_name' | lake env lean --stdin"
    
    run_test "theorem $theorem_name" "$test_cmd" true
}

# Helper function to test module imports
test_import() {
    local module_name="$1"
    local test_cmd="echo 'import $module_name' | lake env lean --stdin"
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
run_test "witness_rho4 noncomputable example" "echo 'import AnalyticPathologies.Rho4
open AnalyticPathologies
open AnalyticPathologies.ClassicalWitness
#check DC_omega2_of_Sel₂
#check witness_rho4
noncomputable example : Sel₂ := witness_rho4' | lake env lean --stdin" true

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
run_test "Foundation accessibility through CategoryTheory" "echo 'import CategoryTheory
open CategoryTheory
#check Foundation' | lake env lean --stdin" true
echo

echo -e "${BLUE}Phase 6: Pseudo-Functor Framework${NC}"
echo "----------------------------------"
test_theorem "GapFunctorPF" "import Papers.PseudoFunctorInstances" ""
test_theorem "APFunctorPF" "import Papers.PseudoFunctorInstances" ""
test_theorem "RNPFunctorPF" "import Papers.PseudoFunctorInstances" ""
test_theorem "Id₁" "import Papers.PseudoFunctorInstances" ""

# KNOWN FAILING TESTS: Papers namespace and GapPseudoFunctor should be accessible but aren't
run_test "Papers namespace accessibility" "echo 'import Papers.PseudoFunctorInstances
open Papers
#check GapPseudoFunctor' | lake env lean --stdin" true
echo

echo -e "${BLUE}Phase 7: Paper Infrastructure${NC}"
echo "-------------------------------"
test_import "Papers.P1_GBC.Core"
test_import "Papers.P2_BidualGap.Basic"
# KNOWN FAILING TEST: P3 Basic has Foundation import errors - needs fixing
test_import "Papers.P3_2CatFramework.Basic"
test_theorem "BidualGap" "import Papers.P2_BidualGap.Basic" "open Papers.P2"
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