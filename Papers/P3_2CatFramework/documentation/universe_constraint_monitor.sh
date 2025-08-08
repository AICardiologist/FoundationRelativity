#!/bin/bash
#
# universe_constraint_monitor.sh
# 
# Automated monitoring for universe constraint issues in Paper 3
# Run this script to check for universe constraint failures
#

set -e

echo "🔍 Paper 3 Universe Constraint Monitor"
echo "======================================"

PAPER3_DIR="Papers/P3_2CatFramework"
EXPERT_DIR="$PAPER3_DIR/expert-session"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo ""
echo "📋 Testing Current Paper 3 Framework Definitions..."

# Test current framework files
echo -n "  • Basic.lean: "
if lake env lean "$PAPER3_DIR/Basic.lean" >/dev/null 2>&1; then
    echo -e "${GREEN}✓ Compiles${NC}"
else
    echo -e "${RED}✗ Universe constraints detected${NC}"
fi

echo -n "  • FunctorialObstruction.lean: " 
if lake env lean "$PAPER3_DIR/FunctorialObstruction.lean" >/dev/null 2>&1; then
    echo -e "${GREEN}✓ Compiles${NC}"
else
    echo -e "${RED}✗ Universe constraints detected${NC}"
fi

echo ""
echo "🧪 Testing Minimal Reproducible Example..."
echo -n "  • universe_constraint_minimal_example.lean: "
if lake env lean "$EXPERT_DIR/universe_constraint_minimal_example.lean" >/dev/null 2>&1; then
    echo -e "${YELLOW}⚠ Unexpected success - constraints may be resolved!${NC}"
else
    echo -e "${RED}✗ Reproduces constraint failure (expected)${NC}"
fi

echo ""
echo "📊 Testing Universe Refactor Draft..."
echo -n "  • universe_refactor_draft.lean: "
if lake env lean "$PAPER3_DIR/documentation/universe_refactor_draft.lean" >/dev/null 2>&1; then
    echo -e "${GREEN}✓ Draft approach works!${NC}"
    echo -e "    ${YELLOW}→ Ready to implement validated approach${NC}"
else
    echo -e "${RED}✗ Draft still has constraints (expected pre-expert session)${NC}"
fi

echo ""
echo "🎯 Current Status Summary:"
echo "  • Paper 3 framework: 6 definitions blocked by universe constraints"
echo "  • GitHub issues: #84-89 tracking specific constraint failures"  
echo "  • Expert session: Materials ready for consultation"
echo "  • Implementation: Awaiting expert-validated universe approach"

echo ""
echo "📅 Next Steps:"
echo "  1. Expert consultation with Mario/Floris/Patrick"
echo "  2. Universe refactor implementation based on expert guidance"
echo "  3. Paper 3 framework definition implementation"
echo "  4. Zero-sorry target achievement"

# Check if we're ready to proceed past expert session
if lake env lean "$PAPER3_DIR/documentation/universe_refactor_draft.lean" >/dev/null 2>&1; then
    echo ""
    echo -e "${GREEN}🚀 READY TO PROCEED: Draft approach successful!${NC}"
    echo "   Consider implementing validated universe approach."
else
    echo ""
    echo -e "${YELLOW}⏳ AWAITING EXPERT SESSION: Universe constraints still present${NC}"
    echo "   Expert consultation required before implementation."
fi

echo ""
echo "Monitor completed. Run this script regularly to track progress."