#!/bin/bash
# Developer script for Paper 3A quick builds
# Run from repository root: ./scripts/dev-3a.sh

set -e

echo "🔨 Paper 3A Developer Build"
echo "============================"

# Get mathlib cache if available
echo "📦 Getting mathlib cache..."
lake exe cache get || true

# Build main aggregator
echo ""
echo "📘 Building Paper 3A aggregator..."
lake build Papers.P3_2CatFramework.Paper3A_Main

# Build FT Frontier module
echo ""
echo "🌐 Building FT Frontier..."
lake build Papers.P3_2CatFramework.FT_Frontier

# Build examples
echo ""
echo "📝 Building Examples..."
lake build Papers.P3_2CatFramework.Examples.Example1_WitnessFamily
lake build Papers.P3_2CatFramework.Examples.Example2_HeightComposition
lake build Papers.P3_2CatFramework.Examples.Example3_StoneWindow

echo ""
echo "✅ Paper 3A dev build OK"
echo ""
echo "Next steps:"
echo "  - Run tests: lake test"
echo "  - Build 3B: lake build Papers.P3_2CatFramework.Paper3B_Main"
echo "  - Full CI: .github/workflows/paper3-separation-guard.yml"