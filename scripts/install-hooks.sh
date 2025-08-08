#!/bin/bash
# Install pre-commit hooks for Paper 3 Framework
set -euo pipefail

echo "Installing Paper 3 Framework git hooks..."

# Create pre-commit hook
cat > .git/hooks/pre-commit << 'EOF'
#!/bin/bash
# Pre-commit hook for Paper 3 Framework
# Runs essential checks before allowing commits

set -euo pipefail

echo "🔍 Running Paper 3 Framework pre-commit checks..."

# Check 1: Guard against vacuity regressions
echo "  ✓ Checking for vacuity regressions..."
if ! ./scripts/guard_vacuity.sh; then
    echo "❌ Pre-commit failed: vacuity guard check failed"
    exit 1
fi

# Check 2: Build core framework
echo "  ✓ Building core framework..."
if ! lake build Papers.P3_2CatFramework.Core.Prelude; then
    echo "❌ Pre-commit failed: core framework build failed"  
    exit 1
fi

# Check 3: Check for unauthorized sorries in staged files
echo "  ✓ Checking for unauthorized sorries..."
staged_files=$(git diff --cached --name-only --diff-filter=AM | grep -E '\.lean$' || true)
if [ -n "$staged_files" ]; then
    disallow=$(echo "$staged_files" | xargs grep -l -E 'sorry|admit' | grep -v 'Blueprint\|FunctorialObstruction' || true)
    if [ -n "$disallow" ]; then
        echo "❌ Pre-commit failed: unauthorized sorry/admit in staged files:"
        echo "$disallow"
        exit 1
    fi
fi

# Check 4: Verify critical tests still compile
echo "  ✓ Compiling critical tests..."
if ! lake env lean Papers/P3_2CatFramework/test/Interp_simp_test.lean > /dev/null 2>&1; then
    echo "❌ Pre-commit failed: Interp simp test compilation failed"
    exit 1
fi

if [ -f "Papers/P3_2CatFramework/test/TwoCell_simp_test.lean" ]; then
    if ! lake env lean Papers/P3_2CatFramework/test/TwoCell_simp_test.lean > /dev/null 2>&1; then
        echo "❌ Pre-commit failed: TwoCell simp test compilation failed"
        exit 1
    fi
fi

echo "✅ All pre-commit checks passed!"
exit 0
EOF

chmod +x .git/hooks/pre-commit

echo "✅ Pre-commit hook installed successfully!"
echo ""
echo "To test the hook:"
echo "  ./scripts/install-hooks.sh"
echo ""  
echo "To disable temporarily:"
echo "  git commit --no-verify"