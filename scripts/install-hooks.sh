#!/usr/bin/env bash
# Install versioned git hooks for the repository
set -euo pipefail

echo "▶ Installing repo-managed git hooks..."

# Use versioned hooks directory instead of .git/hooks
git config core.hooksPath .githooks

# Ensure hooks are executable
chmod +x .githooks/* 2>/dev/null || true

# Legacy: Also create a copy in .git/hooks for backwards compatibility
if [ -f ".githooks/pre-commit" ]; then
  cp .githooks/pre-commit .git/hooks/pre-commit 2>/dev/null || true
  chmod +x .git/hooks/pre-commit 2>/dev/null || true
fi

echo "✅ Hooks installed (core.hooksPath = .githooks)"
echo ""
echo "The following hooks are active:"
ls -la .githooks/ | grep -v "^total\|^d" | awk '{print "  • " $NF}'
echo ""
echo "To bypass hooks temporarily:"
echo "  git commit --no-verify"
echo ""
echo "To uninstall:"
echo "  git config --unset core.hooksPath"

exit 0

# The original hook content is now maintained in .githooks/pre-commit
# Below is the legacy installation for reference only
cat > /dev/null << 'EOF'
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