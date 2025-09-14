#!/bin/bash
# check_diff_warnings.sh - Check for warnings only in changed files
# For Lean 4 projects using lake build

set -euo pipefail

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Get the base branch (usually main)
BASE_REF="${1:-origin/main}"

echo "Checking for warnings in files changed since $BASE_REF..."

# Get list of changed Lean files in Papers/ and CategoryTheory/
CHANGED_FILES=$(git diff --name-only "$BASE_REF"...HEAD | grep -E '^(Papers/|CategoryTheory/).*\.lean$' || true)

if [ -z "$CHANGED_FILES" ]; then
    echo -e "${GREEN}✓ No Lean files changed in Papers/ or CategoryTheory/${NC}"
    exit 0
fi

echo "Changed files to check:"
echo "$CHANGED_FILES" | sed 's/^/  - /'
echo

# Build and collect warnings
echo "Building and checking for warnings..."
lake build 2>&1 | tee build_output.log

# Extract warnings for changed files only
WARNINGS=""
for file in $CHANGED_FILES; do
    # Look for warnings mentioning this file (excluding 'sorry' warnings)
    FILE_WARNINGS=$(grep -E "warning:.*$file" build_output.log | grep -v "declaration uses 'sorry'" || true)
    if [ -n "$FILE_WARNINGS" ]; then
        WARNINGS="${WARNINGS}${FILE_WARNINGS}\n"
    fi
done

# Clean up
rm -f build_output.log

# Report results
if [ -n "$WARNINGS" ]; then
    echo -e "${RED}✗ Warnings found in changed files:${NC}"
    echo -e "$WARNINGS"
    echo
    echo -e "${YELLOW}Please fix these warnings before merging.${NC}"
    echo "Tip: To suppress specific linters, use:"
    echo "  set_option linter.unusedVariables false"
    echo "  set_option linter.unusedSimpArgs false"
    exit 1
else
    echo -e "${GREEN}✓ No warnings in changed files!${NC}"
    exit 0
fi