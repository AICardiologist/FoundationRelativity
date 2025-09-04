#!/bin/bash

# Sorry Allowlist Enforcement Script
# Verifies that only authorized sorry statements exist in the codebase
# Any sorry outside SORRY_ALLOWLIST.txt will fail CI

set -e

echo "🔍 Checking sorry statements against allowlist..."

# Check if allowlist exists
if [[ ! -f "SORRY_ALLOWLIST.txt" ]]; then
    echo "❌ SORRY_ALLOWLIST.txt not found"
    exit 1
fi

# Extract allowed sorry locations from allowlist (ignore comments and empty lines)
allowed_sorries=$(grep -E '^[^#].*\.lean:[0-9]+' SORRY_ALLOWLIST.txt | awk '{print $1}' | sort)
allowed_count=$(echo "$allowed_sorries" | wc -l)

echo "📋 Allowlist contains $allowed_count authorized sorry statements"

# Find all actual sorry statements in the codebase
echo "🔎 Scanning codebase for sorry statements..."

# Create temporary file for results
temp_file=$(mktemp)

# Search for sorry in project .lean files (exclude .lake dependencies)
find . -name "*.lean" -type f -not -path "./.lake/*" -exec grep -Hn "sorry" {} \; | \
    grep -v "test/" | \
    grep -v "docs/" | \
    grep -v "old_files/" | \
    grep -v "Archived/" | \
    grep -v "archive/" | \
    grep -v "communication/" | \
    grep -v "documentation/" | \
    grep -v "WIP/" | \
    grep -v "standalone/" | \
    grep -v "quotient_implementation_guide.lean" | \
    grep -v "test_" | \
    grep -v "compiles without.*sorry" | \
    grep -v "no.*sorry.*no tactics" | \
    sed 's/^\.\///' | \
    awk -F: '{print $1":"$2}' | \
    sort > "$temp_file"

actual_sorries=$(cat "$temp_file")
actual_count=$(cat "$temp_file" | wc -l)

echo "📊 Found $actual_count sorry statements in codebase"

# Compare actual vs allowed
echo ""
echo "📋 Allowlist verification:"

violations=0

while IFS= read -r sorry_location; do
    if [[ -n "$sorry_location" ]]; then
        if echo "$allowed_sorries" | grep -q "^$sorry_location$"; then
            echo "✅ $sorry_location (authorized)"
        else
            echo "❌ $sorry_location (VIOLATION - not in allowlist)"
            violations=$((violations + 1))
        fi
    fi
done < "$temp_file"

# Check for allowlist entries without corresponding sorries
echo ""
echo "📋 Allowlist coverage:"
while IFS= read -r allowed_location; do
    if [[ -n "$allowed_location" ]]; then
        if cat "$temp_file" | grep -q "^$allowed_location$"; then
            echo "📍 $allowed_location (found)"
        else
            echo "⚠️  $allowed_location (allowlist entry without corresponding sorry)"
        fi
    fi
done <<< "$allowed_sorries"

# Cleanup
rm "$temp_file"

# Final verdict
echo ""
if [[ $violations -eq 0 ]]; then
    echo "🎉 All sorry statements are authorized!"
    echo "   $actual_count sorries found, all in allowlist"
    exit 0
else
    echo "💥 Found $violations unauthorized sorry statement(s)"
    echo "   Add to SORRY_ALLOWLIST.txt or remove the sorry statements"
    exit 1
fi