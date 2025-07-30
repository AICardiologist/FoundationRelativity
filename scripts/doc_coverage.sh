#!/bin/bash
# doc_coverage.sh - Calculate documentation coverage for Lean files
# Sprint 44 Day 3: Documentation metrics for CI

set -euo pipefail

# Color codes for output
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
NC='\033[0m' # No Color

# Configuration
PROJECT_ROOT="${PROJECT_ROOT:-$(git rev-parse --show-toplevel 2>/dev/null || pwd)}"
LEAN_DIRS=("CategoryTheory" "AnalyticPathologies" "Papers" "Found")
OUTPUT_FILE="${1:-}"

# Counters
total_declarations=0
documented_declarations=0
total_files=0
files_with_header=0

# Function to check if a line is a declaration
is_declaration() {
    local line="$1"
    # Match theorem, lemma, def, structure, class, instance, example
    if [[ "$line" =~ ^[[:space:]]*(theorem|lemma|def|structure|class|instance|example)[[:space:]]+ ]]; then
        # Exclude private declarations and examples
        if [[ ! "$line" =~ ^[[:space:]]*private[[:space:]]+ ]] && [[ ! "$line" =~ ^[[:space:]]*example[[:space:]]+ ]]; then
            return 0
        fi
    fi
    return 1
}

# Function to check if declaration has doc comment
has_doc_comment() {
    local file="$1"
    local line_num="$2"
    
    # Check the line above for /-- doc comment
    if (( line_num > 1 )); then
        local prev_line=$(sed -n "$((line_num-1))p" "$file")
        if [[ "$prev_line" =~ ^[[:space:]]*/-- ]]; then
            return 0
        fi
    fi
    return 1
}

# Function to check if file has module doc header
has_module_header() {
    local file="$1"
    # Check first 10 lines for /-! module doc
    if head -n 10 "$file" | grep -q "^/-!"; then
        return 0
    fi
    return 1
}

# Process a single Lean file
process_file() {
    local file="$1"
    local file_declarations=0
    local file_documented=0
    
    ((total_files++))
    
    # Check for module header
    if has_module_header "$file"; then
        ((files_with_header++))
    fi
    
    # Process each line
    local line_num=0
    while IFS= read -r line; do
        ((line_num++))
        
        if is_declaration "$line"; then
            ((file_declarations++))
            ((total_declarations++))
            
            if has_doc_comment "$file" "$line_num"; then
                ((file_documented++))
                ((documented_declarations++))
            fi
        fi
    done < "$file"
    
    # Report file-level stats if verbose
    if [[ "${VERBOSE:-0}" == "1" ]] && (( file_declarations > 0 )); then
        local file_coverage=$((file_documented * 100 / file_declarations))
        printf "  %-50s %3d/%3d (%3d%%)\n" "$(basename "$file")" "$file_documented" "$file_declarations" "$file_coverage"
    fi
}

# Main processing
echo "Foundation-Relativity Documentation Coverage Report"
echo "=================================================="
echo ""

# Process each directory
for dir in "${LEAN_DIRS[@]}"; do
    if [[ -d "$PROJECT_ROOT/$dir" ]]; then
        echo "Processing $dir/..."
        
        # Find all .lean files (excluding .olean)
        while IFS= read -r -d '' file; do
            process_file "$file"
        done < <(find "$PROJECT_ROOT/$dir" -name "*.lean" -type f -print0 2>/dev/null)
    fi
done

# Calculate percentages
if (( total_declarations > 0 )); then
    declaration_coverage=$((documented_declarations * 100 / total_declarations))
else
    declaration_coverage=0
fi

if (( total_files > 0 )); then
    header_coverage=$((files_with_header * 100 / total_files))
else
    header_coverage=0
fi

# Output summary
echo ""
echo "Summary"
echo "-------"
echo "Total files processed:        $total_files"
echo "Files with module headers:    $files_with_header ($header_coverage%)"
echo "Total declarations:           $total_declarations"
echo "Documented declarations:      $documented_declarations ($declaration_coverage%)"
echo ""

# Overall coverage (weighted average)
overall_coverage=$(( (declaration_coverage * 2 + header_coverage) / 3 ))

# Color-coded status
if (( overall_coverage >= 80 )); then
    status_color="$GREEN"
    status_text="GOOD"
elif (( overall_coverage >= 60 )); then
    status_color="$YELLOW"
    status_text="FAIR"
else
    status_color="$RED"
    status_text="NEEDS IMPROVEMENT"
fi

echo -e "Overall documentation coverage: ${status_color}${overall_coverage}% - ${status_text}${NC}"

# Output for CI
if [[ -n "$OUTPUT_FILE" ]]; then
    echo "$overall_coverage" > "$OUTPUT_FILE"
fi

# Set GitHub Actions output if running in CI
if [[ -n "${GITHUB_ACTIONS:-}" ]]; then
    echo "coverage=$overall_coverage" >> "$GITHUB_OUTPUT"
    echo "::notice::Documentation coverage: $overall_coverage%"
fi

# Exit with error if coverage is too low (configurable threshold)
THRESHOLD="${DOC_COVERAGE_THRESHOLD:-50}"
if (( overall_coverage < THRESHOLD )); then
    echo ""
    echo "ERROR: Documentation coverage ($overall_coverage%) is below threshold ($THRESHOLD%)"
    exit 1
fi

exit 0