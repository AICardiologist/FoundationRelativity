#!/bin/bash
# leanink_stats.sh - Calculate automation metrics for Lean proofs
# Sprint 44 Day 3: Automation statistics for KPI tracking

set -euo pipefail

# Configuration
PROJECT_ROOT="${PROJECT_ROOT:-$(git rev-parse --show-toplevel 2>/dev/null || pwd)}"
# Default directories
LEAN_DIRS=("CategoryTheory" "AnalyticPathologies" "Papers" "Found")
OUTPUT_JSON="${1:-automation_stats.json}"

# Counters
total_proof_lines=0
manual_proof_lines=0
tactic_proof_lines=0
sorry_count=0
axiom_count=0
total_theorems=0
total_lemmas=0
total_examples=0

# Tactic patterns that indicate automation
AUTOMATION_TACTICS="simp|aesop|norm_num|ring|field_simp|linarith|omega|decide|ext|rfl|trivial|exact"
MANUAL_INDICATORS="rw|rewrite|cases|induction|constructor|intro|apply|refine|have|obtain|use"

# Track LeanInk regions
in_leanink_region=false

# Function to classify proof lines
classify_proof_line() {
    local line="$1"
    
    # Skip if in LeanInk region
    if [[ "$line" =~ --[[:space:]]*LeanInk:[[:space:]]*begin_count ]]; then
        in_leanink_region=true
        return 1
    fi
    if [[ "$line" =~ --[[:space:]]*LeanInk:[[:space:]]*end_count ]]; then
        in_leanink_region=false
        return 1
    fi
    if [[ "$in_leanink_region" == true ]]; then
        ((manual_proof_lines++))
        return 0
    fi
    
    # Check for automation tactics
    if [[ "$line" =~ ($AUTOMATION_TACTICS) ]]; then
        ((tactic_proof_lines++))
        return 0
    fi
    
    # Check for manual proof indicators
    if [[ "$line" =~ ($MANUAL_INDICATORS) ]]; then
        ((manual_proof_lines++))
        return 0
    fi
    
    return 1
}

# Function to process a Lean file
process_file() {
    local file="$1"
    local in_proof=false
    local proof_indent=0
    
    while IFS= read -r line; do
        # Count sorry
        if [[ "$line" =~ sorry ]]; then
            ((sorry_count++))
        fi
        
        # Count axiom declarations
        if [[ "$line" =~ ^[[:space:]]*axiom[[:space:]]+ ]]; then
            ((axiom_count++))
        fi
        
        # Count theorem/lemma/example
        if [[ "$line" =~ ^[[:space:]]*(theorem|lemma)[[:space:]]+ ]]; then
            ((total_theorems++))
            in_proof=false
        elif [[ "$line" =~ ^[[:space:]]*example[[:space:]]+ ]]; then
            ((total_examples++))
            in_proof=false
        fi
        
        # Track proof blocks
        if [[ "$line" =~ :=[[:space:]]*by$ ]] || [[ "$line" =~ ^[[:space:]]*by$ ]]; then
            in_proof=true
            proof_indent=$(echo "$line" | sed 's/[^ ].*//' | wc -c)
            continue
        fi
        
        # End of proof detection (dedent or new declaration)
        if [[ "$in_proof" == true ]]; then
            current_indent=$(echo "$line" | sed 's/[^ ].*//' | wc -c)
            if (( current_indent <= proof_indent )) && [[ -n "$(echo "$line" | tr -d ' ')" ]]; then
                in_proof=false
            fi
        fi
        
        # Process proof lines
        if [[ "$in_proof" == true ]] && [[ -n "$(echo "$line" | tr -d ' ')" ]]; then
            ((total_proof_lines++))
            classify_proof_line "$line"
        fi
    done < "$file"
}

# Generate statistics report
generate_report() {
    local automation_ratio=0
    if (( total_proof_lines > 0 )); then
        automation_ratio=$(awk "BEGIN {printf \"%.1f\", $tactic_proof_lines * 100.0 / $total_proof_lines}")
    fi
    
    local sorry_ratio=0
    local total_proofs=$((total_theorems + total_examples))
    if (( total_proofs > 0 )); then
        sorry_ratio=$(awk "BEGIN {printf \"%.1f\", $sorry_count * 100.0 / $total_proofs}")
    fi
    
    cat > "$OUTPUT_JSON" <<EOF
{
  "timestamp": "$(date -u +"%Y-%m-%dT%H:%M:%SZ")",
  "commit": "$(git rev-parse HEAD 2>/dev/null || echo "unknown")",
  "summary": {
    "total_proof_lines": $total_proof_lines,
    "automated_lines": $tactic_proof_lines,
    "manual_lines": $manual_proof_lines,
    "automation_percentage": $automation_ratio,
    "total_theorems": $total_theorems,
    "total_examples": $total_examples,
    "sorry_count": $sorry_count,
    "sorry_percentage": $sorry_ratio,
    "axiom_count": $axiom_count
  },
  "breakdown": {
    "by_tactic": {
      "automated": $tactic_proof_lines,
      "manual": $manual_proof_lines,
      "unclassified": $((total_proof_lines - tactic_proof_lines - manual_proof_lines))
    }
  }
}
EOF
}

# Main processing
echo "Foundation-Relativity Automation Metrics"
echo "========================================"
echo ""

# Reset LeanInk state
in_leanink_region=false

# Process each directory
for dir in "${LEAN_DIRS[@]}"; do
    if [[ -d "$PROJECT_ROOT/$dir" ]]; then
        echo "Processing $dir/..."
        
        # Find all .lean files
        while IFS= read -r -d '' file; do
            process_file "$file"
        done < <(find "$PROJECT_ROOT/$dir" -name "*.lean" -type f -print0 2>/dev/null)
    fi
done

# Generate report
generate_report

# Display summary
echo ""
echo "Summary"
echo "-------"
echo "Total proof lines:     $total_proof_lines"
echo "Automated lines:       $tactic_proof_lines"
echo "Manual proof lines:    $manual_proof_lines"
echo "Theorems/Lemmas:       $total_theorems"
echo "Examples:              $total_examples"
echo "Sorry count:           $sorry_count"
echo "Axiom count:           $axiom_count"
echo ""

if (( total_proof_lines > 0 )); then
    automation_pct=$(awk "BEGIN {printf \"%.1f\", $tactic_proof_lines * 100.0 / $total_proof_lines}")
    echo "Automation rate:       ${automation_pct}%"
fi

echo ""
echo "Report saved to: $OUTPUT_JSON"

# GitHub Actions output
if [[ -n "${GITHUB_ACTIONS:-}" ]]; then
    echo "automation_rate=$automation_pct" >> "$GITHUB_OUTPUT"
    echo "sorry_count=$sorry_count" >> "$GITHUB_OUTPUT"
    echo "::notice::Proof automation rate: ${automation_pct}%"
fi

exit 0