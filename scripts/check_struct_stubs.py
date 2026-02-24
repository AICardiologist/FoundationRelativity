#!/usr/bin/env python3
"""
check_struct_stubs.py

Detects Unit stub structures and trivial Prop definitions that are used
to fake "0 sorries" status without real formalization.

Exit codes:
  0 - No stubs found
  1 - Stubs detected
"""

import re
import sys
import pathlib
from typing import List, Tuple

# Patterns that indicate stub structures
STUB_PATTERNS = [
    # structure X where dummy : Unit
    (re.compile(r'structure\s+(\w+)\s*(?:where|:=)[^{]*\{\s*dummy\s*:\s*Unit\s*\}'), 
     "Unit stub structure"),
    # structure X := (dummy : Unit)
    (re.compile(r'structure\s+(\w+)\s*:=\s*\(\s*dummy\s*:\s*Unit\s*\)'), 
     "Unit stub structure"),
    # def X : Prop := True
    (re.compile(r'def\s+(\w+)\s*:\s*Prop\s*:=\s*True\b'), 
     "Trivial Prop definition"),
    # abbrev X := Unit
    (re.compile(r'abbrev\s+(\w+)\s*:=\s*Unit\b'), 
     "Unit type alias"),
    # structure X where field : True
    (re.compile(r'structure\s+(\w+)\s*(?:where|:=)[^{]*\{\s*\w+\s*:\s*True\s*\}'), 
     "True stub structure"),
]

# Patterns for vacuous proofs
VACUOUS_PROOF_PATTERNS = [
    # exact ⟨()⟩ or exact ⟨⟨()⟩⟩
    (re.compile(r'exact\s*⟨+\(\)⟩+'), "Unit constructor proof"),
    # by trivial (as only tactic)
    (re.compile(r':\s*by\s+trivial\s*(?:--[^\n]*)?$'), "Trivial-only proof"),
    # := ⟨()⟩
    (re.compile(r':=\s*⟨+\(\)⟩+'), "Direct Unit constructor"),
    # constructor; exact ⟨()⟩ patterns
    (re.compile(r'constructor\s*[;·]\s*(?:intro\s+\w+\s*[;·]\s*)?(?:cases\s+\w+\s*[;·]\s*)?exact\s*⟨'), 
     "Constructor with Unit exact"),
]

def scan_file(filepath: pathlib.Path) -> List[Tuple[str, int, str, str]]:
    """
    Scan a file for stub patterns.
    Returns list of (type, line_no, content, description)
    """
    issues = []
    
    try:
        content = filepath.read_text(encoding='utf-8')
    except Exception as e:
        print(f"Warning: Could not read {filepath}: {e}")
        return issues
    
    lines = content.split('\n')
    
    # Check for stub structures
    for pattern, description in STUB_PATTERNS:
        for match in pattern.finditer(content):
            line_no = content[:match.start()].count('\n') + 1
            struct_name = match.group(1) if match.lastindex else "unknown"
            matched_text = match.group(0).replace('\n', ' ')
            issues.append(("stub_structure", line_no, 
                          f"Structure '{struct_name}': {matched_text}", 
                          description))
    
    # Check for vacuous proofs
    for i, line in enumerate(lines, 1):
        for pattern, description in VACUOUS_PROOF_PATTERNS:
            if pattern.search(line):
                issues.append(("vacuous_proof", i, 
                             f"Line content: {line.strip()}", 
                             description))
    
    return issues

def main():
    root = pathlib.Path('.')
    all_issues = []
    
    # Directories to skip
    skip_dirs = {'.lake', 'lake-packages', '.git', 'build', '.github', 'examples',
                 'WIP', 'standalone', 'old_paper_abandoned', 'paper_2_redo',
                 'Archived', 'zenodo', 'archive_old_pdfs'}

    # Also skip frozen published paper directories (Zenodo-archived, reproducibility-locked)
    skip_prefixes = ('paper ', 'Paper ')
    
    # Find all Lean files
    lean_files = []
    for lean_file in root.rglob('*.lean'):
        # Skip if in excluded directory
        if any(part in skip_dirs for part in lean_file.parts):
            continue

        # Skip frozen published paper directories
        if any(part.startswith(skip_prefixes) for part in lean_file.parts):
            continue
        
        # Skip generated files
        if 'lake-build' in str(lean_file) or lean_file.name.endswith('.ilean'):
            continue
        
        # Skip Axioms.lean as mentioned in rules
        if 'Axioms.lean' in lean_file.name:
            continue
            
        lean_files.append(lean_file)
    
    # Scan each file
    for lean_file in sorted(lean_files):
        issues = scan_file(lean_file)
        if issues:
            all_issues.append((lean_file, issues))
    
    # Report results
    if all_issues:
        print("❌ Stub structures and vacuous proofs detected:\n")
        
        stub_count = 0
        proof_count = 0
        
        for filepath, issues in all_issues:
            print(f"📄 {filepath}:")
            for issue_type, line_no, content, description in issues:
                if issue_type == "stub_structure":
                    icon = "🔲"
                    stub_count += 1
                else:
                    icon = "⭕"
                    proof_count += 1
                print(f"  {icon} Line {line_no}: {description}")
                print(f"     {content}")
            print()
        
        print(f"Summary:")
        print(f"  🔲 Stub structures: {stub_count}")
        print(f"  ⭕ Vacuous proofs: {proof_count}")
        print(f"  ❌ Total issues: {stub_count + proof_count}")
        print("\nReplace these with proper definitions and 'sorry' for incomplete proofs.")
        sys.exit(1)
    else:
        print("✅ No stub structures or vacuous proofs found")
        sys.exit(0)

if __name__ == "__main__":
    main()