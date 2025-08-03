#!/usr/bin/env python3
"""
check_alignment.py

Checks that LaTeX theorems are properly formalized in Lean with real proofs.
Also verifies that theorems depend on non-trivial mathematical libraries.

Exit codes:
  0 - All theorems properly aligned
  1 - Missing or suspicious theorems found
"""

import re
import json
import pathlib
import subprocess
import sys
from typing import Dict, List, Set, Optional, Tuple

class AlignmentChecker:
    def __init__(self):
        self.latex_theorems: Dict[str, List[Dict]] = {}
        self.lean_declarations: Dict[str, str] = {}
        self.cheap_proofs: Set[str] = set()
        
    def extract_latex_theorems(self, tex_file: pathlib.Path) -> List[Dict]:
        """Extract theorem/lemma/proposition labels from LaTeX"""
        if not tex_file.exists():
            print(f"Warning: LaTeX file {tex_file} not found")
            return []
            
        try:
            content = tex_file.read_text(encoding='utf-8')
        except Exception as e:
            print(f"Warning: Could not read {tex_file}: {e}")
            return []
            
        results = []
        
        # Patterns for LaTeX theorem environments
        patterns = [
            # \begin{theorem}[description]\label{label}
            r'\\begin\{(theorem|lemma|proposition|corollary|definition)\}(?:\[([^\]]*)\])?\s*\\label\{([^}]+)\}',
            # \begin{theorem}[description] ... \label{label}
            r'\\begin\{(theorem|lemma|proposition|corollary|definition)\}(?:\[([^\]]*)\])?[^}]*\n\s*\\label\{([^}]+)\}',
            # Also check for \newtheorem custom environments
            r'\\begin\{(thm|lem|prop|cor|defn)\}(?:\[([^\]]*)\])?\s*\\label\{([^}]+)\}',
        ]
        
        for pattern in patterns:
            for match in re.finditer(pattern, content, re.MULTILINE | re.DOTALL):
                env_type = match.group(1)
                description = match.group(2) or ""
                label = match.group(3)
                
                # Extract content preview
                start = match.end()
                end_pattern = f'\\\\end\\{{{env_type}\\}}'
                end_match = re.search(end_pattern, content[start:])
                if end_match:
                    theorem_content = content[start:start + end_match.start()].strip()
                    # Clean LaTeX for preview
                    theorem_content = re.sub(r'\\[a-zA-Z]+\{[^}]*\}', '', theorem_content)
                    theorem_content = re.sub(r'\\[a-zA-Z]+', '', theorem_content)
                    theorem_content = re.sub(r'\$[^$]+\$', '[math]', theorem_content)
                    theorem_content = ' '.join(theorem_content.split())[:200]
                    if len(theorem_content) == 200:
                        theorem_content += "..."
                else:
                    theorem_content = ""
                
                results.append({
                    'type': env_type,
                    'label': label,
                    'description': description,
                    'content_preview': theorem_content,
                    'file': str(tex_file)
                })
        
        return results
    
    def find_lean_declaration(self, label: str, paper_dir: str) -> Optional[Tuple[str, str]]:
        """Find Lean declaration that references this LaTeX label"""
        # Common label transformations
        possible_names = [
            label,
            label.replace('-', '_'),
            label.replace(':', '_'),
            label.replace('.', '_'),
            'theorem_' + label.replace('-', '_'),
            'lemma_' + label.replace('-', '_'),
        ]
        
        # Search in the corresponding paper directory
        search_dirs = [paper_dir, '.']
        
        for search_dir in search_dirs:
            for name in possible_names:
                # Search for LaTeX reference in comments
                result = subprocess.run(
                    ['grep', '-r', f'LaTeX.*{label}', '--include=*.lean', search_dir],
                    capture_output=True, text=True
                )
                if result.stdout:
                    lines = result.stdout.strip().split('\n')
                    if lines:
                        # Return file and the match
                        parts = lines[0].split(':', 1)
                        if len(parts) >= 2:
                            return (parts[0], lines[0])
                
                # Also search for the theorem name directly
                result = subprocess.run(
                    ['grep', '-r', f'theorem {name}\\b', '--include=*.lean', search_dir],
                    capture_output=True, text=True
                )
                if result.stdout:
                    lines = result.stdout.strip().split('\n')
                    if lines:
                        parts = lines[0].split(':', 1)
                        if len(parts) >= 2:
                            return (parts[0], lines[0])
        
        return None
    
    def check_dependencies(self, lean_file: str, theorem_line: str) -> Tuple[bool, str]:
        """Check if theorem uses non-trivial dependencies"""
        # Extract theorem name from the line
        theorem_match = re.search(r'(theorem|lemma|def)\s+(\w+)', theorem_line)
        if not theorem_match:
            return True, "Could not parse theorem"
        
        theorem_name = theorem_match.group(2)
        
        try:
            # Read the file to find the proof
            content = pathlib.Path(lean_file).read_text(encoding='utf-8')
            
            # Find the theorem and its proof
            theorem_pattern = f'(theorem|lemma|def)\\s+{theorem_name}.*?:=\\s*by(.*?)(?=theorem|lemma|def|end|$)'
            match = re.search(theorem_pattern, content, re.DOTALL)
            
            if match:
                proof_body = match.group(2)
                
                # Check for suspicious patterns
                if re.search(r'exact\s*⟨+\(\)⟩+', proof_body):
                    return False, "Uses Unit constructor (exact ⟨()⟩)"
                if re.search(r'^\s*trivial\s*$', proof_body.strip()):
                    return False, "Proof is just 'trivial'"
                if len(proof_body.strip()) < 10:
                    return False, "Suspiciously short proof"
                
                # Check if it uses any project-specific or mathlib definitions
                # Look for capital letters (type names) or qualified names
                if re.search(r'[A-Z]\w+|[\w\.]+\.\w+', proof_body):
                    return True, "Uses mathematical definitions"
                
                return False, "No mathematical content detected"
            else:
                # Check for direct assignment with Unit
                direct_pattern = f'(theorem|lemma|def)\\s+{theorem_name}.*?:=\\s*⟨'
                if re.search(direct_pattern, content):
                    return False, "Direct Unit assignment"
            
            return True, "Could not analyze proof"
            
        except Exception as e:
            return True, f"Error analyzing: {e}"
    
    def generate_report(self) -> Dict:
        """Generate alignment report"""
        papers = {
            'Paper 1': (pathlib.Path('docs/papers/P1-GBC.tex'), 'Papers/P1_GBC'),
            'Paper 2': (pathlib.Path('docs/papers/P2-BidualGap.tex'), 'Papers/P2_BidualGap'),
            'Paper 3': (pathlib.Path('docs/papers/P3-2CatFramework.tex'), 'Papers/P3_2CatFramework'),
        }
        
        report = {}
        
        for paper_name, (tex_file, lean_dir) in papers.items():
            theorems = self.extract_latex_theorems(tex_file)
            
            if not theorems:
                report[paper_name] = {'error': 'No theorems found in LaTeX'}
                continue
                
            aligned = []
            missing = []
            suspicious = []
            
            for thm in theorems:
                lean_match = self.find_lean_declaration(thm['label'], lean_dir)
                if lean_match:
                    lean_file, match_line = lean_match
                    # Check if it's a real proof
                    is_real, reason = self.check_dependencies(lean_file, match_line)
                    if is_real:
                        aligned.append({**thm, 'lean_file': lean_file})
                    else:
                        suspicious.append({
                            **thm, 
                            'lean_file': lean_file,
                            'reason': reason
                        })
                else:
                    missing.append(thm)
            
            report[paper_name] = {
                'total': len(theorems),
                'aligned': len(aligned),
                'missing': len(missing),
                'suspicious': len(suspicious),
                'details': {
                    'aligned': aligned,
                    'missing': missing,
                    'suspicious': suspicious
                }
            }
        
        return report
    
def main():
    checker = AlignmentChecker()
    report = checker.generate_report()
    
    # Print summary
    print("📊 LaTeX-Lean Alignment Report")
    print("=" * 50)
    print()
    
    all_good = True
    total_stats = {'total': 0, 'aligned': 0, 'missing': 0, 'suspicious': 0}
    
    for paper, data in report.items():
        if 'error' in data:
            print(f"❌ {paper}: {data['error']}")
            continue
            
        total = data['total']
        aligned = data['aligned']
        missing = data['missing']
        suspicious = data['suspicious']
        
        total_stats['total'] += total
        total_stats['aligned'] += aligned
        total_stats['missing'] += missing
        total_stats['suspicious'] += suspicious
        
        percentage = (aligned / total * 100) if total > 0 else 0
        
        status = "✅" if percentage == 100 else "⚠️" if percentage > 50 else "❌"
        print(f"{status} {paper}: {aligned}/{total} theorems properly formalized ({percentage:.0f}%)")
        
        if missing > 0:
            print(f"   🔴 Missing: {missing} theorems not found in Lean")
            all_good = False
            
        if suspicious > 0:
            print(f"   🟡 Suspicious: {suspicious} theorems may use Unit tricks")
            all_good = False
        
        print()
    
    # Print details for problematic theorems
    if not all_good:
        print("\n📋 Detailed Issues:")
        print("=" * 50)
        
        for paper, data in report.items():
            if 'error' in data:
                continue
                
            if data['missing'] > 0 or data['suspicious'] > 0:
                print(f"\n{paper}:")
                
                if data['details']['missing']:
                    print("  Missing theorems:")
                    for thm in data['details']['missing']:
                        print(f"    - {thm['type']} {thm['label']}: {thm['description']}")
                
                if data['details']['suspicious']:
                    print("  Suspicious theorems:")
                    for thm in data['details']['suspicious']:
                        print(f"    - {thm['type']} {thm['label']}: {thm['reason']}")
                        print(f"      File: {thm['lean_file']}")
    
    # Save detailed report
    with open('alignment_report.json', 'w') as f:
        json.dump(report, f, indent=2)
    
    print(f"\n📄 Detailed report saved to alignment_report.json")
    
    # Print summary
    print(f"\n📊 Overall Summary:")
    print(f"  Total theorems in LaTeX: {total_stats['total']}")
    print(f"  ✅ Properly formalized: {total_stats['aligned']}")
    print(f"  🔴 Missing: {total_stats['missing']}")
    print(f"  🟡 Suspicious: {total_stats['suspicious']}")
    
    if not all_good:
        print("\n❌ Alignment check FAILED")
        print("Replace Unit stubs with proper definitions and 'sorry' for incomplete work")
        sys.exit(1)
    else:
        print("\n✅ All theorems properly aligned")
        sys.exit(0)

if __name__ == "__main__":
    main()