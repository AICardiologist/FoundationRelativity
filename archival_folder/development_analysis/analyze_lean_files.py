#!/usr/bin/env python3
"""
Analyze all Lean files in the repository for Paper 3 planning
"""
import os
import re
import subprocess
from pathlib import Path

def count_sorries(filepath):
    """Count sorry statements in a file"""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
        # Count various forms of sorry
        sorries = len(re.findall(r'\bsorry\b', content, re.IGNORECASE))
        admits = len(re.findall(r'\badmit\b', content, re.IGNORECASE))
        return sorries + admits
    except Exception as e:
        return -1

def get_file_info(filepath):
    """Extract key information about a Lean file"""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Get imports
        imports = re.findall(r'^import\s+([^\n]+)', content, re.MULTILINE)
        
        # Get main structures/definitions
        defs = re.findall(r'^\s*(?:def|structure|class|inductive|theorem|lemma)\s+(\w+)', content, re.MULTILINE)
        
        # Get namespaces
        namespaces = re.findall(r'^namespace\s+([^\n]+)', content, re.MULTILINE)
        
        # Extract docstring
        docstring_match = re.search(r'/\*!(.*?)\*/', content, re.DOTALL)
        docstring = docstring_match.group(1).strip() if docstring_match else ""
        
        # Get line count
        lines = len(content.split('\n'))
        
        return {
            'imports': imports[:5],  # First 5 imports
            'definitions': defs[:10],  # First 10 definitions
            'namespaces': namespaces,
            'docstring': docstring[:200] if docstring else "",  # First 200 chars
            'lines': lines,
            'sorries': count_sorries(filepath)
        }
    except Exception as e:
        return {'error': str(e)}

def analyze_all_lean_files():
    """Analyze all Lean files and generate report"""
    repo_root = Path('.')
    lean_files = list(repo_root.rglob('*.lean'))
    lean_files = [f for f in lean_files if '.lake' not in str(f)]
    lean_files.sort()
    
    results = {}
    
    for filepath in lean_files:
        rel_path = str(filepath)
        results[rel_path] = get_file_info(filepath)
    
    return results

def categorize_files(results):
    """Categorize files by their purpose for Paper 3"""
    categories = {
        'bicategorical': [],
        'paper1': [],
        'paper2': [],
        'paper3': [],
        'paper4': [],
        'old_files': [],
        'foundation_core': [],
        'category_theory': [],
        'scripts': [],
        'tests': []
    }
    
    for filepath, info in results.items():
        if 'bicategorical' in filepath.lower():
            categories['bicategorical'].append((filepath, info))
        elif 'P1_GBC' in filepath or 'paper1' in filepath.lower():
            categories['paper1'].append((filepath, info))
        elif 'P2_BidualGap' in filepath or 'paper2' in filepath.lower():
            categories['paper2'].append((filepath, info))
        elif 'P3_2CatFramework' in filepath or 'paper3' in filepath.lower():
            categories['paper3'].append((filepath, info))
        elif 'P4_SpectralGeometry' in filepath or 'paper4' in filepath.lower():
            categories['paper4'].append((filepath, info))
        elif 'old_files' in filepath or 'archive' in filepath:
            categories['old_files'].append((filepath, info))
        elif 'Found' in filepath or 'foundation' in filepath.lower():
            categories['foundation_core'].append((filepath, info))
        elif 'CategoryTheory' in filepath or 'category' in filepath.lower():
            categories['category_theory'].append((filepath, info))
        elif 'scripts' in filepath or 'test' in filepath:
            if 'test' in filepath.lower():
                categories['tests'].append((filepath, info))
            else:
                categories['scripts'].append((filepath, info))
        else:
            categories['old_files'].append((filepath, info))
    
    return categories

def generate_markdown_report(categories):
    """Generate comprehensive markdown report"""
    
    report = []
    
    # Header
    report.extend([
        "# Paper 3: Comprehensive Lean Codebase Analysis for Foundation-Relativity Framework",
        "",
        "## Executive Summary",
        "",
        "This document provides a systematic catalog of all Lean files in the FoundationRelativity repository, analyzing their content, sorry counts, proof quality, and potential reuse value for Paper 3's bicategorical foundation-relativity framework.",
        "",
        "**Key Finding**: The repository contains substantial bicategorical infrastructure, particularly in `archive/bicategorical/` which provides the core 2-category framework needed for Paper 3.",
        "",
        "---",
        ""
    ])
    
    # Statistics summary
    total_files = sum(len(files) for files in categories.values())
    total_sorries = sum(info.get('sorries', 0) for files in categories.values() for _, info in files if info.get('sorries', 0) > 0)
    
    report.extend([
        "## Repository Statistics",
        "",
        f"- **Total Lean files**: {total_files}",
        f"- **Total sorry statements**: {total_sorries}",
        f"- **Categories analyzed**: {len(categories)}",
        "",
        "---",
        ""
    ])
    
    # Analysis by category
    for cat_name, files in categories.items():
        if not files:
            continue
            
        report.extend([
            f"## {cat_name.replace('_', ' ').title()} Files",
            "",
            f"**Total files**: {len(files)}"
        ])
        
        # Category statistics
        sorry_counts = [info.get('sorries', 0) for _, info in files]
        total_cat_sorries = sum(s for s in sorry_counts if s > 0)
        files_with_sorries = sum(1 for s in sorry_counts if s > 0)
        
        report.extend([
            f"**Files with sorries**: {files_with_sorries}/{len(files)}",
            f"**Total sorries**: {total_cat_sorries}",
            ""
        ])
        
        # Individual file analysis
        for filepath, info in files:
            if 'error' in info:
                continue
                
            sorry_count = info.get('sorries', 0)
            sorry_status = f"**{sorry_count} sorries**" if sorry_count > 0 else "✅ **0 sorries**"
            
            report.extend([
                f"### {filepath}",
                "",
                f"- **Status**: {sorry_status}",
                f"- **Lines**: {info.get('lines', 0)}",
                f"- **Key definitions**: {', '.join(info.get('definitions', [])[:5])}",
                f"- **Namespaces**: {', '.join(info.get('namespaces', []))}",
            ])
            
            if info.get('docstring'):
                report.extend([
                    f"- **Purpose**: {info['docstring'][:150]}{'...' if len(info['docstring']) > 150 else ''}"
                ])
            
            if info.get('imports'):
                report.extend([
                    f"- **Key imports**: {', '.join(info['imports'][:3])}"
                ])
            
            # Reuse assessment
            reuse_value = assess_reuse_value(filepath, info)
            if reuse_value:
                report.extend([
                    f"- **Reuse value**: {reuse_value}"
                ])
            
            report.extend(["", ""])
    
    return "\n".join(report)

def assess_reuse_value(filepath, info):
    """Assess reuse value for Paper 3"""
    if 'bicategorical' in filepath.lower():
        return "🔥 **CRITICAL** - Core bicategorical infrastructure for Paper 3"
    elif 'P3_2CatFramework' in filepath:
        return "🔥 **HIGH** - Direct Paper 3 implementation"
    elif 'CategoryTheory' in filepath or 'category' in filepath.lower():
        return "⚡ **MEDIUM** - Category theory infrastructure"
    elif 'Found' in filepath and 'sorries' in str(info.get('sorries', 0)) and info.get('sorries', 0) == 0:
        return "✅ **MEDIUM** - Foundation infrastructure (complete)"
    elif info.get('sorries', 0) == 0 and info.get('lines', 0) > 50:
        return "✅ **LOW** - Complete implementation, may have utilities"
    elif info.get('sorries', 0) > 10:
        return "❌ **NONE** - Too many incomplete proofs"
    else:
        return "🔍 **TBD** - Needs detailed review"

if __name__ == "__main__":
    print("Analyzing Lean files...")
    results = analyze_all_lean_files()
    categories = categorize_files(results)
    report = generate_markdown_report(categories)
    
    with open('Paper3_Lean_Catalog_Analysis.md', 'w') as f:
        f.write(report)
    
    print(f"Analysis complete! Report written to Paper3_Lean_Catalog_Analysis.md")
    print(f"Total files analyzed: {sum(len(files) for files in categories.values())}")