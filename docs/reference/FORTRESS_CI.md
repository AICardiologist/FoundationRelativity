# Fortress CI System

## Overview

The Fortress CI system provides comprehensive protection for the mathematical formalization with an 8-stage guard system that ensures axiom hygiene and proof integrity.

## Usage

### Full Guard System
```bash
lake run fullGuard
```

Runs all protection stages:
1. **Constructive Guard**: Axiom hygiene protection
2. **Sorry Scanner**: Hidden sorry detection
3-8. **Smoke Tests**: Core mathematical components

### Individual Guards
```bash
# Axiom hygiene only
lake run axiomGuard

# Sorry detection only  
lake run sorryGuard
```

## Protection Stages

### Stage 1-2: Core Protection
- **Constructive Guard**: Ensures core theorems use only standard axioms
- **Sorry Scanner**: Detects hidden sorries with robust file handling

### Stage 3-8: Mathematical Integrity
- **FiniteCesaro Tests**: Basic mathematical infrastructure
- **BooleanSubLattice Tests**: §3.3 residue class partitions
- **IndicatorSpec Tests**: §3.1 core equivalence framework
- **IndicatorEventual Tests**: finite ↔ eventually zero bridges
- **C0Spec Tests**: eventually zero ↔ c₀-spec bridges  
- **Iota Tests**: §3.2-3.5 ι embedding and lattice homomorphism

## Expected Output

```
🔒 Constructive Guard: Core theorems axiom audit complete
✅ Expected clean theorems should show only: [propext, Classical.choice, Quot.sound]
🎯 SUCCESS: core constructive theorems axiom‑clean; no Compat imports.
🎯 SUCCESS: no real 'sorry' tokens detected
[Build outputs for each smoke test stage]
🛡️ All guards passed - fortress secure!
```

## Architecture

### Axiom Hygiene
- Pattern matching for contamination detection
- Explicit axiom audit of core theorems
- Protection against accidental `sorryAx` usage

### File Robustness
- Robust file producers using `|| true` concatenation
- Nested comment-aware filtering
- Pin-friendly style guards

### Exit Code Propagation
- Each stage returns distinct exit codes (1-8)
- Allows CI systems to identify specific failure points
- Fail-fast behavior stops on first failure

## Files

- `lakefile.lean`: Main guard system implementation
- `scripts/constructive_guard.sh`: Axiom hygiene checker
- `scripts/sorry_scan.sh`: Sorry detection with robust file handling
- `scripts/strip_lean_comments.awk`: Nested comment filtering

## Integration

The fortress system integrates with:
- Local development workflows (`lake run fullGuard`)
- CI/CD pipelines via exit code checking
- Paper 3 pre-commit hooks (demonstrated in commit logs)
- Future axiom gate workflows