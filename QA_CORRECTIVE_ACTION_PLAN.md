# QA Corrective Action Plan

**Date:** 2025-08-03  
**Author:** Claude Code (Opus)  
**Purpose:** Address critical QA findings about Papers 2 & 3 formalization

## Executive Summary

QA audit revealed critical issues in ALL THREE PAPERS:
- **Paper 1**: Main Survey Theorem uses `exact ⟨()⟩` - the central result is not actually proved
- **Paper 2**: Not formalized at all - only placeholder stubs
- **Paper 3**: Not formalized at all - only placeholder stubs

All papers compile with "0 sorries" by using Unit tricks instead of real mathematics. This plan outlines the corrective actions required.

## Immediate Actions (Week 0)

### 1. Transparency Updates
- [x] Created CRITICAL_QA_NOTICE.md in repository root
- [x] Updated README.md with warning notice
- [x] Added QA_AUDIT_FINDINGS.md in Papers directory
- [x] Added FORMALIZATION_STATUS.md in Papers 2 & 3 directories
- [x] Updated docs/README.md with warning

### 2. CI Infrastructure (Week 1)
Create and deploy the following tools:

#### a. Cheap Proofs Linter (`scripts/cheap_proofs.lean`)
```lean
-- Detect theorems proved only with Unit/True/trivial
def isHarmless (n : Name) : Bool :=
  n.isInternal || n.isAnonymous ||
  n.getPrefix.isPrefixOf `Init ||
  n == ``Unit || n == ``True || n == ``PUnit
```

#### b. Stub Structure Detector (`scripts/check_struct_stubs.py`)
```python
# Detect structure X where dummy : Unit patterns
UNIT_PAT = re.compile(r'structure\s+\w+\s*:=[^{]*\{\s*dummy\s*:\s*Unit\s*\}')
```

#### c. Alignment Checker (`scripts/check_alignment.py`)
- Parse LaTeX for theorem labels
- Verify Lean has matching declarations
- Check dependencies use real mathematical libraries

### 3. Replace Stubs with Sorry (Week 1)
Transform all placeholder code:

**Before:**
```lean
structure BidualGap where dummy : Unit
theorem gap_equiv_WLPO : BidualGap ↔ WLPO := by
  constructor; · cases; exact ⟨⟨()⟩⟩; · cases; exact ⟨⟨()⟩⟩
```

**After:**
```lean
/-- The bidual gap property for Banach spaces -/
def BidualGap : Prop := 
  ∃ (X : BanachSpace ℝ), ¬Isometric (canonicalEmbedding X)

/-- (LaTeX Theorem 4.1) Main equivalence theorem -/
theorem gap_equiv_WLPO : BidualGap ↔ WLPO := by
  sorry
```

## Phase 1: Paper 1 Cleanup (Weeks 1-3)

### Tasks
1. Fix 12 "cheap" proofs identified by linter
2. Implement `Cat/OrdinalRho.lean`
3. Complete Reflection lemmas properly
4. Remove all Unit-based tricks

### Resources
- In-house team: 2 developers
- External: Ordinal consultant (1 week)

## Phase 2: Core Library Extensions (Weeks 1-6, parallel)

### Analysis Branch
**Lead:** Functional analysis developer  
**Consultant:** Banach space expert (2 weeks)

New modules needed:
- `Analysis/WeakStar.lean` - Weak* topology
- `Analysis/Goldstine.lean` - Goldstine's theorem
- `Analysis/BidualIsometry.lean` - Canonical embedding
- `Analysis/QuantitativeGap.lean` - ε-estimates

### Category Branch
**Lead:** Category theory developer  
**Consultant:** Higher category expert (3 weeks)

New modules needed:
- `Cat/Bicategory/GPS.lean` - Coherence conditions
- `Cat/Found.lean` - 2-category of foundations
- `Cat/PseudoFunctor/OplaxLimit.lean` - Limits
- `Cat/RhoHierarchy.lean` - Ordinal metric

### Logic Branch
**Lead:** Logic developer  
**Consultant:** Constructive logic expert (1 week)

New modules needed:
- `Logic/WLPO.lean` - Formal WLPO definition
- `Logic/ConstructiveBridge.lean` - Classical bridges

## Phase 3: Paper 2 Formalization (Weeks 4-8)

### Week 4-5: Basic Definitions
```lean
def BidualSpace (X : BanachSpace ℝ) := (X.dual).dual
def canonicalEmbedding (X : BanachSpace ℝ) : X →L[ℝ] BidualSpace X
def BidualGap : Prop := ∃ X, ¬Isometric (canonicalEmbedding X)
```

### Week 6-7: Main Theorems
- Implement gap_equiv_WLPO using real functional analysis
- Prove quantitative bounds from §4 of paper

### Week 8: Integration & Polish
- Remove all sorries
- Add cross-references to LaTeX

## Phase 4: Paper 3 Formalization (Weeks 6-12)

### Week 6-8: Foundation Setup
- Implement full `Found` 2-category
- Add GPS coherence machinery

### Week 9-10: Main Constructions
- Define Gap⟂ pseudo-functor
- Implement ρ-hierarchy

### Week 11-12: Obstruction Theorem
- Prove Functorial Obstruction Theorem
- Complete all examples

## Success Criteria

### CI Must Pass These Checks
1. `lake exe sorry_count` → 0
2. `lake exe cheap_proofs` → No output
3. `python scripts/check_struct_stubs.py` → Pass
4. `python scripts/check_alignment.py` → 100% coverage

### Code Review Requirements
- Every theorem references LaTeX section
- Every proof uses real mathematical definitions
- No Unit/True/() tricks anywhere
- External reviewers sign off

## Risk Mitigation

### High Risk Items
1. **GPS Coherence** - Very technical, error-prone
   - Mitigation: Start early with expert guidance
   
2. **Quantitative Estimates** - Not in mathlib
   - Mitigation: Build custom library with tests

3. **WLPO Bridge** - Constructive/classical mix
   - Mitigation: Clear separation of concerns

## Timeline Summary

| Week | Paper 1 | Core Libs | Paper 2 | Paper 3 |
|------|---------|-----------|---------|---------|
| 1    | Cleanup | Start all | Stubs   | -       |
| 2    | Ordinal | Build     | -       | -       |
| 3    | Finish  | Build     | -       | -       |
| 4    | ✅      | Build     | Start   | -       |
| 5    | ✅      | Build     | Defs    | -       |
| 6    | ✅      | Finish    | Thms    | Start   |
| 7    | ✅      | ✅        | Prove   | Found   |
| 8    | ✅      | ✅        | Finish  | GPS     |
| 9    | ✅      | ✅        | ✅      | Functor |
| 10   | ✅      | ✅        | ✅      | ρ-hier  |
| 11   | ✅      | ✅        | ✅      | Obstr   |
| 12   | ✅      | ✅        | ✅      | Finish  |

## Conclusion

This plan transforms the repository from "compiles with tricks" to "genuinely formalized mathematics". The key is enforcing the no-shortcuts rules through CI and maintaining transparency about actual progress.