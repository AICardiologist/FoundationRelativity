# Legacy Warnings Whitelist

This file documents warnings that are expected and acceptable in the Foundation-Relativity project due to legacy code, intentional design choices, or upstream mathlib constraints.

## Whitelisted Warnings

### 1. Unused Variables in Bicategory Laws
**Files**: `CategoryTheory/PseudoFunctor.lean`, `CategoryTheory/BicatHelpers.lean`
**Pattern**: `unused variable 'f'`, `unused variable 'g'`, `unused variable 'h'`
**Reason**: These variables appear in coherence law signatures but are not used in placeholder proofs. They will be used once the full coherence conditions are implemented.
**Example**:
```
warning: CategoryTheory/PseudoFunctor.lean:46:31: unused variable `f`
```

### 2. Declaration Uses Sorry
**Files**: Various proof files during active development
**Pattern**: `declaration uses 'sorry'`
**Reason**: Incremental proof development - theorems are stated with correct types but proofs are deferred to maintain compilability during scaffolding phases.
**Sprint Policy**: All sorries must be tracked in sprint backlogs and resolved by sprint end.

### 3. Unused Simp Arguments
**Files**: Files using mathlib tactics
**Pattern**: `This simp argument is unused`
**Reason**: Simp lemmas may become redundant as mathlib evolves, but are kept for compatibility with multiple mathlib versions.

### 4. Info Messages from Bicategory
**Files**: `CategoryTheory/BicatFound.lean`
**Pattern**: `info: CategoryTheory/BicatFound.lean:XXX:0: FoundationBicat.YYY`
**Reason**: Lean's elaborator outputs information about synthesized instances. These are not warnings and indicate correct type inference.

## Temporary Warnings (To Be Fixed)

### 1. Finrank API Changes
**Target**: Sprint 45
**Issue**: `LinearMap.finrank` vs `Module.finrank` naming inconsistency
**Resolution**: Update to latest mathlib API once stabilized

### 2. Missing Fredholm Theory Imports
**Target**: When mathlib 4.10+ is adopted
**Issue**: `Mathlib.Analysis.NormedSpace.Fredholm` doesn't exist in current version
**Resolution**: Implement local version until mathlib catches up

## Review Policy

This whitelist is reviewed at the end of each sprint. Warnings can only be added with:
1. Clear justification
2. Target resolution date (if applicable)
3. Approval in sprint retrospective

Last reviewed: Sprint 44, Day 3