# Consultant Documentation Index

## Active Documents

### 1. Critical Corrections (ESSENTIAL)
**File**: `consultant-critical-corrections.md`  
**Status**: Essential reference document  
**Content**: Documents fundamental errors identified by consultant and their corrections
- Wrong theorem (eigenvalue vs Rayleigh quotient)
- Wrong geometry (n vs 2n edges)
- Invalid model (negative weights)
- Missing scaling (n = C/h requirement)

### 2. Current Technical Questions
**File**: `consultant-question-perturbation-coefficient.md`  
**Status**: Active consultation  
**Content**: Latest specific technical questions about:
- Perturbation coefficient derivation
- n-dependence in bounds
- Sturm's theorem implementation
- Primitive recursive encoding

### 3. Future Implementation Strategy
**File**: `consultant-smooth-case-strategy.md`  
**Status**: Future roadmap  
**Content**: Strategy for smooth manifold case using IFT approach
- Three-phase implementation plan
- Implicit Function Theorem methodology
- Long-term vision (24-36 months)

## Archived Documents

The following consultant documents have been archived to `docs/archive/obsolete-2025-08/`:
- `consultant-question-final.md` - Superseded by more specific questions
- `consultant-questions-phase2.md` - General questions refined in later docs
- `consultant-third-letter.md` - Detailed discussion covered in corrections

## Usage Guide

1. **For understanding errors**: Read `consultant-critical-corrections.md` first
2. **For current work**: Reference `consultant-question-perturbation-coefficient.md`
3. **For future planning**: See `consultant-smooth-case-strategy.md`

## Key Takeaways

The consultant interaction revealed critical mathematical errors that required fundamental corrections to our approach. The corrected implementation is now in:
- `Papers/P4_SpectralGeometry/Discrete/ConsultantBoundsRevised.lean`

Always reference the critical corrections document when working on Paper 4 implementation.