# Paper 1: Rank-One Toggle Kernel (Minimal Lean Implementation)

## Overview

**Updated Focus (Post-Paper 2)**: Following the completion of Paper 2's WLPO ↔ BidualGap formalization, Paper 1 has been refocused to a minimal, library-quality implementation of the **rank-one toggle kernel** operator theory. This provides reusable mathematical components for mathlib4 while supporting the higher-level foundation-relativity narrative.

## New Scope: Minimal Lean Work Plan

### What We're Building
A self-contained, axiom-clean formalization of:
- **Rank-one toggle operator**: `G(c) := id - c·P` where `c ∈ {false, true}` and `P` is a rank-one projection
- **Spectral analysis**: Complete spectrum and essential spectrum computations
- **Sherman-Morrison formula**: For projection operators `(I + αP)⁻¹ = I - α/(1+α)P`
- **Fredholm theory**: Index calculations for the toggle operator
- **Block decomposition**: Kernel/range characterizations and injectivity/surjectivity equivalences

### What's Out of Scope (By Design)
- Meta-level Gödel bridge (Prop/Type barrier) - conceptual only
- Banach limits and ℓ∞/c₀ examples - covered in Paper 2
- Bicategorical Found layer - reserved for Paper 3
- Full Gödel incompleteness formalization - replaced by focused operator theory

## Current Status (Implementation Progress)

### Module Structure (August 2025 Update)

| Module | Purpose | Status | Sorry Count |
|--------|---------|--------|-------------|
| RankOneToggle/Projection.lean | Orthogonal projection API | ✅ **Complete** | **0** |
| RankOneToggle/Toggle.lean | G(c) operator definition | ✅ **Complete** | **0** |
| RankOneToggle/Spectrum.lean | Spectral computations | ✅ **Complete** | **0** |
| **RankOneToggle/ShermanMorrison.lean** | **Inverse formulas + norm bounds** | ✅ **COMPLETE** | **0** |
| RankOneToggle/Fredholm.lean | Index theory | 📋 Planned | N/A |
| RankOneToggle/Tutorial.lean | Usage examples | 📋 Planned | N/A |

### 🎉 Major Achievement: Sherman-Morrison Implementation Complete!

**Date**: August 22, 2025  
**Status**: ✅ **0 compilation errors, 0 sorries**  
**Key Features**:
- Complete Sherman-Morrison formula for projection operators
- Robust norm bounds using version-stable tactics (no `gcongr`, no `field_simp`)
- Triangle inequality approach with explicit bound `C = ‖α‖ * (1 + ‖P‖)`
- Import-free proof using only `norm_smul_le`, `norm_sub_le`, and basic inequalities

## Deliverables & Acceptance Criteria

### ✅ AC-1: Projection API (COMPLETE)
- ✅ Orthogonal projection onto line spanned by unit vector
- ✅ Proofs: P² = P, P* = P, ‖P‖ = 1, Pu = u
- **File**: `RankOneToggle/Projection.lean` (0 sorries)

### ✅ AC-2: Toggle Operator (COMPLETE)
- ✅ Definition: `G(c) := id - (if c then 1 else 0) • P`
- ✅ Kernel/range characterization
- ✅ Injectivity ↔ Surjectivity ↔ (c = false)
- **File**: `RankOneToggle/Toggle.lean` (0 sorries)

### ✅ AC-3: Spectrum Analysis (COMPLETE)
- ✅ σ(G(false)) = {1}
- ✅ σ(G(true)) = {0,1}
- ✅ Essential spectrum = {1} for both cases
- **File**: `RankOneToggle/Spectrum.lean` (0 sorries)

### ✅ AC-4: Sherman-Morrison (COMPLETE)
- ✅ Formula: `(I + αP).comp (I - α/(1+α)•P) = I` when `1+α ≠ 0`
- ✅ **Robust norm bounds**: Triangle inequality approach with explicit bound
- ✅ **Version-stable proof**: Uses only import-free tactics
- **File**: `RankOneToggle/ShermanMorrison.lean` (0 sorries)

### 📋 AC-5: Fredholm Theory (Planned)
- G(c) is Fredholm with index 0
- dim ker = dim coker = 1 when c = true

### 📋 AC-6: Tutorial & Documentation (Planned)
- Didactic examples showing practical usage
- Mathlib-quality docstrings

## Mathematical Theory

### Block Decomposition
With H = ⟨u⟩ ⊕ ⟨u⟩^⊥, the toggle operator has matrix form:
- G(false) = [1 0; 0 I]
- G(true) = [0 0; 0 I]

This immediately yields kernel/range characterizations and spectral properties.

### Sherman-Morrison Formula
For idempotent P (P² = P):
- (I + αP)(I - α/(1+α)P) = I when 1+α ≠ 0
- Enables explicit resolvent computations

### Essential Spectrum
Rank-one perturbations preserve essential spectrum:
- σ_ess(G(c)) = {1} for both c ∈ {false, true}
- Uses compact perturbation theory from mathlib

## Upstream Strategy for mathlib4

### Planned PRs
1. **PR-A**: Projection-on-a-line helpers
2. **PR-B**: Sherman-Morrison for projections
3. **PR-C**: Toggle operator lemmas (kernel/range, injectivity/surjectivity)
4. **PR-D**: Spectrum/essential spectrum corollaries

### Design Principles
- Small, self-contained PRs
- Follow mathlib naming conventions
- Include comprehensive documentation
- Provide example usage

## Relation to Paper 2

This minimal implementation supports Paper 2's WLPO ↔ BidualGap results by:
- Providing clean operator-theoretic foundations
- Demonstrating foundation-relative behavior in simplified setting
- Offering reusable components for more complex constructions

The rank-one toggle serves as a pedagogical example of how:
- Boolean parameters (c ∈ {false, true}) encode logical choices
- Spectral properties reflect foundation-dependent behavior
- Operator surjectivity connects to constructive principles

## Documentation

- **[New Work Plan](documentation/paper1-lean-work-plan.tex)**: Detailed minimal Lean implementation plan
- **[Original Paper](documentation/)**: Conceptual Gödel-Banach correspondence (archived)
- **[Integration Notes](../P2_BidualGap/documentation/)**: Connection to Paper 2 results

## Build Instructions

```bash
# Build the completed Sherman-Morrison implementation
lake build Papers.P1_GBC.RankOneToggle.ShermanMorrison

# Build all completed Paper 1 modules
lake build Papers.P1_GBC.RankOneToggle.Projection
lake build Papers.P1_GBC.RankOneToggle.Toggle  
lake build Papers.P1_GBC.RankOneToggle.Spectrum

# Run tutorial examples (when implemented)
lake env lean Papers/P1_GBC/RankOneToggle/Tutorial.lean
```

## Status Summary

**Major Achievement**: Sherman-Morrison implementation complete with 0 sorries (August 22, 2025)  
**Scope**: Library-quality operator theory components ready for mathlib4 PRs  
**Connection**: Supports Paper 2's foundation-relativity narrative with concrete mathematical implementations  
**Next Steps**: Complete Fredholm theory and Tutorial modules, prepare upstream PRs

### Ready for mathlib4 Contribution
The completed Sherman-Morrison implementation demonstrates:
- **Version-stable proofs**: No fragile tactics or complex algebraic normalization
- **Import-free approach**: Uses only basic norm inequalities available across mathlib versions  
- **Clean mathematical API**: Self-contained projection and toggle operator theory
- **Comprehensive coverage**: Projection API, toggle operators, spectral analysis, and robust norm bounds