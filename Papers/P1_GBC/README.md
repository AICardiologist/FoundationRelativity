# Paper 1: Rank-One Toggle Kernel

## Overview

Paper 1 delivers a minimal, reusable operator-theory core around the rank-one toggle
G(c) := id - c·P on Hilbert spaces. We provide a clean formalization of orthogonal projections,
toggle operators, and the Sherman-Morrison formula for rank-one perturbations.

## Current Status (September 2025)

**Total sorries: 13** distributed across:
- ShermanMorrison: 1 (optional norm bound)
- Spectrum: 3 (pending mathlib operator algebra API)
- Fredholm: 5 (numeric index computation)
- Tutorial: 4 (examples)

## Scope

### ✅ Completed (0 sorries)
- **Projection API**: Orthogonal projection onto line spanned by unit vector
- **Toggle Operator**: G(c) := id - (if c then 1 else 0) • P with ker/range characterization
- **FredholmAlt**: Lightweight "index-zero spec" (algebra-free characterization)

### 🔧 Nearly Complete (1 sorry)
- **Sherman-Morrison**: Formula proven, one optional norm bound remains

### 📋 Pending Mathlib Update
- **Spectrum**: 3 sorries - awaiting operator algebra instances in mathlib
- **Fredholm**: 5 sorries - numeric index requires finrank/quotient APIs
- **Tutorial**: 4 sorries - pedagogical examples

## Module Status

| Module | Sorries | Status | Notes |
|--------|---------|--------|-------|
| `Projection.lean` | 0 | ✅ Complete | P² = P, P* = P, ‖P‖ = 1 |
| `Toggle.lean` | 0 | ✅ Complete | ker/range, injectivity ↔ surjectivity |
| `FredholmAlt.lean` | 0 | ✅ Complete | Algebra-free index spec |
| `ShermanMorrison.lean` | 1 | 🔧 Nearly complete | Formula proven, norm bound pending |
| `Spectrum.lean` | 3 | 📋 Stub | σ(G₀) = {1}, σ(G₁) = {0,1} documented |
| `Fredholm.lean` | 5 | 📋 Planned | Numeric index computation |
| `Tutorial.lean` | 4 | 📋 Examples | Pedagogical demonstrations |

## Key Results

### Sherman-Morrison Formula
For idempotent P (P² = P):
```lean
theorem sherman_morrison_proj {α : 𝕜} (hα : (1 : 𝕜) + α ≠ 0) :
    ((ContinuousLinearMap.id 𝕜 H) + α • P).comp (
      (ContinuousLinearMap.id 𝕜 H) - (α / (1 + α)) • P) = 
    ContinuousLinearMap.id 𝕜 H
```

### Spectrum Characterization
- σ(G(false)) = {1}
- σ(G(true)) = {0, 1}
- σ_ess(G(c)) = {1} for both cases

### Toggle Properties
- G(false) is bijective
- G(true) has ker = ⟨u⟩ and range = ⟨u⟩^⊥
- Injectivity ↔ Surjectivity ↔ (c = false)

## Build Commands

```bash
# Core modules (0 sorries)
lake build Papers.P1_GBC.RankOneToggle.Projection
lake build Papers.P1_GBC.RankOneToggle.Toggle
lake build Papers.P1_GBC.RankOneToggle.FredholmAlt

# Nearly complete (1 sorry)
lake build Papers.P1_GBC.RankOneToggle.ShermanMorrison

# Pending mathlib (builds with sorries)
lake build Papers.P1_GBC.RankOneToggle.Spectrum
lake build Papers.P1_GBC.RankOneToggle.Fredholm
```

## Mathematical Overview

### Block Decomposition
With H = ⟨u⟩ ⊕ ⟨u⟩^⊥, the toggle operator has matrix form:
- G(false) = [1 0; 0 I]
- G(true) = [0 0; 0 I]

### Resolvent Formula
For λ ∉ {0,1}:
- (λI - G(true))^(-1) = (1/(λ-1))·I - (1/(λ(λ-1)))·P

## Documentation

- **[Current Paper](documentation/paper1-rankone-toggle-current.tex)**: Full mathematical development with Lean status annotations
- **[Work Plan](documentation/paper1-lean-work-plan.tex)**: Implementation roadmap

## Upstream Strategy

Planned mathlib4 contributions:
1. **Projection helpers**: Orthogonal projection onto line API
2. **Sherman-Morrison**: Specialized formula for projections
3. **Toggle lemmas**: Kernel/range characterizations

## Connection to Paper 2

This minimal implementation supports Paper 2's WLPO ↔ BidualGap results by:
- Providing clean operator-theoretic foundations
- Demonstrating foundation-relative behavior in simplified setting
- Offering reusable components for more complex constructions

The rank-one toggle exemplifies how Boolean parameters encode logical choices in operator theory.