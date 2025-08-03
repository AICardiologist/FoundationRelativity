# Proof Architecture: Discrete CPW Model

## Overview
This document maps out the complete proof architecture for Paper 4's discrete CPW model, showing how all components connect to establish the main undecidability result.

## Core Components

### 1. Infrastructure Layer
- **NeckGraph.lean**: Discrete neck torus structure (n×n grid)
- **TuringEncoding.lean**: TM computation → edge weight perturbations

### 2. Mathematical Analysis Layer
- **IntervalBookkeeping.lean**: Spectral band separation
- **SpectralTheory.lean**: Variational characterization of eigenvalues
- **PerturbationTheory.lean**: How perturbations affect spectrum

### 3. Computability Layer
- **Pi1Encoding.lean**: Π₁ complexity of spectral conditions

### 4. Main Results Layer
- **MainTheorem.lean**: The equivalence theorem
- **ConPA_bridge.lean**: Connection to consistency

## The Main Proof Flow

```
Turing Machine M
    ↓ (encode)
Edge perturbations εᵢ = 1/i at step i
    ↓ (accumulate)
Total perturbation = Σ εᵢ
    ├─→ If M halts at n: Σ ≤ Hₙ ≈ log(n) [bounded]
    └─→ If M doesn't halt: Σ = H_N → ∞ [unbounded]
         ↓ (affect spectrum)
Spectral gap λ₁
    ├─→ Bounded perturbation: λ₁ ≥ h²/8 [gap preserved]
    └─→ Unbounded perturbation: λ₁ < h²/8 [gap destroyed]
         ↓ (equivalence)
Main Theorem: M halts ↔ (∃ε>0, ∀N, λ₁(N) ≥ ε)
```

## Key Lemmas and Their Roles

### Phase 1 Lemmas (Infrastructure)
1. **unperturbed_bands_disjoint** ✅
   - Shows initial spectrum has clear band structure
   - Enables perturbation analysis

2. **discrete_neck_scaling** ✅
   - Proves λ₁ ≈ h² for unperturbed system
   - Sets the scale for threshold h²/8

### Phase 2 Lemmas (Perturbation Analysis)
3. **halting_preserves_gap** 📝
   - When M halts early, perturbation < threshold
   - Gap stays above h²/8

4. **non_halting_kills_gap** 📝
   - When M runs forever, perturbation → ∞
   - Gap falls below h²/8

5. **harmonic_growth** 🔧
   - Proves Hₙ ≈ log(n) growth
   - Key to perturbation bounds

### Phase 3 Lemmas (Main Connection)
6. **spectral_gap_jump_forward** 🔧
   - Halting → bounded perturbation → large gap
   - Uses lemmas 3 and 5

7. **spectral_gap_jump_reverse** 🔧
   - Large gap → bounded perturbation → halting
   - Contrapositive using lemma 4

8. **large_gap_bounds_perturbations** 🔧
   - Key technical lemma for reverse direction
   - If gap always ≥ ε, perturbations must be bounded

## Technical Challenges and Solutions

### Challenge 1: Eigenvalue Computation
- **Problem**: Can't compute eigenvalues explicitly
- **Solution**: Variational characterization via Rayleigh quotient

### Challenge 2: Perturbation Bounds
- **Problem**: How do edge perturbations quantitatively affect λ₁?
- **Solution**: First-order analysis + sensitivity bounds
- **Open**: Awaiting consultant input on best approach

### Challenge 3: Π₁ Complexity
- **Problem**: Show spectral condition is primitive recursive
- **Solution**: Express as ∀v (rational arithmetic formula)
- **Status**: Structure clear, details axiomatized

## Remaining Work

### High Priority (Core Logic)
1. Prove **large_gap_bounds_perturbations**
2. Complete **spectral_gap_jump_reverse**
3. Connect to halting problem undecidability

### Medium Priority (Technical Details)
4. Harmonic series bounds (replace axioms)
5. Perturbation sensitivity analysis
6. Primitive recursive formalization

### Low Priority (Nice to Have)
7. Explicit constants (currently using h²/8 threshold)
8. Optimal bounds on n < 100 condition
9. Computational estimates

## Success Metrics
- [ ] Main theorem statement compiles
- [ ] Forward direction complete (halting → gap)
- [ ] Reverse direction complete (gap → halting)
- [ ] Connection to PA consistency
- [ ] Undecidability corollary

## Current Sorry Count
- **Total**: 19 (8 axiomatization + 11 implementation)
- **Critical path**: ~6-8 sorries for main theorem
- **Target**: <10 sorries for complete discrete model

## Legend
- ✅ Complete
- 📝 Axiomatized with explanation
- 🔧 In progress
- ❌ Not started