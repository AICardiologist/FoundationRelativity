# Phase 1B: Key Lemmas Implementation Plan

## Overview
Phase 1B focuses on proving the mathematical lemmas that connect Turing machine halting to spectral gaps. This is the most challenging part as it requires careful analysis of how computational steps affect eigenvalues.

## Priority Order (Easiest to Hardest)

### 1. IntervalBookkeeping - Band Order Proofs (Day 1-2)
**File**: `IntervalBookkeeping.lean`
**Sorries**: 7 total

#### 1.1 Band h_order proofs (3 sorries) - EASY
```lean
⟨0, h^2 / 10, sorry⟩           -- Need: 0 ≤ h²/10
⟨h^2 / 4, 5 * h^2, sorry⟩     -- Need: h²/4 ≤ 5h²  
⟨10 * h^2, 100 * h^2, sorry⟩  -- Need: 10h² ≤ 100h²
```
**Strategy**: Simple arithmetic using `ring_nf` and `positivity`

#### 1.2 unperturbed_bands_disjoint (1 sorry) - MEDIUM
- Already partially implemented
- Need case analysis showing bands don't overlap
- Use `linarith` with explicit inequalities

#### 1.3 Harmonic series lemmas (3 sorries) - MEDIUM
- `halting_preserves_gap`: Show perturbation ≤ log(n) when TM halts
- `non_halting_kills_gap`: Show perturbation → ∞ when TM doesn't halt
- `threshold_dichotomy`: Combine above for clear threshold

### 2. Pi1Encoding - Computability Theory (Day 3-4)
**File**: `Pi1Encoding.lean`
**Sorries**: 6 total

#### 2.1 Primitive recursive proofs (2 sorries) - MEDIUM
- `orthogonal_is_primrec`: Checking ∑vᵢ = 0 is primitive recursive
- `rayleigh_is_primrec`: Rayleigh quotient computation is primitive recursive

#### 2.2 Π₁ characterization (3 sorries) - HARD
- Show spectral gap condition is universal quantification
- Connect to primitive recursive predicates
- Prove equivalence with Π₁ formula

#### 2.3 Undecidability (1 sorry) - MEDIUM
- `spectral_question_co_ce`: Use halting problem reduction

### 3. NeckGraph - Spectral Theory (Day 5-6)
**File**: `NeckGraph.lean`
**Sorries**: 2 total

#### 3.1 Define lambda_1 (1 sorry) - HARD
- Implement first non-zero eigenvalue of discrete Laplacian
- Use Rayleigh quotient characterization
- Handle orthogonality to constant functions

#### 3.2 Prove discrete_neck_scaling (1 sorry) - VERY HARD
- Main scaling theorem: (h²/4) ≤ λ₁ ≤ 5h²
- Lower bound: Use test function on neck
- Upper bound: Use Cheeger inequality analog

### 4. TuringEncoding - Main Theorem (Day 7-10)
**File**: `TuringEncoding.lean`
**Sorries**: 4 total

#### 4.1 Define halts_in (1 sorry) - MEDIUM
- Formal definition of TM halting within n steps
- Connect to TM configuration sequences

#### 4.2 Define spectralGap (1 sorry) - HARD
- Extract first non-zero eigenvalue from perturbedLaplacian
- Handle matrix eigenvalue computation

#### 4.3 Prove spectral_gap_jump (1 sorry) - VERY HARD
- **THE MAIN THEOREM**
- Forward: TM halts → gap stays large
- Reverse: TM doesn't halt → gap shrinks
- Use interval bookkeeping lemmas

#### 4.4 Connect to consistency (1 sorry) - MEDIUM
- Use PA consistency ↔ inconsistency searcher doesn't halt

## Key Mathematical Insights Needed

### For Spectral Bounds
1. **Test Functions**: Construct explicit functions that achieve bounds
2. **Perturbation Theory**: Show small edge weight changes → small eigenvalue changes
3. **Accumulation**: Show how non-halting accumulates perturbations

### For Computability
1. **Arithmetization**: Express spectral conditions in first-order arithmetic
2. **Quantifier Structure**: Show universal quantification over vectors
3. **Reduction**: Encode halting problem into spectral gap question

## Tactics Toolbox
- `ring_nf`, `field_simp`: Rational arithmetic
- `positivity`, `linarith`: Inequalities  
- `simp`, `rw`: Definitional equalities
- `use`, `existsi`: Constructing witnesses
- `by_cases`, `cases`: Case analysis

## Success Metrics
- Reduce sorries from 27 to ~10-12
- Have `spectral_gap_jump` theorem verified
- All interval arithmetic working
- Clear path to remaining proofs

## Next Session Goals
1. Complete all IntervalBookkeeping h_order proofs
2. Implement maxPerturbation bounds
3. Start on primitive recursive proofs