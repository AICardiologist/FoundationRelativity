# Dual Isometries Implementation

## Purpose
Discharge the two placeholder axioms in the WLPO ↔ BidualGapStrong theorem by proving:
1. `(c₀ →L[ℝ] ℝ) ≃ₗᵢ ℓ¹` 
2. `(ℓ¹ →L[ℝ] ℝ) ≃ₗᵢ ℓ^∞`

These isometries allow us to prove:
- `WLPO → DualIsBanach c₀`
- `WLPO → DualIsBanach (c₀ →L[ℝ] ℝ)`

## Key Innovation: The σ_ε Trick

Instead of using the sign function (which requires decidability), we use the constructive approximate sign:
```
σ_ε(t) = t / (|t| + ε) ∈ [-1, 1]
```

This allows us to prove norm equalities without case-splitting on signs, keeping everything constructive.

## Files

- `SigmaEpsilon.lean`: The σ_ε function and its properties
- `DualIsometries.lean`: Main isometry proofs (skeleton with 27 sorries)
- `DirectDual.lean`: Existing signVector machinery we'll reuse
- `IMPLEMENTATION_PLAN.md`: Detailed step-by-step plan from math team guidance

## Mathematical Insights

### Where WLPO is Used
- **NOT** for the isometries themselves (these are constructive)
- **NOT** for completeness proofs (uniform Cauchy argument)
- **ONLY** for locating suprema in ℓ^∞ via binary search

### Proof Strategy
1. **Upper bounds**: Direct from triangle/Hölder inequalities
2. **Lower bounds**: Test on vectors with coordinates σ_ε(aᵢ) on finite support
3. **Norm equality**: Combine upper and lower bounds with ε-argument

### Key Lemma Pattern
For f : c₀ →L[ℝ] ℝ with coefficients aₙ = f(eₙ):
- Upper: |f(x)| ≤ ∑|aₙ| for ‖x‖ ≤ 1 
- Lower: Test on x_F^ε = ∑_{n∈F} σ_ε(aₙ)·eₙ gives f(x_F^ε) ≥ ∑_{n∈F}|aₙ| - ε|F|
- Hence ‖f‖ = ∑|aₙ| exactly

## Current Status
- [x] Created σ_ε function with key properties
- [x] Updated DualIsBanach structure per professor's guidance
- [ ] Implement toCoeffs with summability proof
- [ ] Prove norm equality using σ_ε
- [ ] Build inverse ofCoeffs
- [ ] Bundle as LinearIsometryEquiv
- [ ] Repeat for (ℓ¹ →L ℝ) ≃ₗᵢ ℓ^∞
- [ ] Add transport lemma
- [ ] Implement WLPO → locatedness
- [ ] Final discharge theorems

## Testing
Run after each phase:
```bash
lake env lean Papers/P2_BidualGap/HB/DualIsometries.lean
```

Check axiom profile:
```lean
#print axioms dual_is_banach_c0_from_WLPO
```

## Success Criteria
- All 27 sorries resolved
- No project-level axioms in final theorem
- Regression tests pass
- Can claim "axiom-free" main theorem in paper