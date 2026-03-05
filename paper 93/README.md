# Paper 93: The Structural Vanishing Theorem — Why Exotic Weil Classes Are Universally Flat

**Paper 93 of the Constructive Reverse Mathematics Series**

Paul Chun-Kit Lee, New York University, Brooklyn, New York

**DOI:** [10.5281/zenodo.18816989](https://doi.org/10.5281/zenodo.18816989)

## Summary

Papers 84--92 verified computationally that the Gauss-Manin trace tau_+ on
/\^g V_+ vanishes identically for odd hyperelliptic Weil families in genera
g = 2,...,8. This paper explains WHY.

Two independent structural proofs show that tau_+ = 0 is forced by:
(A) Oddness of the defining polynomial: f(-x) = -f(x).
(B) Unit leading/trailing coefficients: f(x) = x^{2g+1} + ... + x.

## Main Results

- **Theorem A (Varchenko Exponent Cancellation):** Root-root exponents cancel
  to zero (discriminant drops out). Root-origin exponent is -1/4. Vieta's
  formula freezes the product of roots to (-1)^g. All BISH (norm_num).
- **Theorem B (Picard-Lefschetz Backbone):** sigma^2 consistency, nilpotent
  variation, unipotent determinant, boundary freezing. All BISH (norm_num/ring/rfl).
- **Theorem C (CRM Decomposition):** 13 BISH + 4 CLASS. All CLASS components
  (Aomoto-Varchenko, Deligne regularity, Picard-Lefschetz, Ehresmann) are
  documentary and unused in the constructive path.

## Lean 4 Bundle

### Build instructions

```bash
cd P93_StructuralVanishing
lake update    # fetch Mathlib
lake build     # ~3112 jobs
```

### Requirements
- Lean 4 toolchain: leanprover/lean4:v4.29.0-rc2
- Mathlib4 v4.29.0-rc2

### File structure (~525 lines, 0 sorry)

| File | Lines | Content |
|------|-------|---------|
| CRMLevel.lean | 47 | CRM hierarchy (reused from Papers 72-92) |
| FractionalLocalSystem.lean | 105 | Local exponents, basis transformation |
| VietaFreeze.lean | 82 | Vieta's formula, intersection numbers |
| Paper93_StructuralVanishing.lean | 237 | Theorems A-C, CRM audit, axiom inventory |

### Axiom inventory

| Theorem | Axioms | Type |
|---------|--------|------|
| varchenko_exponent_cancellation | propext, Classical.choice, Quot.sound + av_* | infrastructure + documentary |
| picard_lefschetz_backbone | propext, Classical.choice, Quot.sound + deligne_*, pl_*, ehresmann_* | infrastructure + documentary |
| crm_bish_count | native_decide | computation |

### CAS scripts

- `solve_structural_vanishing.py`: Exponent arithmetic and Vieta verification (fractions)

## Dependencies

- Papers 84, 85, 89, 92 (computational verification of tau_+ = 0)
- Papers 86, 91 (Kani-Rosen splitting, Markman audit)
- Aomoto-Kita (2011) for hypergeometric function theory
- Varchenko (1989) for period determinant formula
- Deligne (1970) for regular singular connections
