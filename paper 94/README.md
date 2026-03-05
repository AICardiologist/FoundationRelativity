# Paper 94: The Griffiths Group of the Mirror Quintic

**Paper 94 of the Constructive Reverse Mathematics Series**

Paul Chun-Kit Lee, New York University, Brooklyn, New York

**DOI:** [10.5281/zenodo.18820969](https://doi.org/10.5281/zenodo.18820969)

## Summary

This paper applies the CRMLint Squeeze protocol to the Griffiths group of
a Calabi-Yau 3-fold, using the mirror quintic as the test case. Walcher (2007)
computed the inhomogeneous Picard-Fuchs equation for the real Lagrangian
RP^3 in X_5: the domainwall tension T(z) satisfies L * T = (15/8)*sqrt(z), where
L is the 4th-order PF operator. The source term (15/8)*sqrt(z) is algebraic,
determined by the topology of the real cycle. The expansion T = sqrt(z) * sum b_n z^n
has b_0 = 30 (Walcher's disk count) and b_n satisfying a rational recurrence.

## Main Results

- **Theorem A (PF Algebra):** The 4th-order Picard-Fuchs operator for the
  mirror quintic, its Weyl algebra expansion, and its singular locus are
  strictly BISH (13 sub-results, all ring/norm_num/rfl).
- **Theorem B (Walcher Equation):** Source term (15/8)*sqrt(z) verified algebraically.
  Leading coefficient b_0 = 30, recurrence verified at 5 indices by norm_num.
- **Theorem C (Normal Function Squeeze):** The algebraic shadow (source term,
  recurrence, coefficients) is BISH; Abel-Jacobi integration, convergence,
  and Baire category are irreducibly CLASS.
- **Theorem D (Voisin Decomposition):** 11 BISH + 3 CLASS components. All
  CLASS unused in the constructive path.

## Lean 4 Bundle

### Build instructions

```bash
cd P94_NormalFunctionSqueeze
lake update    # fetch Mathlib
lake build     # ~3112 jobs
```

### Requirements
- Lean 4 toolchain: leanprover/lean4:v4.29.0-rc2
- Mathlib4 v4.29.0-rc2

### File structure (~500 lines, 0 sorry)

| File | Lines | Content |
|------|-------|---------|
| CRMLevel.lean | 47 | CRM hierarchy (reused from Papers 72-93) |
| MirrorData.lean | 149 | PF operator, Weyl algebra expansion, singular locus |
| WalcherData.lean | 103 | Source coefficient, b_n values, recurrence verification |
| Paper94_NormalFunctionSqueeze.lean | 267 | Theorems A-D, CRM audit, axiom inventory |

### Axiom inventory

| Theorem | Axioms | Type |
|---------|--------|------|
| pf_algebra_squeeze | propext, Classical.choice, Quot.sound | infrastructure |
| walcher_equation_squeeze | propext, Classical.choice, Quot.sound | infrastructure |
| normal_function_squeeze | + abel_jacobi_*, baire_* | documentary |

### CAS scripts

- `solve_mirror_quintic.py`: Picard-Fuchs operator computation (SymPy)
- `solve_walcher.py`: Walcher expansion coefficients and recurrence (fractions)

## Dependencies

- Paper 93 (Structural Vanishing Theorem) for the abelian campaign capstone
- Papers 80 (Gauss-Manin), 87 (Hodge cost) for CRM methodology
- Papers 84-89 (Weil locus campaign) for Squeeze protocol
- Candelas-de la Ossa-Green-Parkes (1991) for PF operator
- Walcher (2007), Morrison-Walcher (2009) for inhomogeneous PF equation
- Voisin (2000, 2003) for Griffiths group infinite generation
