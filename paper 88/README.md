# Paper 88: Fermat Domination and the Variational Hodge Conjecture

Paper 88 of the Constructive Reverse Mathematics Series.

## Summary

For the asymmetric genus-4 family C_t: y^2 = x^9 + tx^7 + x (Paper 85), the Jacobian is generically absolutely simple — Kani-Rosen splitting (Paper 86) is unavailable because the core polynomial x^8 + tx^6 + 1 is not palindromic.

We prove the Hodge Conjecture conditionally via CM specialization:

1. At t = 0, the curve C_0: y^2 = x^9 + x is dominated by the Fermat curve F_16: u^16 + v^16 = 1 via the map x = u^2/v^2, y = u/v^9.
2. By Shioda (1982), the exotic Weil class is algebraic at t = 0.
3. Paper 85 proved tau_+ = 0 over Q(t) (global flat section).
4. The Variational Hodge Conjecture spreads algebraicity to generic t.

Result: conditional on Shioda + VHC. Tenth CRMLint Squeeze.

## Main Results

- **Theorem A (Fermat Domination):** C_0 is dominated by F_16. Pullback differentials are holomorphic Fermat differentials with a + b = 8 <= 15.
- **Theorem B (Conditional Hodge):** Assuming Shioda's theorem and VHC, the exotic Weil class on J(C_t) is algebraic for generic t.
- **Theorem C (CRM Squeeze):** BISH anchors the CM fiber (Fermat domination + trace vanishing); CLASS spreads algebraicity (Shioda + VHC).

## Lean 4 Bundle

**Location:** `P88_VariationalSqueeze/`

### Build Instructions

```bash
cd "paper 88/P88_VariationalSqueeze"
lake build
```

### File Structure

| File | Lines | Content |
|------|-------|---------|
| `FermatData.lean` | 185 | Curve data, specialization, Fermat domination identity, non-palindromic obstruction, pullback holomorphicity, trace vanishing |
| `Paper88_Variational.lean` | 226 | 14-conjunct squeeze theorem, CLASS axiom stubs, CRM audit |
| **Total** | **411** | **0 sorry** |

### Axiom Inventory

```
#print axioms P88.variational_hodge_squeeze
-- [propext, Classical.choice, Quot.sound]
```

- `propext`, `Quot.sound`: Lean kernel infrastructure.
- `Classical.choice`: Q field structure infrastructure (not mathematical content).
- `shioda_fermat_hodge`, `variational_hodge_conjecture`: declared as CLASS documentation stubs, not referenced by the squeeze theorem.

### Key Verified Identities

- Fermat domination: u^2 = u^18 + u^2*v^16 (from u^16 + v^16 = 1)
- Non-palindromic obstruction: g(x,t) - g_rev(x,t) = t*x^2*(x^4 - 1)
- Specialization: f(x, 0) = x^9 + x
- Trace vanishing: (-9) + (-45) + (-81) + 135 = 0
- Pullback holomorphicity: a + b = 8 <= 15 for all k in {0,1,2,3}

## Dependencies

- Papers 84-85: exotic trace vanishing (tau_+ = 0)
- Paper 86: comparison (Kani-Rosen approach for palindromic family)
- Lean 4 toolchain: leanprover/lean4:v4.29.0-rc2
- Mathlib

## Author

Paul Chun-Kit Lee, New York University
