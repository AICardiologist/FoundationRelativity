# Paper 85: Universal Trace Vanishing for Exotic Weil Classes

**Paper 85, Constructive Reverse Mathematics Series**

Paul Chun-Kit Lee, New York University, Brooklyn, New York

## Summary

Paper 85 proves that for every genus-4 hyperelliptic family C_t: y^2 = f(x,t) with Q(i)-action (f odd in x), the exotic trace tau_+(t) = tr(nabla|_{V_+}) = 0. The exotic Weil class is universally a global flat section of the Gauss-Manin connection.

The proof is structural: the cup-product pairing on H^1_dR pairs omega_j with omega_{2g-2-j}. For g=4, this pairs even-index differentials with even-index differentials (since 2g-2=6 is even), so the restriction to V_+ is a nondegenerate symplectic form. The Gauss-Manin connection preserves this form, forcing nabla|_{V_+} to be symplectic (hence traceless): tau_+ = 0.

The key parity check: g-1 = 3 is odd, so omega_{g-1} is NOT in V_+ (no self-pairing issue). This is specific to even genus.

## Main Results

1. **Universal Exotic Flatness (Theorem A):** For any genus-g hyperelliptic family with Q(i)-action and g even, tau_+(t) = 0.
2. **Computational Verification (Theorem B):** For y^2 = x^9 + tx^7 + x (no order-8 automorphism), the V_+ block is a dense 4x4 with tau_+ = 0, confirming the structural theorem.
3. **CRM Squeeze (Theorem C):** BISH (symplectic duality) confirms the CLASS prediction (exotic Hodge classes exist and are flat).

## Comparison with Paper 84

| Property | Paper 84 | Paper 85 |
|----------|----------|----------|
| Curve | x^9 - tx^5 + x | x^9 + tx^7 + x (test) |
| Scope | One family | All genus-4 Q(i)-families |
| Proof | 15-step Griffiths + Kovacic | 2-step symplectic duality |
| V_+ block | 4 x (2x2) | 4x4 (dense) |
| tau_+(t) | 0 | 0 |

## Lean 4 Build Instructions

```bash
cd P85_UniversalFlatness
lake build
```

Toolchain: `leanprover/lean4:v4.29.0-rc2`. Requires Mathlib (fetched automatically by `lake build`).

## Axiom Inventory

| Theorem | Axioms |
|---------|--------|
| `universal_flatness_squeeze` | **(none)** |
| `p85_tau_plus_coeff_sum` | (none) |
| `p85_f_odd` | (none) |
| `hodge_decomposition_exotic` | axiom (declared, unused) |
| `cup_product_pairing` | axiom (declared, unused) |

The main squeeze theorem depends on **no axioms whatsoever**.

## File Structure

| File | Content | Tactic |
|------|---------|--------|
| `TraceData.lean` | Trace arithmetic, oddness, no-tau obstruction | `ring`, `decide` |
| `Paper85_UniversalFlatness.lean` | Structural parameters, squeeze theorem, CRM audit | `rfl`, `decide`, `ring` |

## Dependencies

- Paper 84 (computation): One-family Gauss-Manin computation
- Papers 80-83 (method): Function-field pipeline for Legendre family
- Mathlib: Lean 4 mathematics library (tactic infrastructure only)

## CRM Classification

- 8 BISH components (structural parameters, trace arithmetic, oddness, no-tau)
- 2 CLASS components (declared, unused): Hodge decomposition, cup-product pairing

Eighth CRMLint Squeeze.

## License

CC BY 4.0
