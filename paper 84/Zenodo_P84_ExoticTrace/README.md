# Paper 84: Exotic Weil Classes as Flat Sections

**Paper 84, Constructive Reverse Mathematics Series**

Paul Chun-Kit Lee, New York University, Brooklyn, New York

## Summary

Paper 84 computes the Gauss-Manin connection on the de Rham cohomology of the genus-4 hyperelliptic family C_t: y^2 = x^9 - tx^5 + x with Q(i)-action, using Griffiths pole-order reduction with the correct coboundary subtraction A_k = B_k - h_k'.

An order-8 automorphism tau(x,y) = (ix, e^{pi*i/4} y) decomposes the 8x8 connection matrix into four 2x2 blocks. Each block has G_gal(W_k) = SL_2 (nilpotent residues with non-proportional kernels). Since det(SL_2) = 1, the induced action on the exotic line bundle wedge^4(V_+) is trivial: G_gal(wedge^4 V_+) = {1}. The exotic Weil class is a global flat section.

This is a positive result: the BISH-computable monodromy certifies that the exotic class is monodromy-invariant. By Deligne's Theorem of the Fixed Part, it is an absolute Hodge class on every fiber.

## Main Results

1. **Block Decomposition (Theorem A):** M_k = (2k+1)/(4(t^2-4)) * [[-t/2, -1], [1, t/2]] for k = 0,1,2,3. All entries regular. tr(M) = 0, tau_+ = tau_- = 0.
2. **SL_2 Monodromy (Theorem B):** Nilpotent residues at t = +/-2 with ker(R_+) = <(-1,1)>, ker(R_-) = <(1,1)>. Non-proportional => irreducible => G_gal(W_k) = SL_2.
3. **Global Flatness (Theorem C):** det(SL_2) = 1 => G_gal(wedge^4 V_+) = {1} => exotic Weil class is a global flat section => absolute Hodge by Deligne's Theorem of the Fixed Part.

## Erratum (v1 -> v2 -> v3)

**v1 -> v2 (computational):** v1 omitted the coboundary correction h_k' in the Griffiths reduction, producing an incorrect trace with polynomial part of degree 3. v1 also misidentified the block-producing automorphism as sigma^2 instead of the correct order-8 automorphism tau. v2 corrects both errors: G_gal(W_k) = SL_2 (not Gm).

**v2 -> v3 (interpretive):** v2 correctly computed G_gal(W_k) = SL_2 but incorrectly claimed G_gal(wedge^4 V_+) = SL_2 x SL_2 (negative result). Since det(SL_2) = 1, the correct answer is G_gal(wedge^4 V_+) = {1} (positive result: exotic class is flat). v3 corrects the geometric interpretation; the Lean proofs are unchanged.

## Lean 4 Build Instructions

```bash
cd P84_ExoticTrace
lake build
```

Toolchain: `leanprover/lean4:v4.29.0-rc2`. Requires Mathlib (fetched automatically by `lake build`).

## Axiom Inventory

| Theorem | Axioms |
|---------|--------|
| `exotic_trace_squeeze` | **(none)** |
| `griffiths_k0` through `griffiths_k7` | (none) |
| `kernel_det_nonzero` | (none) |
| `hodge_decomposition_exotic` | axiom (declared, unused) |
| `kolchin_kovacic_SL2` | axiom (declared, unused) |

The main squeeze theorem depends on **no axioms whatsoever**.

## File Structure

| File | Content | Tactic |
|------|---------|--------|
| `TraceData.lean` | 8 Griffiths identities, traces, residues, kernels | `ring`, `decide` |
| `Paper84_ExoticTrace.lean` | Squeeze theorem, CRM audit, axiom inventory | `rfl`, `decide` |

## Dependencies

- Papers 80-83 (method): Function-field pipeline for Legendre family
- Mathlib: Lean 4 mathematics library (tactic infrastructure only)

## CRM Classification

- 15 BISH components (8 Griffiths identities, 3 traces, 2 residues, Fuchs relation, kernel non-proportionality)
- 2 CLASS components (declared, unused): Hodge decomposition, Kolchin-Kovacic classification

Seventh CRMLint Squeeze.

## License

CC BY 4.0
