# Paper 84 — The Exotic Trace Probe: Transcendence of Weil Classes via Gauss-Manin Analysis

**Paper 84, Constructive Reverse Mathematics Series**

Paul Chun-Kit Lee, New York University, Brooklyn, New York

## Summary

Paper 84 computes the Gauss-Manin connection on the exotic Weil subspace of a genus-4 hyperelliptic family C_t: y^2 = x^9 - tx^5 + x with Q(i)-action. The Q(i)-eigenspace decomposition collapses the 70-dimensional exterior power computation to a scalar ODE via the trace trick. The CAS computation yields:

    tau_+(t) = (-250t^5 + 1890t^3 - 3564t) / (81(t^2 - 4))

The irregular singularity at infinity (polynomial part of degree 3) certifies that the differential Galois group is Gm, meaning the exotic Weil classes are transcendental over Q(t). No finite base change can produce exotic algebraic cycles generically.

This is a negative result: the function-field pipeline provides a finite certificate of generic non-algebraicity, bypassing the Hodge Conjecture.

## Main Results

1. **Exotic Trace (Theorem 1.1):** tau_+(t) = (-250t^5 + 1890t^3 - 3564t) / (81(t^2 - 4)), with tau_-(t) = (10/9) tau_+(t).
2. **Transcendence Certificate (Theorem 1.2):** G_gal = Gm. The flat section involves exp(polynomial), which is transcendental over Q(t).
3. **CRM Descent (Theorem 1.3):** CLASS (Hodge Conjecture) -> BISH (explicit trace computation + Galois analysis).

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
| `galois_is_gm` | (none) |
| `exotic_not_algebraic` | (none) |
| `hodge_conjecture_weil_fourfold` | axiom (declared, unused) |
| `comparison_theorem_de_rham_betti` | axiom (declared, unused) |
| `baire_generic_noether_lefschetz` | axiom (declared, unused) |

The main squeeze theorem depends on **no axioms whatsoever** — not even `propext`.

## File Structure

| File | Lines | Sorry | Content |
|------|-------|-------|---------|
| `TraceData.lean` | 51 | 0 | CAS-emitted coefficients |
| `Paper84_ExoticTrace.lean` | 338 | 0 | Main theorems + squeeze |
| **Total** | **389** | **0** | |

## Dependencies

- Papers 80-83 (method): Function-field pipeline for Legendre family
- Mathlib: Lean 4 mathematics library (tactic infrastructure only)

## CRM Classification

- 10 BISH components (all constructive)
- 3 CLASS components (declared, unused): Hodge Conjecture, comparison theorem, Baire category

Seventh CRMLint Squeeze.

## License

CC BY 4.0
