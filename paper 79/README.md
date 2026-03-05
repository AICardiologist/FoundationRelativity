# Paper 79: Standard Conjecture D for Abelian Fourfolds of Weil Type Is Constructively Decidable

**Paper 79, Constructive Reverse Mathematics Series**
Paul Chun-Kit Lee, New York University
DOI: [10.5281/zenodo.18843129](https://doi.org/10.5281/zenodo.18843129)

## Summary

Paper 79 applies the CRMLint Squeeze protocol to Grothendieck's Standard
Conjecture D for abelian fourfolds of Weil type.  The Classical Boundary
Node is Lieberman's 1968 proof via the Hard Lefschetz theorem and
Hodge-Riemann bilinear relations (CLASS).  The constructive path bypasses
the abstract Hodge-Riemann machinery entirely: for a generic abelian
fourfold with K = Q(i) acting on H^1(A, Q) ~ Q^8, the exotic Weil
subspace W_K is 2-dimensional with Gram matrix G = 8*I_2, verified
positive definite by Sylvester's criterion via `decide` in Lean 4.

A preliminary sweep over all 16 CM types for Q(zeta_15) confirms that
cyclotomic fields of degree <= 8 cannot host exotic Weil classes
(Hazama-Ribet obstruction), motivating the pivot to the generic setting.

## Main Results

- **Theorem A (Squeeze):** Standard Conjecture D for the exotic Weil classes of a generic abelian fourfold of Weil type descends from CLASS to BISH
- **Theorem B (Definiteness):** The 2x2 Gram matrix G = [[8, 0], [0, 8]] is positive definite by Sylvester's criterion, verified by `decide`
- **Corollary C (Non-degeneracy):** Cup product pairing is non-degenerate on any algebraic subspace of W_K (modular law: Alg^2 = D + (W_K cap Alg^2))
- **CRM Descent:** CLASS (Hodge-Riemann bilinear relations) -> BISH (Sylvester on 2x2 integer matrix)

## Files

| File | Description |
|------|-------------|
| `paper79.tex` | LaTeX source (15 pages) |
| `paper79.pdf` | Compiled paper |
| `P79_ConjD/` | Lean 4 bundle |
| `solve_generic_weil.py` | Python CAS: Gram matrix computation |
| `sweep_cm_types.py` | Python CAS: CM type sweep for Q(zeta_15) |

## Lean 4 Build Instructions

```bash
cd P79_ConjD
lake update       # downloads Mathlib (first time only)
lake build        # builds all files
```

### Requirements

- **Lean toolchain:** `leanprover/lean4:v4.29.0-rc2`
- **Mathlib:** latest (resolved via `lake update`)

### Lean File Structure

| File | Lines | Content |
|------|-------|---------|
| `Paper79_ConjD.lean` | 106 | CRM hierarchy, opaque types, Hodge-Riemann axiom (CLASS), Squeeze theorems, CRM audit |
| `ConjDData.lean` | 43 | CAS-emitted Gram matrix entries, Sylvester criterion by `decide`, leading principal minors |
| **Total** | **149** | **0 sorry** |

Note: `ConjDData.lean` is emitted by `solve_generic_weil.py`.

## Axiom Inventory

| Axiom | CRM Level | Used by Squeeze? |
|-------|-----------|-----------------|
| `hodge_riemann_conjD` | CLASS | No |
| (none) | — | — |

All 5 constructive theorems (`exotic_pairing_is_definite`, `gram_matrix_positive_definite`,
`gram_matrix_is_scalar`, `weil_classes_orthogonal`, `allMinorsPositive`) depend on
**zero axioms** — pure kernel-level `decide` on integer data.

## Dependencies

- Paper 77: CRMLint Squeeze protocol
- Paper 72: DPT biconditional characterization
- Paper 50: DPT framework

## CRM Classification

- **BISH components:** Weil class construction, cup product computation, Sylvester criterion (all `decide`)
- **CLASS components:** Hard Lefschetz theorem, Hodge-Riemann bilinear relations (all unused by squeeze)

## License

CC BY 4.0
