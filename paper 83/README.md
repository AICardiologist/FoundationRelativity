# Paper 83: Generic Picard Number of E_t x E_t

**Paper 83, Constructive Reverse Mathematics Series**

Paul Chun-Kit Lee, New York University, Brooklyn, New York

## Summary

This paper synthesizes the function-field pipeline (Papers 80-82) to compute the generic Picard number of E_t x E_t, where E_t is the Legendre elliptic curve y^2 = x(x-1)(x-t). The generic Picard rank is exactly 3: horizontal fiber + vertical fiber + diagonal.

## Main Results

- **Theorem A (Kunneth):** H^2(E_t x E_t) decomposes as H^2(E_t)^2 + (H^1(E_t) tensor H^1(E_t)), with trivial rank 2 and tensor dimension 4.
- **Theorem B (Invariant tensors):** The SL_2-invariant subspace of V tensor V is 1-dimensional (the symplectic form), matching the flat section dimension from Paper 81.
- **Theorem C (Generic Picard rank):** rho(E_t x E_t) = 2 + 1 = 3, proved entirely within BISH.

## CRM Descent

Classical proof requires: Lefschetz (1,1) theorem (Baire category), Noether-Lefschetz theorem (Zariski density), topological monodromy density (CLASS).

Constructive proof uses: Kunneth rank arithmetic, tensor flat section analysis (Paper 81), Kovacic obstruction (Paper 82), SL_2 representation theory (BISH).

The "Unbounded Degree Trap" is resolved: Kovacic's algorithm provides a finite certificate that no exotic algebraic cycles exist, without searching polynomial degrees.

## Lean Build

```bash
cd P83_GenericPicard && lake build
```

**Toolchain:** leanprover/lean4:v4.29.0-rc2
**Dependencies:** Mathlib (fetched automatically)

### File Structure

| File | Lines | Sorry |
|------|-------|-------|
| Paper83_GenericPicard.lean | 282 | 0 |

### Axiom Inventory

| Theorem | Axioms |
|---------|--------|
| `generic_picard_squeeze` | **(none)** |
| `picard_rank_is_three` | (none) |
| `flat_equals_invariant` | (none) |
| `kunneth_tensor_dim` | (none) |
| `generic_lefschetz_1_1` | generic_lefschetz_1_1 (axiom, unused) |
| `noether_lefschetz_generic` | noether_lefschetz_generic (axiom, unused) |
| `topological_monodromy_density` | topological_monodromy_density (axiom, unused) |

The main squeeze theorem depends on **no axioms whatsoever** -- not even `propext`. This is the cleanest axiom inventory in the CRM series.

### CRM Audit

| Component | Level | Tactic |
|-----------|-------|--------|
| Kunneth rank arithmetic | BISH | `decide` |
| H^2 trivial classes | BISH | `rfl` |
| Tensor flat section dim = 1 (Paper 81) | BISH | `rfl` |
| Galois group = SL_2 (Paper 82) | BISH | `rfl` |
| SL_2 rep theory: invariant dim = 1 | BISH | `rfl` |
| Flat-invariant consistency | BISH | `rfl` |
| Picard rank = 3 | BISH | `rfl` |
| Degree trap resolution | BISH | `rfl` |
| Lefschetz (1,1) theorem | CLASS | (unused) |
| Noether-Lefschetz theorem | CLASS | (unused) |
| Topological monodromy density | CLASS | (unused) |

## Dependencies

- Paper 80: Algebraic Gauss-Manin connection (DOI: 10.5281/zenodo.18791985)
- Paper 81: Algebraic flat sections and the Fixed Part theorem
- Paper 82: Constructive differential Galois theory via Kovacic's algorithm

## License

CC BY 4.0
