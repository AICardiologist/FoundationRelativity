# Paper 51: The Constructive Archimedean Rescue in Birch--Swinnerton-Dyer

**Series:** Constructive Reverse Mathematics and Physics
**Author:** Paul Chun-Kit Lee
**DOI:** [10.5281/zenodo.18732168](https://doi.org/10.5281/zenodo.18732168)
**Date:** February 2026, v2.0

---

## Abstract

We prove that the positive-definite Archimedean metric is the unique topological modality converting the rank-1 BSD generator search from MP (unbounded Diophantine search) to BISH (bounded exhaustive search). Given quarantined analytic axioms (Gross-Zagier, Kolyvagin, Silverman), the search for a generator of E(Q) lies in an explicit Finset of size O(B^2), where B = ceil(exp(2*h_hat(y_K) + 2*mu(E))).

The p-adic analogue fails: without positive-definiteness (u = 4), the canonical height can vanish on non-torsion points, collapsing the search bound.

Formalized in Lean 4 + Mathlib with zero `sorry`s and zero custom axiom declarations.

---

## Repository Contents

```
P51_BSD_Archimedean_Rescue/
|
|-- README.md                          (this file)
|-- paper51_archimedean_bsd.pdf        (compiled paper)
|
|-- latex/
|   +-- paper51_archimedean_bsd.tex    (LaTeX source)
|
+-- lean/
    |-- lakefile.lean                  (Lake build file, Mathlib dependency)
    |-- lean-toolchain                 (leanprover/lean4:v4.29.0-rc1)
    |-- Papers.lean                    (root import)
    +-- Papers/P51_BSD/
        |-- Defs.lean                  (ECData, RatPoint, naiveHeight)
        |-- Principles.lean            (MarkovPrinciple, BISHDecidable)
        |-- HeightBounds.lean          (Silverman bound, BISH core)
        |-- SearchSpace.lean           (searchBound, searchGrid, grid membership)
        |-- BSDAxioms.lean             (Gross-Zagier, Kolyvagin as Prop-valued defs)
        |-- ConstructiveBSD.lean       (main theorems, p-adic failure)
        +-- Main.lean                  (root module, axiom audit)
```

## Building the Lean Formalization

```bash
cd lean/
lake update
lake build
```

Requires: Lean 4 (v4.29.0-rc1) and internet access for Mathlib download.
First build takes ~30-60 minutes (Mathlib compilation).

## Key Results

| Theorem | Statement | File |
|---------|-----------|------|
| `naiveHeight_bounded_of_canonical` | h_hat(P) <= C ==> h(P) <= 2C + 2mu | HeightBounds.lean |
| `bsd_rank_one_finite_search` | Main: generator search in explicit Finset | ConstructiveBSD.lean |
| `bsd_stratification` | Existential form with positive bound | ConstructiveBSD.lean |
| `padic_failure_vacuous` | p-adic collapse: C=0 gives h(P) <= 2mu | ConstructiveBSD.lean |
| `archimedean_rescue_gap` | 2mu < 2*h_hat(y_K) + 2mu | ConstructiveBSD.lean |
| `bish_decidable_of_bound` | Axiom-free BISH decidability | Principles.lean |

## Axiom Audit

All theorems depend only on `[propext, Classical.choice, Quot.sound]` (standard Mathlib infrastructure for R). `bish_decidable_of_bound`, `height_bound_monotone`, and `height_bound_nonneg` depend on no axioms at all.

Zero `sorry`s. Zero custom `axiom` declarations. All analytic axioms (Gross-Zagier, Silverman bound, positive-definiteness) enter as Prop-valued structure fields, not Lean axiom commands.

## Series Context

- **Paper 23:** Fan Theorem <-> CompactOptimization
- **Paper 28:** Newton vs. Lagrange vs. Hamilton stratification
- **Paper 51:** Archimedean metric as the logical modality for BSD

## License

Creative Commons Attribution 4.0 International (CC BY 4.0)
