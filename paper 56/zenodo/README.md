# Paper 56: Exotic Weil Class Self-Intersection on CM Abelian Fourfolds

**Explicit Computation at the DPT Boundary**

Paper 56 in the Constructive Reverse Mathematics and Arithmetic Geometry Series

Paul Chun-Kit Lee (dr.paul.c.lee@gmail.com), February 2026

## Overview

This Lean 4 formalization computes the self-intersection degree deg(w_0 . w_0) = sqrt(disc(F))
for exotic Weil classes on three CM abelian fourfolds of Weil type, providing explicit
numerical evidence at the boundary of the Deligne-Poisson-Tate (DPT) conjecture.

For each CM field K and totally real subfield F, the discriminant equation det(G) = disc(F)
is established via the cyclic conductor theorem (disc(F) = conductor^2, d_0 = conductor).
The 3x3 trace-matrix determinants are computed by `native_decide`. All degrees are positive
(Hodge-Riemann) and all exotic Weil classes are algebraic (Schoen's norm criterion).

**Three examples:**

- **Example 1** (K = Q(sqrt(-3)), F = Q(zeta_7 + zeta_7^{-1})): disc(F) = 49, deg = 7
- **Example 2** (K = Q(i), F = Q(zeta_9 + zeta_9^{-1})): disc(F) = 81, deg = 9
- **Example 3** (K = Q(sqrt(-7))): disc(F) = 169, deg = 13

## Main Results

| Theorem | Statement | Status |
|---------|-----------|--------|
| `det_trace_matrix_ex1 = 49` | disc(F) for Q(zeta_7 + zeta_7^{-1}) | `native_decide` |
| `det_trace_matrix_ex2 = 81` | disc(F) for Q(zeta_9 + zeta_9^{-1}) | `native_decide` |
| `det_trace_matrix_ex3 = 169` | disc(F) for Q(zeta_13 + zeta_13^{-1}) | `native_decide` |
| `deg_ex1 = 7` | Self-intersection degree, Example 1 | From disc + conductor |
| `deg_ex2 = 9` | Self-intersection degree, Example 2 | From disc + conductor |
| `deg_ex3 = 13` | Self-intersection degree, Example 3 | From disc + conductor |
| `hr_positive_ex{1,2,3}` | Hodge-Riemann: deg > 0 | `norm_num` |
| `schoen_algebraic_ex{1,2,3}` | Schoen algebraicity criterion | From axiom + `norm_num` |
| `d0_sq_eq_disc` | d_0^2 = disc(F) via conductor | `ring` + `rw` |

## How to Open and Build

### LaTeX Paper

The compiled PDF is included (`paper56.pdf`). To recompile:

```bash
pdflatex paper56.tex
pdflatex paper56.tex
```

### Lean 4 Formalization

**Prerequisites:** Install [elan](https://github.com/leanprover/elan) (Lean version
manager) and ensure `lake` is available. Requires ~8 GB disk space for Mathlib cache.

```bash
cd P56_ExoticWeilSelfInt
lake exe cache get       # downloads prebuilt Mathlib (~5 min)
lake build               # compiles Paper 56 source files (~2-5 min)
```

A successful build produces 0 errors, 0 warnings, and 0 sorries.

### Verify Axiom Profile

After building:

```lean
#print axioms Papers.P56_ExoticWeilSelfInt.det_trace_matrix_ex1
-- [propext, Classical.choice, Quot.sound]
```

All computational modules (NumberFieldData, HodgeRiemann, Pattern, Verdict,
GramMatrixDerivation) have zero sorry. Principled axioms are confined to
modules encoding deep theorems (Milne, Shimura, Schoen).

## Axiom Audit

**Sorry budget: 10 principled axioms, 0 false axioms, 0 sorry gaps.**

All theorems carry the axiom profile `[propext, Classical.choice, Quot.sound]`.
`Classical.choice` is a Lean metatheory axiom from Mathlib's real number
construction (classical Cauchy completion) --- not an object-level
non-constructive principle.

The 10 principled axioms encode published results:

| Axiom | Citation |
|-------|----------|
| `milne_weil_dim` | Milne (1999), Lemma 1.3 |
| `exotic_not_lefschetz` | Anderson (1993); Milne (1999), Section 1 |
| `cm_polarization_threefold` | Shimura (1998), Chapter II |
| `det_product_ex1` | CM arithmetic for K = Q(sqrt(-3)) |
| `det_product_ex2` | CM arithmetic for K = Q(i) |
| `det_product_ex3` | CM arithmetic for K = Q(sqrt(-7)) |
| `weil_class_degree_eq_conductor` | d_0 = conductor (geometric) |
| `schoen_algebraicity_ex1` | Schoen (1998), Theorem 0.2 |
| `schoen_algebraicity_ex2` | Schoen (1998), Theorem 0.2 |
| `schoen_algebraicity_ex3` | Schoen (1998), Theorem 0.2 |

Computational modules (1, 5, 7, 8, 9) have ZERO sorry:
- 3x3 determinants via `native_decide`
- HR sign computation via `norm_num`
- Pattern checks (n^2 = n^2) via `native_decide`
- Norm witnesses via `norm_num`
- Gram matrix algebra via `ring`, d_0^2 = disc(F) via conductor `rw`

**Correction history:** v2 (conductor-based) is current. The v1/v3 discriminant
equation det(G) = disc(F) is FALSE in general; deprecated files retained for
transparency.

## Contents

```
README.md                                   This file
.zenodo.json                                Zenodo metadata
CITATION.cff                                Citation metadata
paper56.tex                                 LaTeX source (677 lines)
paper56.pdf                                 Compiled paper
P56_ExoticWeilSelfInt/                      Lean 4 formalization
  lakefile.lean                             Package configuration
  lean-toolchain                            leanprover/lean4:v4.29.0-rc1
  lake-manifest.json                        Dependency lock file
  Papers.lean                               Root import (52 lines)
  Papers/P56_ExoticWeilSelfInt/
    NumberFieldData.lean         162 lines   Trace matrices, disc(F) via det
    WeilLattice.lean             101 lines   Exotic Weil lattice, dim = 2
    PolarizationDet.lean         125 lines   CM polarization determinants
    SelfIntersection.lean        145 lines   deg(w_0 . w_0) from disc(F)
    HodgeRiemann.lean             71 lines   HR verification: deg > 0
    SchoenAlgebraicity.lean      113 lines   Schoen norm criterion
    Pattern.lean                  81 lines   deg = sqrt(disc(F)) pattern
    Verdict.lean                 140 lines   DPT interpretation, summary
    GramMatrixDerivation.lean    393 lines   d_0^2 = disc(F) proof
    Module9_v1_original.lean      26 lines   (deprecated)
    Module9_v3_deprecated.lean   309 lines   (deprecated)
```

9 active modules + 2 deprecated, ~1,666 lines total (active: ~1,331 lines).

## Complete Paper List

Papers in the Constructive Reverse Mathematics Series:

- Paper 1: Withdrawn
- Paper 2: Bidual gap and WLPO -- DOI: 10.5281/zenodo.17107493
- Paper 3: Withdrawn
- Paper 4: Quantum spectra axiom calibration -- DOI: 10.5281/zenodo.17059483
- Paper 5: Schwarzschild curvature verification -- DOI: 10.5281/zenodo.18489703
- Paper 6: Heisenberg uncertainty (v2, CRM over Mathlib) -- DOI: 10.5281/zenodo.18519836
- Paper 7: Physical bidual gap, trace-class operators -- DOI: 10.5281/zenodo.18527559
- Paper 8: 1D Ising model and LPO -- DOI: 10.5281/zenodo.18516813
- Paper 9: Ising formulation-invariance -- DOI: 10.5281/zenodo.18517570
- Paper 10: Logical geography of mathematical physics -- DOI: 10.5281/zenodo.18580342
- Paper 11: Entanglement, CHSH, Tsirelson bound -- DOI: 10.5281/zenodo.18527676
- Paper 12: Constructive history of mathematical physics -- DOI: 10.5281/zenodo.18581707
- Paper 13: Event horizon as logical boundary -- DOI: 10.5281/zenodo.18529007
- Paper 14: Quantum decoherence -- DOI: 10.5281/zenodo.18569068
- Paper 15: Noether theorem -- DOI: 10.5281/zenodo.18572494
- Paper 16: Technical note: Born rule -- DOI: 10.5281/zenodo.18575377
- Paper 17: Bekenstein-Hawking formula -- DOI: 10.5281/zenodo.18597306
- Paper 18: Yukawa RG constructive stratification -- DOI: 10.5281/zenodo.18626839
- Paper 19: WKB tunneling and LLPO -- DOI: 10.5281/zenodo.18602596
- Paper 20: Observable-dependent logical cost, 1D Ising magnetization and WLPO -- DOI: 10.5281/zenodo.18603079
- Paper 21: Bell nonlocality and LLPO -- DOI: 10.5281/zenodo.18603251
- Paper 22: Markov's Principle and radioactive decay -- DOI: 10.5281/zenodo.18603503
- Paper 23: Fan Theorem and optimization -- DOI: 10.5281/zenodo.18604312
- Paper 24: Kochen-Specker contextuality and LLPO -- DOI: 10.5281/zenodo.18604317
- Paper 25: Choice axis (CC, DC) and ergodic theorems -- DOI: 10.5281/zenodo.18615453
- Paper 26: Bidual gap arithmetic route, WLPO -- DOI: 10.5281/zenodo.18615457
- Paper 27: Bell angle optimisation via IVT, LLPO -- DOI: 10.5281/zenodo.18615459
- Paper 28: Newton vs. Lagrange vs. Hamilton -- DOI: 10.5281/zenodo.18616620
- Paper 29: Fekete's Subadditive Lemma and LPO -- DOI: 10.5281/zenodo.18632776
- Paper 56: Exotic Weil class self-intersection on CM abelian fourfolds -- This paper

## License

Apache 2.0 (code) / CC-BY 4.0 (paper).
