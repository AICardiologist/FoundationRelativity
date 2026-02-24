# Paper 17 — Axiom Calibration of Black Hole Entropy

**Author:** Paul Chun-Kit Lee (New York University)
**Date:** February 2026
**Series:** Constructive Reverse Mathematics for Mathematical Physics

## Abstract

The Bekenstein–Hawking entropy formula S = A/4, derived from loop quantum gravity spin network state counting, splits across the constructive hierarchy. The finite entropy computation is provable in Bishop's constructive mathematics (BISH). The assertion that the entropy density S(A)/A converges to a completed real number as A → ∞ is equivalent to the Limited Principle of Omniscience (LPO) via Bounded Monotone Convergence (BMC). The subleading logarithmic correction coefficient −3/2 is verified by finite algebra (BISH). This is the fifth independent physics domain exhibiting the BISH/LPO boundary at bounded monotone convergence.

## Contents

```
paper17_writeup.tex    LaTeX source (16 pages)
paper17_writeup.pdf    Compiled PDF
P17_BHEntropy/         Lean 4 formalization (20 files, 1,804 lines)
```

## Lean Formalization

### Build Instructions

```bash
cd P17_BHEntropy
lake exe cache get    # download Mathlib cache (~5 min)
lake build            # build project (0 errors, 0 sorry)
```

### Toolchain

- **Lean:** `leanprover/lean4:v4.28.0-rc1`
- **Mathlib:** pinned via `lakefile.lean`

### File Manifest

| Module | Lines | Content |
|--------|------:|---------|
| `Basic.lean` | 130 | LPO, BMC, HalfInt, casimir, area eigenvalue, SpinConfig |
| `CasimirProps.lean` | 113 | Casimir/area eigenvalue monotonicity and positivity |
| `FiniteCount.lean` | 65 | Admissible set finiteness (axiomatized) |
| `Entropy.lean` | 74 | count_configs, entropy, entropy_density |
| `PartA_Main.lean` | 47 | Part A assembly + axiom audit |
| `PartB_Defs.lean` | 78 | runMax, areaSeq, S_alpha, EntropyConvergence |
| `PartB_RunMax.lean` | 112 | runMax monotonicity, witness extraction |
| `PartB_AreaSeq.lean` | 76 | Area sequence properties |
| `PartB_GapLemma.lean` | 51 | Entropy density gap (axiomatized) |
| `PartB_EncodedSeq.lean` | 60 | Encoded sequence limit behavior |
| `PartB_Forward.lean` | 70 | LPO → convergence via BMC |
| `PartB_Backward.lean` | 142 | Convergence → LPO (core encoding proof) |
| `PartB_Main.lean` | 86 | Part B equivalence + axiom audit |
| `PartC_GenFunc.lean` | 179 | Generating function Z(t), properties |
| `PartC_SaddlePoint.lean` | 96 | Saddle point existence (IVT) and uniqueness |
| `PartC_Hessian.lean` | 98 | −3/2 coefficient (algebraically proven) |
| `PartC_ErrorBound.lean` | 117 | Saddle-point expansion + error bound |
| `PartC_Main.lean` | 80 | Part C assembly + axiom audit |
| `Main.lean` | 117 | Top-level theorem + comprehensive audit |
| `SmokeTest.lean` | 13 | Build verification |
| **Total** | **1,804** | |

### Axiom Profile

**Main theorem** (`bh_entropy_axiom_calibration`):
```
[propext, Classical.choice, Quot.sound,
 admissible_set_finite, bmc_of_lpo, entropy_density_gap]
```

**BISH content** (`bh_entropy_computable`, `log_correction_neg_three_halves`):
```
[propext, Classical.choice, Quot.sound]
```
(`Classical.choice` is Mathlib infrastructure, not mathematical content.)

### Three-Part Structure

- **Part A (BISH):** Finite entropy count S(A,γ,δ) = log N — decidable finite combinatorics
- **Part B (LPO):** Entropy density convergence S(A)/A → L ⟺ LPO via BMC
- **Part C (BISH):** The −3/2 logarithmic correction coefficient — algebraic identity

## Series

Paper 17 in the Constructive Reverse Mathematics series.
Full archive: [Zenodo DOI 10.5281/zenodo.18597306](https://doi.org/10.5281/zenodo.18597306)

## License

This work is released for academic use.
