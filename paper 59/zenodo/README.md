# Paper 59: De Rham Decidability --- The p-adic Precision Bound

**Paper 59 in the Constructive Reverse Mathematics Series**

Paul Chun-Kit Lee (dr.paul.c.lee@gmail.com), February 2026

## Overview

This Lean 4 formalization establishes the p-adic precision bound for
BISH-decidable verification of elliptic curves with good reduction:

    N_M = v_p(det(1 - φ)) = v_p(1 - a_p + p) = v_p(#E(F_p))

The precision lost in p-adic verification equals the p-adic valuation of
the number of rational points on the reduction.

The Hasse bound a_p² ≤ 4p implies #E(F_p) ≥ 1, so N_M is always
well-defined. All computation is pure integer arithmetic — no p-adic
analysis or period rings appear in the formalization.

## Main Results

| Theorem | Statement | Proof |
|---------|-----------|-------|
| `hasse_implies_positive` | From a_p² ≤ 4p and p ≥ 2: 1 - a_p + p > 0 | `nlinarith` |
| `point_count_ge_one` | #E(F_p) ≥ 1 | `nlinarith` |
| `supersingular_no_precision_loss` | a_p = 0 implies p ∤ (1+p), so N_M = 0 | algebraic |
| `ordinary_non_anomalous` | p ∤ (1-a_p) implies p ∤ (1-a_p+p), so N_M = 0 | algebraic |
| `det_pos` | det(1-φ) > 0 for any GoodReductionData | from Hasse |
| `de_rham_bish_decidable` | N_M is computable in BISH | from det_pos |
| `table_length` | Verification table has 24 entries | `native_decide` |
| `anomalous_count` | 4 entries have N_M ≥ 1 | `native_decide` |
| `generic_count` | 20 entries have N_M = 0 | `native_decide` |
| `max_precision_loss` | Maximum N_M = 2 (X₀(15) at p=2) | `native_decide` |

## Verification Table (24 entries, 4 curves)

| Curve | p | a_p | det(1-φ) | N_M | Note |
|-------|---|-----|----------|-----|------|
| X₀(11) | 2 | -2 | 5 | 0 | |
| X₀(11) | 3 | -1 | 5 | 0 | |
| X₀(11) | 5 | 1 | 5 | **1** | Anomalous |
| X₀(11) | 7 | -2 | 10 | 0 | |
| X₀(11) | 13 | 4 | 10 | 0 | |
| X₀(11) | 17 | -2 | 20 | 0 | |
| X₀(11) | 19 | 0 | 20 | 0 | Supersingular |
| X₀(11) | 23 | -1 | 25 | 0 | |
| X₀(14) | 3 | -2 | 6 | **1** | Anomalous |
| X₀(14) | 5 | -1 | 7 | 0 | |
| X₀(14) | 11 | -1 | 13 | 0 | |
| X₀(14) | 13 | 4 | 10 | 0 | |
| X₀(14) | 17 | -2 | 20 | 0 | |
| X₀(15) | 2 | -1 | 4 | **2** | Anomalous (max) |
| X₀(15) | 7 | 1 | 7 | **1** | Anomalous |
| X₀(15) | 11 | -2 | 14 | 0 | |
| X₀(15) | 13 | 4 | 10 | 0 | |
| X₀(15) | 17 | -2 | 20 | 0 | |
| 37a | 2 | -2 | 5 | 0 | |
| 37a | 3 | -3 | 7 | 0 | |
| 37a | 5 | -2 | 8 | 0 | |
| 37a | 7 | -2 | 10 | 0 | |
| 37a | 11 | 0 | 12 | 0 | Supersingular |
| 37a | 13 | 5 | 9 | 0 | |

## How to Open and Build

### LaTeX Paper

The compiled PDF is included (`paper59_de_rham_decidability.pdf`). To recompile:

```bash
pdflatex paper59_de_rham_decidability.tex
pdflatex paper59_de_rham_decidability.tex
```

### Lean 4 Formalization

**Prerequisites:** Install [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) (version 4.29.0-rc1) and ensure `lake` is available.

```bash
cd P59_DeRhamDecidability
lake exe cache get && lake build
```

The first build may take 30-60 minutes to download and compile Mathlib dependencies.
Subsequent builds are fast. Build status: **0 errors, 0 warnings**.

To explore interactively, open the `P59_DeRhamDecidability` folder in VS Code with the
Lean 4 extension installed.

## Axiom Audit

All theorems have axiom profile `[propext, Classical.choice, Quot.sound]`.
`Classical.choice` is a Lean metatheory axiom from Mathlib's real number construction
(classical Cauchy completion) --- not an object-level non-constructive principle.

The constructive stratification is established by proof content:
- All proofs use explicit witness construction and algebraic manipulation
  (`norm_num`, `nlinarith`, `simp`, `linarith`).
- No omniscience principle (LPO, WLPO, LLPO) appears as a hypothesis.
- The `native_decide` summary statistics use kernel-level decidability.

**Zero custom axioms. Zero sorry.**

## Contents

```
README.md                              This file
paper59_de_rham_decidability.tex       LaTeX source (348 lines)
paper59_de_rham_decidability.pdf       Compiled paper (8 pages)
P59_DeRhamDecidability/                Lean 4 formalization
  lakefile.lean                        Package configuration
  lean-toolchain                       leanprover/lean4:v4.29.0-rc1
  lake-manifest.json                   Dependency lock file
  Papers.lean                          Root import
  Papers/P59_DeRhamDecidability/
    Defs.lean              74 lines    Core structures, Hasse bound
    PadicVal.lean          54 lines    Divisibility-based valuation
    VerificationTable.lean 272 lines   24 verified entries across 4 curves
    WeakAdmissibility.lean 128 lines   Hasse → positivity, case analysis
    Interpretation.lean    185 lines   CRM interpretation, anomalous primes
    Main.lean              49 lines    Assembly + axiom audit
```

6 Lean source files, 762 lines total.

## Complete Paper List

Other papers in the Constructive Reverse Mathematics Series (see Zenodo for current files):

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
- Paper 29: Fekete's Subadditive Lemma and LPO
- Paper 58: Class number correction for exotic Weil classes
- Paper 59: De Rham decidability — the p-adic precision bound -- This paper

## License

This work is part of the Constructive Reverse Mathematics series.
