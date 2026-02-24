# Paper 33: QCD One-Loop Renormalization and Confinement

**Paper 33 in the Constructive Reverse Mathematics Series**

Paul Chun-Kit Lee (dr.paul.c.lee@gmail.com), February 2026

## Overview

This paper carries out a complete constructive reverse-mathematical calibration of
QCD one-loop renormalization and extends the analysis to the non-perturbative sector:
confinement and the mass gap.

The QCD running coupling, governed by the one-loop beta function with the
negative coefficient b_0 = (33 - 2 n_f) / (12 pi), exhibits asymptotic freedom ---
the coupling decreases at high energies. The paper proves that asymptotic freedom
is BISH-computable, Λ_QCD divergence has an explicit Cauchy modulus (BISH),
threshold crossings cost WLPO, and the continuum limit of lattice QCD costs LPO
via BMC.

The surprise: **confinement is FREE.** The LPO already paid for the continuum
limit automatically subsidizes both the WLPO for the mass gap decision
(Δ = 0 ∨ Δ > 0) and the MP for extracting strict positivity (Δ > 0). The
boundary of QCD is BISH+LPO.

## Main Results

| Theorem | Statement | Level |
|---------|-----------|-------|
| `qcd_step_decrease` | QCD discrete RG step decreases (asymptotic freedom) | BISH |
| `lambda_qcd_divergence_bish` | Λ_QCD divergence with explicit Cauchy modulus | BISH |
| `qcd_threshold_decision` | Quark mass threshold crossings | WLPO |
| `continuum_limit_lpo` | Continuum limit of lattice QCD | LPO (via BMC) |
| `mass_gap_decision_wlpo` | Mass gap decision: Δ = 0 ∨ Δ > 0 | WLPO |
| `confinement_free` | Mass gap strict positivity: Δ > 0 | LPO (FREE!) |
| `qcd_logical_constitution` | Master theorem: complete CRM classification | LPO |

## CRM Classification

| Feature | Logical cost | Why |
|---------|-------------|-----|
| Discrete RG step (asymptotic freedom) | BISH | Finite arithmetic |
| Λ_QCD divergence | BISH | Explicit Cauchy modulus |
| Finite lattice mass gap | BISH | Finite-dimensional |
| Threshold crossings | WLPO | Zero-test for quark masses |
| Continuum limit | LPO | BMC for lattice sequence |
| Mass gap decision | WLPO ⊆ LPO | Subsumed by continuum limit |
| Confinement (Δ > 0) | MP ⊆ LPO | Subsumed by continuum limit |

## How to Open and Build

### LaTeX Paper

The compiled PDF is included (`paper33.pdf`). To recompile:

```bash
pdflatex paper33.tex
pdflatex paper33.tex
```

### Lean 4 Formalization

**Prerequisites:** Install [elan](https://github.com/leanprover/elan) (Lean version
manager) and ensure `lake` is available. Requires ~8 GB disk space for Mathlib cache.

```bash
cd P33_QCDConfinement
lake exe cache get       # downloads prebuilt Mathlib (~5 min)
lake build               # compiles Paper 33 source files (~2-5 min)
```

A successful build produces 0 errors, 0 warnings, and 0 sorries.

## Axiom Audit

All theorems have axiom profile `[propext, Classical.choice, Quot.sound]` plus
explicitly cited axioms. `Classical.choice` is a Lean metatheory axiom from
Mathlib's real number construction --- not an object-level non-constructive principle.

| Axiom | Citation |
|-------|----------|
| `bmc_of_lpo` | Bridges and Vita, *Techniques of Constructive Analysis* (2006), Theorem 2.1.5 |
| `wlpo_of_lpo` | Standard CRM hierarchy |
| `mp_of_lpo` | Standard CRM hierarchy |
| `coupling_exceeds_at_qcd_delta` | Quantitative calculus bound |
| `YM_gap_nonneg` | Mass gap >= 0 (physics) |
| `YM_gap_not_zero` | Mass gap != 0 (Millennium Prize hypothesis) |

**Zero sorry.**

## Contents

```
README.md                              This file
paper33.tex                            LaTeX source
paper33.pdf                            Compiled paper
P33_QCDConfinement/                    Lean 4 formalization
  lakefile.lean                        Package configuration
  lean-toolchain                       leanprover/lean4:v4.28.0-rc1
  lake-manifest.json                   Dependency lock file
  Papers.lean                          Root import
  Papers/P33_QCDConfinement/
    Defs.lean             120 lines    QCD constants, coupling, Λ_QCD, thresholds
    PerturbativeQCD.lean   88 lines    Asymptotic freedom, Λ_QCD divergence (BISH)
    Thresholds.lean        43 lines    Threshold crossing decisions (WLPO)
    LatticeContinuum.lean  52 lines    Continuum limit of lattice QCD (LPO)
    MillenniumGap.lean     76 lines    Mass gap decision + confinement (FREE)
    Main.lean             102 lines    Master theorem + axiom audit
```

6 Lean source files, 481 lines total.

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
- Paper 10: Logical geography of mathematical physics -- DOI: 10.5281/zenodo.18627193
- Paper 11: Entanglement, CHSH, Tsirelson bound -- DOI: 10.5281/zenodo.18527676
- Paper 12: Constructive history of mathematical physics -- DOI: 10.5281/zenodo.18627283
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
- Paper 25: Ergodic theorems and laws of large numbers -- DOI: 10.5281/zenodo.18615453
- Paper 26: Bidual gap detection, Godel sequences -- DOI: 10.5281/zenodo.18615457
- Paper 27: IVT as mechanism behind LLPO in Bell physics -- DOI: 10.5281/zenodo.18615459
- Paper 28: Classical mechanics -- DOI: 10.5281/zenodo.18616620
- Paper 29: Fekete's Subadditive Lemma and LPO -- DOI: 10.5281/zenodo.18643617
- Paper 30: Physical dispensability of the Fan Theorem -- DOI: 10.5281/zenodo.18638394
- Paper 31: Physical dispensability of Dependent Choice -- DOI: 10.5281/zenodo.18645578
- Paper 32: QED one-loop renormalization, Landau pole -- DOI: 10.5281/zenodo.18642598
- Paper 33: QCD one-loop renormalization and confinement -- This paper

## License

Apache 2.0 (code) / CC-BY 4.0 (paper).
