# Paper 32: QED One-Loop Renormalization --- The Landau Pole

**Paper 32 in the Constructive Reverse Mathematics Series**

Paul Chun-Kit Lee (dr.paul.c.lee@gmail.com), February 2026

## Overview

This paper carries out a complete constructive reverse-mathematical calibration of
QED one-loop renormalization. The running coupling constant, governed by the one-loop
beta function d(alpha)/d(ln mu) = b * alpha^2 with b = 2/(3*pi), is classified
across six theorems.

The surprise: the Landau pole divergence --- naively the most "non-constructive"
feature of QED --- is fully BISH-computable. The closed-form ODE solution
alpha(mu) = alpha_0 / (1 - b*alpha_0*ln(mu/mu_0)) provides an explicit Cauchy
modulus delta(M) = mu_L * (1 - exp(-1/(b*M))) requiring no omniscience.

## Main Results

| Theorem | Statement | Level |
|---------|-----------|-------|
| `discrete_step_growth` | Discrete RG steps are monotonically increasing | BISH |
| `coupling_computable_below_pole` | Exact coupling computable below Landau pole | BISH |
| `threshold_decision_wlpo` | Threshold crossing decisions | WLPO |
| `global_coupling_exists_lpo` | Global coupling converges via BMC | LPO |
| `landau_pole_bish_classification` | Landau pole divergence (the surprise!) | BISH |
| `ward_identity_algebraic` | Ward-Takahashi identity preservation | BISH |
| `qed_logical_constitution` | Master theorem: complete CRM classification | LPO |

## CRM Classification

| Feature | Logical cost | Why |
|---------|-------------|-----|
| Discrete RG step | BISH | Finite arithmetic |
| Coupling below pole | BISH | Closed-form solution |
| Landau pole divergence | BISH | Explicit Cauchy modulus |
| Ward-Takahashi identity | BISH | Algebraic identity |
| Threshold crossings | WLPO | Zero-test for mass gaps |
| Global coupling | LPO | BMC across thresholds |

## How to Open and Build

### LaTeX Paper

The compiled PDF is included (`paper32.pdf`). To recompile:

```bash
pdflatex paper32.tex
pdflatex paper32.tex
```

### Lean 4 Formalization

**Prerequisites:** Install [elan](https://github.com/leanprover/elan) (Lean version
manager) and ensure `lake` is available. Requires ~8 GB disk space for Mathlib cache.

```bash
cd P32_QEDRenormalization
lake exe cache get       # downloads prebuilt Mathlib (~5 min)
lake build               # compiles Paper 32 source files (~2-5 min)
```

A successful build produces 0 errors, 0 warnings, and 0 sorries.

## Axiom Audit

All theorems have axiom profile `[propext, Classical.choice, Quot.sound]` plus
explicitly cited literature axioms. `Classical.choice` is a Lean metatheory axiom from
Mathlib's real number construction --- not an object-level non-constructive principle.

| Axiom | Citation |
|-------|----------|
| `bmc_of_lpo` | Bridges and Vita, *Techniques of Constructive Analysis* (2006), Theorem 2.1.5 |
| `wlpo_of_lpo` | Standard CRM implication |
| `coupling_exceeds_at_delta` | Monotone coupling exceeds threshold at precision delta |

**Zero sorry.**

## Contents

```
README.md                                This file
paper32.tex                              LaTeX source
paper32.pdf                              Compiled paper
P32_QEDRenormalization/                  Lean 4 formalization
  lakefile.lean                          Package configuration
  lean-toolchain                         leanprover/lean4:v4.28.0-rc1
  lake-manifest.json                     Dependency lock file
  Papers.lean                            Root import
  Papers/P32_QEDRenormalization/
    Defs.lean              123 lines     QED constants, coupling, Landau pole, thresholds
    DiscreteRG.lean         56 lines     Theorem 1: discrete step growth (BISH)
    FinitePrecision.lean    80 lines     Theorem 2: coupling below pole (BISH)
    Threshold.lean          63 lines     Theorem 3: threshold crossing (WLPO)
    GlobalCoupling.lean     56 lines     Theorem 4: global coupling (LPO via BMC)
    LandauPole.lean        107 lines     Theorem 5: Landau divergence (BISH)
    WardIdentity.lean       53 lines     Theorem 6: Ward-Takahashi (BISH)
    Main.lean               97 lines     Master theorem + axiom audit
```

8 Lean source files, 635 lines total.

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
- Paper 29: Fekete's Subadditive Lemma and LPO -- DOI: 10.5281/zenodo.18632776
- Paper 30: Physical dispensability of the Fan Theorem -- DOI: (forthcoming)
- Paper 31: Physical dispensability of Dependent Choice -- DOI: 10.5281/zenodo.18645578
- Paper 32: QED one-loop renormalization, Landau pole -- This paper

## License

Apache 2.0 (code) / CC-BY 4.0 (paper).
