# Paper 30: The Physical Dispensability of the Fan Theorem

**Paper 30 in the Constructive Reverse Mathematics Series**

Paul Chun-Kit Lee (dr.paul.c.lee@gmail.com), February 2026

## Overview

Papers 23 and 28 established that compact optimization (the Extreme Value Theorem on
[a,b]) and variational action minimization in classical mechanics each cost exactly
the Fan Theorem (FT) over BISH. Paper 29 established that Fekete's Subadditive Lemma
is equivalent to LPO, and that LPO is physically instantiated because phase
transitions are real.

This paper proves that every empirically accessible prediction derived from the
FT-calibrated results in Papers 23 and 28 is recoverable in BISH+LPO, without
invoking the Fan Theorem. The argument rests on three pillars:

1. LPO implies bounded monotone convergence (BMC), which yields the supremum and
   epsilon-approximate witnesses for any continuous function on [a,b].
2. The equations of motion (Euler-Lagrange equations) are BISH-valid and do not
   require any minimizer to exist.
3. No finite experiment can distinguish an exact minimizer from an
   epsilon-approximate one.

Together: FT captures exact existence of an optimizer; LPO captures convergent
approximation to the supremum. Since no laboratory measurement has infinite
precision, FT is physically dispensable.

## Main Results

| Theorem | Statement | Level |
|---------|-----------|-------|
| `approxEVT_of_lpo` | LPO -> ApproxEVT | LPO |
| `exactEVT_iff_ft` | ExactEVT <-> FanTheorem | FT |
| `empirical_completeness` | LPO provides all finite-precision predictions | LPO |
| `variational_stratification` | EL is BISH; approx min is LPO; exact min is FT | Stratified |
| `ft_physically_dispensable` | Master theorem: FT is physically dispensable | LPO |

## Physical Significance

| Route | Logical cost | Example |
|-------|-------------|---------|
| Euler-Lagrange equations | BISH | Equations of motion directly |
| Approximate optimization | LPO (via BMC) | epsilon-attainment on [a,b] |
| Exact optimization | FT | Exact minimizer existence |

Since experiments have finite precision, the LPO route suffices for all empirical
content. The Fan Theorem is a mathematical luxury, not a physical necessity.

## How to Open and Build

### LaTeX Paper

The compiled PDF is included (`paper30.pdf`). To recompile:

```bash
pdflatex paper30.tex
pdflatex paper30.tex
```

### Lean 4 Formalization

**Prerequisites:** Install [elan](https://github.com/leanprover/elan) (Lean version
manager) and ensure `lake` is available. Requires ~8 GB disk space for Mathlib cache.

```bash
cd P30_FTDispensability
lake exe cache get       # downloads prebuilt Mathlib (~5 min)
lake build               # compiles Paper 30 source files (~2-5 min)
```

A successful build produces 0 errors, 0 warnings, and 0 sorries.

## Axiom Audit

All theorems have axiom profile `[propext, Classical.choice, Quot.sound]` plus one
explicitly cited literature axiom. `Classical.choice` is a Lean metatheory axiom from
Mathlib's real number construction --- not an object-level non-constructive principle.

| Axiom | Citation |
|-------|----------|
| `bmc_of_lpo` | Bridges and Vita, *Techniques of Constructive Analysis* (2006), Theorem 2.1.5 |

**Zero sorry. One cited axiom.**

## Contents

```
README.md                              This file
paper30.tex                            LaTeX source
paper30.pdf                            Compiled paper
P30_FTDispensability/                  Lean 4 formalization
  lakefile.lean                        Package configuration
  lean-toolchain                       leanprover/lean4:v4.28.0-rc1
  lake-manifest.json                   Dependency lock file
  Papers.lean                          Root import
  Papers/P30_FTDispensability/
    Defs.lean             113 lines    LPO, BMC, ExactEVT, ApproxEVT, FT, grid infra
    GridApprox.lean       180 lines    Grid point membership, max bounds, density
    SupExists.lean        230 lines    BMC -> supremum existence + epsilon-attainment
    ApproxAttain.lean      57 lines    LPO -> ApproxEVT, empirical completeness
    Separation.lean       126 lines    Rescaling lemmas, ExactEVT <-> FT
    Variational.lean      136 lines    EL is BISH, approx min from LPO, stratification
    Main.lean              76 lines    Master theorem + axiom audit
```

7 Lean source files, 918 lines total.

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
- Paper 30: Physical dispensability of the Fan Theorem -- This paper

## License

Apache 2.0 (code) / CC-BY 4.0 (paper).
