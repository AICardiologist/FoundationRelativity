# Paper 34: Scattering Amplitudes Are Constructively Computable

**Paper 34 in the Constructive Reverse Mathematics Series**

Paul Chun-Kit Lee (dr.paul.c.lee@gmail.com), February 2026

## Overview

This paper establishes that fixed-order scattering cross sections --- the quantities
actually measured at particle colliders --- are fully BISH-computable. No omniscience
principle is required for the predictions that experiments test.

The logical constitution is stratified across six results:

1. **Tree-level amplitudes** are rational functions of Mandelstam invariants (BISH).
2. **One-loop integrals** reduce to dilogarithms Li_2, logarithms, and rational
   functions, all of which are computable (BISH).
3. **Dimensional regularization + MS-bar subtraction** is formal Laurent series
   manipulation (BISH).
4. **Bloch-Nordsieck cancellation** of IR divergences between virtual and real
   emission is algebraic (BISH).
5. **Fixed-order inclusive cross sections** combine the above (BISH --- main result).
6. **All-orders perturbative summation** requires convergence of the perturbation
   series, costing LPO via BMC.

The punchline: everything a collider experiment actually measures (a cross section
at fixed loop order) is BISH. LPO enters only when asserting convergence of the
full perturbation series --- a mathematical idealization, not a physical measurement.

## Main Results

| Theorem | Statement | Level |
|---------|-----------|-------|
| `tree_level_well_defined` | Tree-level cross section is computable | BISH |
| `Li2_computable` | Dilogarithm is BISH-computable | BISH |
| `renormalized_result_bish` | Dim reg + MS-bar is algebraic | BISH |
| `bloch_nordsieck_cancellation` | IR poles cancel algebraically | BISH |
| `fixed_order_bish` | Fixed-order cross section (main result) | BISH |
| `all_orders_sum_lpo` | All-orders perturbative summation | LPO |
| `scattering_amplitudes_constitution` | Master theorem | LPO |

## CRM Classification

| Feature | Logical cost | Why |
|---------|-------------|-----|
| Tree-level amplitude | BISH | Rational function |
| One-loop integrals | BISH | Li_2, log computable |
| Dim reg + MS-bar | BISH | Laurent series algebra |
| IR cancellation | BISH | Algebraic identity |
| Fixed-order cross section | BISH | Finite arithmetic |
| All-orders summation | LPO | BMC for series convergence |

## How to Open and Build

### LaTeX Paper

The compiled PDF is included (`paper34.pdf`). To recompile:

```bash
pdflatex paper34.tex
pdflatex paper34.tex
```

### Lean 4 Formalization

**Prerequisites:** Install [elan](https://github.com/leanprover/elan) (Lean version
manager) and ensure `lake` is available. Requires ~8 GB disk space for Mathlib cache.

```bash
cd P34_ScatteringAmplitudes
lake exe cache get       # downloads prebuilt Mathlib (~5 min)
lake build               # compiles Paper 34 source files (~2-5 min)
```

A successful build produces 0 errors, 0 warnings, and 0 sorries.

## Axiom Audit

All theorems have axiom profile `[propext, Classical.choice, Quot.sound]` plus
explicitly cited axioms. `Classical.choice` is a Lean metatheory axiom from
Mathlib's real number construction --- not an object-level non-constructive principle.

| Axiom | Citation |
|-------|----------|
| `bmc_of_lpo` | Bridges and Vita, *Techniques of Constructive Analysis* (2006), Theorem 2.1.5 |
| `Li2_computable` | Computability of the dilogarithm (analysis) |

**Zero sorry. The fixed-order result uses `Li2_computable` (a BISH-provable
convergence rate, axiomatized due to missing Mathlib infrastructure) in addition
to Lean foundations. It is pure BISH in content.**

## Contents

```
README.md                                This file
paper34.tex                              LaTeX source
paper34.pdf                              Compiled paper
P34_ScatteringAmplitudes/                Lean 4 formalization
  lakefile.lean                          Package configuration
  lean-toolchain                         leanprover/lean4:v4.28.0-rc1
  lake-manifest.json                     Dependency lock file
  Papers.lean                            Root import
  Papers/P34_ScatteringAmplitudes/
    Defs.lean             127 lines      Mandelstam vars, Laurent series, Li_2, IR poles
    TreeLevel.lean         37 lines      Tree-level amplitude (BISH)
    SpecialFunctions.lean  46 lines      Li_2 computability (BISH)
    DimReg.lean            38 lines      Dim reg + MS-bar subtraction (BISH)
    BlochNordsieck.lean    40 lines      IR cancellation (BISH)
    FixedOrder.lean        42 lines      Fixed-order cross section (BISH)
    AllOrders.lean         47 lines      All-orders summation (LPO)
    Main.lean              86 lines      Master theorem + axiom audit
```

8 Lean source files, 463 lines total.

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
- Paper 33: QCD one-loop renormalization and confinement -- DOI: 10.5281/zenodo.18642610
- Paper 34: Scattering amplitudes are constructively computable -- This paper

## License

Apache 2.0 (code) / CC-BY 4.0 (paper).
