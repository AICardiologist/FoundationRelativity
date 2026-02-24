# Paper 23: The Fan Theorem and the Constructive Cost of Optimization

**Free Energy Extrema on Compact Parameter Spaces**

Paper 23 in the Constructive Reverse Mathematics Series
Paul C.-K. Lee (NYU), February 2026

DOI: 10.5281/zenodo.18604312

## Overview

This paper establishes that the assertion "a continuous function on a compact interval
attains its extremum" -- the Extreme Value Theorem (EVT) -- is equivalent to the
Fan Theorem (FT) over BISH, and instantiates this equivalence through free energy
optimization in the 1D Ising model.

This is the first CRM calibration at the Fan Theorem, adding a third independent branch
to the calibration hierarchy (independent of the LPO/WLPO/LLPO omniscience chain).

## Main Results

| Theorem | Statement |
|---------|-----------|
| `ft_iff_compact_opt` | FanTheorem <-> CompactOptimization |
| `evt_max_iff_evt_min` | EVT_max <-> EVT_min |
| `ising_opt_of_ft` | FT -> Ising free energy attains its minimum on [a, b] |
| `fan_stratification` | Three-branch partial order (omniscience + MP + FT) |
| `finite_opt_bish` | Finite-grid optimization is BISH |

## How to Open and Build

### LaTeX Paper

The compiled PDF is included (`paper23_writeup.pdf`). To recompile from source:

```bash
pdflatex paper23_writeup
bibtex paper23_writeup
pdflatex paper23_writeup
pdflatex paper23_writeup
```

### Lean 4 Formalization

**Prerequisites:** Install [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) (version 4.28.0-rc1) and ensure `lake` is available.

```bash
cd P23_FanTheorem
lake build    # Downloads Mathlib, then builds (0 errors, 0 warnings, 0 sorry)
```

The first build may take 30-60 minutes to download and compile Mathlib dependencies.
Subsequent builds are fast (seconds).

To explore interactively, open the `P23_FanTheorem` folder in VS Code with the
Lean 4 extension installed.

## Axiom Audit

**ZERO custom axioms.** Every theorem depends only on Mathlib infrastructure
(`propext`, `Classical.choice`, `Quot.sound`). This is the cleanest axiom audit
of any paper in the CRM series (Papers 2-24).

## Contents

```
README.md                             This file
paper23_writeup.tex                   LaTeX source
paper23_writeup.pdf                   Compiled paper
paper23_references.bib                Bibliography
paper23_fan_theorem_proof.md          Proof specification
P23_FanTheorem/                       Lean 4 formalization
  lakefile.lean                       Package configuration
  lean-toolchain                      leanprover/lean4:v4.28.0-rc1
  Papers.lean                         Root import
  lake-manifest.json                  Dependency lock file
  README.md                           Lean project documentation
  Papers/P23_FanTheorem/
    Defs/
      EVT.lean                        EVT_max, EVT_min, CompactOptimization, FanTheorem
      IsingFreeEnergy.lean            isingFreeEnergy, positivity helpers
      Principles.lean                 LPO, WLPO, LLPO, MP, hierarchy proofs
      Rescaling.lean                  rescale/unscale between [0,1] and [a,b]
    PartA/
      Continuity.lean                 isingFreeEnergy_continuous
      FiniteOpt.lean                  finite_opt_bish (Finset.exists_min_image)
      PartA_Main.lean                 Summary and axiom audit
    PartB/
      EVTEquiv.lean                   EVT_max <-> EVT_min (negate f)
      CompactOpt.lean                 EVT_min <-> CompactOptimization (rescaling)
      PartB_Main.lean                 ft_iff_compact_opt
    Main/
      PhysicalInstance.lean           ising_opt_of_ft
      Stratification.lean             fan_stratification (three-branch)
      AxiomAudit.lean                 Comprehensive #print axioms
    Main.lean                         Root imports
```

14 Lean files, ~684 lines total.

## The 1D Ising Model: Four Logical Costs

The same physical system now exhibits four distinct logical costs across Papers 8, 20, 22, and 23:

| Question | Principle | Paper |
|----------|-----------|-------|
| Finite-volume computation | BISH | 8 (Part A) |
| Thermodynamic limit existence | LPO | 8 (Part B) |
| Phase classification (magnetization zero-test) | WLPO | 20 |
| Parameter-space optimization | FT | 23 |

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
- Paper 10: Logical geography of mathematical physics -- DOI: 10.5281/zenodo.18580342 [v 2.0 Technical Synthesis of Papers 1-16]
- Paper 11: Entanglement, CHSH, Tsirelson bound -- DOI: 10.5281/zenodo.18527676
- Paper 12: Constructive history of mathematical physics -- DOI: 10.5281/zenodo.18581707 [v 2.0 Historical Synthesis of Papers 1-16]
- Paper 13: Event horizon as logical boundary -- DOI: 10.5281/zenodo.18529007
- Paper 14: Quantum decoherence -- DOI: 10.5281/zenodo.18569068
- Paper 15: Noether theorem -- DOI: 10.5281/zenodo.18572494
- Paper 16: Technical note: Born rule -- DOI: 10.5281/zenodo.18575377
- Paper 17: Bekenstein-Hawking formula -- DOI: 10.5281/zenodo.18597306
- Paper 18: Fermion mass hierarchy and scaffolding principle -- DOI: 10.5281/zenodo.18600243
- Paper 19: WKB tunneling and LLPO -- DOI: 10.5281/zenodo.18602596
- Paper 20: Observable-dependent logical cost, 1D Ising magnetization and WLPO -- DOI: 10.5281/zenodo.18603079
- Paper 21: Bell nonlocality and LLPO -- DOI: 10.5281/zenodo.18603251
- Paper 22: Markov's Principle and radioactive decay -- DOI: 10.5281/zenodo.18603503
- Paper 23: Fan Theorem and optimization -- DOI: 10.5281/zenodo.18604312
- Paper 24: Kochen-Specker contextuality and LLPO -- DOI: 10.5281/zenodo.18604317

## License

This work is part of the Constructive Reverse Mathematics series.
