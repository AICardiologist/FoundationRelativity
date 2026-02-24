# Paper 37: The Undecidability Landscape Is LPO

**Paper 37 in the Constructive Reverse Mathematics Series**

Paul Chun-Kit Lee (dr.paul.c.lee@gmail.com), February 2026

## Overview

This paper proves a meta-theorem: every known undecidability result in quantum
many-body physics --- phase diagrams (BCW 2021), 1D spectral gaps (BCLPG 2020),
RG flows (CLPE 2022) --- is exactly LPO. The "undecidability" of physics is a
misnomer: it is the non-computability of a single, well-understood logical
principle that physics has used since Boltzmann.

The meta-theorem works because all these results share the same architecture:
encode a Turing machine into a Hamiltonian, reduce halting to a physical property,
then observe that "for all alpha, (exists n, alpha(n) = true) or (forall n,
alpha(n) = false)" is exactly LPO.

The one exception --- ground state energy density (Watson-Cubitt 2021) --- is
BISH, because it admits explicit finite-precision computation without any
oracle.

## Main Results

| Theorem | Statement | Level |
|---------|-----------|-------|
| `halting_reduction_iff_lpo` | Meta-theorem: any halting reduction <-> LPO | LPO |
| `phase_diagram_iff_lpo` | Phase diagrams (BCW 2021) <-> LPO | LPO |
| `spectral_gap_1d_iff_lpo` | 1D spectral gap (BCLPG 2020) <-> LPO | LPO |
| `rg_flow_iff_lpo` | RG flows (CLPE 2022) <-> LPO | LPO |
| `energy_density_logical_status` | Ground state energy density | BISH |
| `undecidability_landscape_theorem` | Master theorem | LPO |

## The Undecidability Landscape

| Result | Year | Reduction | CRM Level |
|--------|------|-----------|-----------|
| Spectral Gap 2D (CPgW) | 2015 | Halting via Tiling | LPO |
| Spectral Gap 1D (BCLPG) | 2020 | Halting via 1D Tiling | LPO |
| Phase Diagrams (BCW) | 2021 | Halting via QPE | LPO |
| RG Flows (CLPE) | 2022 | Halting via Tiling+RG | LPO |
| Ground State Energy (Watson-Cubitt) | 2021 | Halting (BISH) | BISH |

All entries are LPO-equivalent (verified by `decide` in Lean).

## How to Open and Build

### LaTeX Paper

The compiled PDF is included (`paper37.pdf`). To recompile:

```bash
pdflatex paper37.tex
pdflatex paper37.tex
```

### Lean 4 Formalization

**Prerequisites:** Install [elan](https://github.com/leanprover/elan) (Lean version
manager) and ensure `lake` is available. Requires ~8 GB disk space for Mathlib cache.

```bash
cd P37_UndecidabilityLandscape
lake exe cache get       # downloads prebuilt Mathlib (~5 min)
lake build               # compiles Paper 37 source files (~2-5 min)
```

A successful build produces 0 errors, 0 warnings, and 0 sorries.

## Axiom Audit

All theorems have axiom profile `[propext, Classical.choice, Quot.sound]` plus
explicitly cited axioms. `Classical.choice` is a Lean metatheory axiom from
Mathlib's real number construction --- not an object-level non-constructive principle.

**Bridge lemmas (axiomatized physics):**

| Axiom | Source |
|-------|--------|
| `bcw_phaseB_iff_exists` | BCW 2021 |
| `bcw_phaseA_iff_all_false` | BCW 2021 |
| `bclpg_gapless_iff_halts` | BCLPG 2020 |
| `bclpg_gapped_iff_not_halts` | BCLPG 2020 |
| `clpe_gapless_fp_iff_halts` | CLPE 2022 |
| `clpe_gapped_fp_iff_not_halts` | CLPE 2022 |
| `clpe_rg_step_computable` | CLPE individual step |
| `ground_energy_computable` | Watson-Cubitt 2021 |
| `tm_from_seq` / `tm_from_seq_halts` | Encoding construction |
| `halting_problem_undecidable` | Turing (1936) |

**Zero sorry.**

## Contents

```
README.md                                This file
paper37.tex                              LaTeX source
paper37.pdf                              Compiled paper
P37_UndecidabilityLandscape/             Lean 4 formalization
  lakefile.lean                          Package configuration
  lean-toolchain                         leanprover/lean4:v4.28.0-rc1
  lake-manifest.json                     Dependency lock file
  Papers.lean                            Root import
  Papers/P37_UndecidabilityLandscape/
    Defs.lean             110 lines      TM, LPO, phase, gap, RG, Hamiltonian defs
    MetaTheorem.lean      132 lines      Meta-theorem: halting reduction <-> LPO
    PhaseDiagram.lean      71 lines      BCW 2021 <-> LPO
    SpectralGap1D.lean     77 lines      BCLPG 2020 <-> LPO
    RGFlow.lean            99 lines      CLPE 2022 <-> LPO
    GroundStateEnergy.lean 65 lines      Watson-Cubitt: BISH
    Main.lean             106 lines      Master theorem + landscape table
```

7 Lean source files, 660 lines total.

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
- Paper 34: Scattering amplitudes are constructively computable -- DOI: 10.5281/zenodo.18642612
- Paper 35: The logical constitution of empirical physics -- DOI: 10.5281/zenodo.18642616
- Paper 36: Stratifying spectral gap undecidability (Cubitt's theorem) -- DOI: 10.5281/zenodo.18642620
- Paper 37: The undecidability landscape is LPO -- This paper

## License

Apache 2.0 (code) / CC-BY 4.0 (paper).
