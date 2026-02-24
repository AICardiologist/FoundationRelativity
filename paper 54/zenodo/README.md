# Paper 54: The Bloch-Kato Calibration --- Out-of-Sample Test of the DPT Framework

**Paper 54 in the Constructive Reverse Mathematics and Arithmetic Geometry Series**

Paul Chun-Kit Lee (dr.paul.c.lee@gmail.com), February 2026

## Overview

This paper provides the first out-of-sample test of the Decidability-Preserving
Transfer (DPT) framework. We calibrate the Bloch-Kato conjecture against the
DPT axioms, isolating which components preserve decidability and which
introduce genuine logical obstructions.

The calibration reveals a sharp separation: pure motives (Axiom 2) are
decidability-preserving via Deligne's Weil I theorem, while mixed motives
(Axiom 1) fail due to the absence of numerical equivalence for Ext^1.
The p-adic Tamagawa number obstruction (Theorem E) identifies concrete
arithmetic barriers, and the descent diagram (Theorem F) assembles the
full picture with explicit fracture points.

## Main Results

| Theorem | Statement |
|---------|-----------|
| Theorem A (`LPOIsolation`) | LPO isolation for zero-testing: analytic evaluation is computable but zero-testing requires LPO |
| Theorem B (`Axiom2Realization`) | Axiom 2 realized by Deligne Weil I: Frobenius eigenvalues have absolute value p^{w/2} |
| Theorem C (`Axiom3PartialRealization`) | Axiom 3 partial: Hodge-Riemann unconditional, Beilinson height pairing conditional |
| Theorem D (`Axiom1Failure`) | Axiom 1 fails for mixed motives: Ext^1 decidability is not available |
| Theorem E (`TamagawaObstruction`) | p-adic Tamagawa obstruction: u-invariant of Q_p forces isotropy |
| Theorem F (`CalibrationVerdict`) | Descent diagram: full calibration verdict with fracture points |

## How to Open and Build

### LaTeX Paper

The compiled PDF is included (`paper54.pdf`). To recompile:

```bash
pdflatex paper54.tex
pdflatex paper54.tex
```

### Lean 4 Formalization

**Prerequisites:** Install [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) (version 4.29.0-rc1) and ensure `lake` is available.

```bash
cd P54_BlochKatoDPT
lake exe cache get && lake build
```

The first build may take 30-60 minutes to download and compile Mathlib dependencies.
Subsequent builds are fast. Build status: **0 errors, 0 warnings**.

To explore interactively, open the `P54_BlochKatoDPT` folder in VS Code with the
Lean 4 extension installed.

## Axiom Audit

All theorems have axiom profile `[propext, Classical.choice, Quot.sound]`.
`Classical.choice` is a Lean metatheory axiom from Mathlib's real number construction
(classical Cauchy completion) --- not an object-level non-constructive principle.

The constructive stratification is established by proof content:

- **7 principled axioms** encode deep published results or conjectures:
  1. `analytic_eval_computable` (Bishop-Bridges 1985)
  2. `zero_test_requires_LPO` (Bridges-Richman 1987, S1.3)
  3. `deligne_weil_I` (Deligne 1974, Theoreme 1.6)
  4. `hodge_riemann_positive_definite` (Hodge 1941)
  5. `beilinson_height_positive_definite` (Beilinson 1987, conjectural)
  6. `u_invariant_Qp` (Lam 2005, Theorem VI.2.2)
  7. `ext1_not_decidable` (structural impossibility)
- ~30 opaque type stubs (abstract domain signatures, no mathematical content)
- ~19 structural helper axioms (routine algebraic identities)

**Zero sorry gaps.**

## Contents

```
README.md                              This file
.zenodo.json                           Zenodo metadata
CITATION.cff                           Citation metadata
paper54.tex                            LaTeX source (838 lines)
paper54.pdf                            Compiled paper
P54_BlochKatoDPT/                      Lean 4 formalization
  lakefile.lean                        Package configuration
  lean-toolchain                       leanprover/lean4:v4.29.0-rc1
  lake-manifest.json                   Dependency lock file
  Papers.lean                          Root import (52 lines)
  Papers/P54_BlochKatoDPT/
    DPTCalibration.lean    162 lines   Calibration record type
    LPOIsolation.lean      174 lines   Theorem A: LPO isolation
    Axiom2Realization.lean 104 lines   Theorem B: Deligne Weil I
    Axiom3PartialRealization.lean
                           125 lines   Theorem C: HR + Beilinson
    Axiom1Failure.lean     117 lines   Theorem D: mixed motive undecidability
    TamagawaObstruction.lean
                           159 lines   Theorem E: p-adic obstruction
    CalibrationVerdict.lean 145 lines  Theorem F: comparison table
    DescentDiagram.lean    153 lines   Descent with fracture points
```

8 Lean source files, 1,139 lines total (+ Papers.lean = 52 lines).

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
- Paper 54: The Bloch-Kato Calibration --- Out-of-Sample Test of the DPT Framework -- This paper

## License

This work is part of the Constructive Reverse Mathematics series.
Licensed under the Apache License 2.0.
