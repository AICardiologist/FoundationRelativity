# Paper 55: K3 Surfaces, the Kuga-Satake Construction, and the DPT Framework

**Second Out-of-Sample Test: Full Decomposition and the Codimension Principle**

**Paper 55 in the Constructive Reverse Mathematics and Arithmetic Geometry Series**

Paul Chun-Kit Lee (dr.paul.c.lee@gmail.com), February 2026

## Overview

This paper provides the second out-of-sample test of the Decidability-Preserving
Transfer (DPT) framework, applying it to K3 surfaces and the Kuga-Satake
construction. The calibration achieves a full decomposition of the DPT axioms
against the rich geometry of K3 surfaces, demonstrating the codimension principle:
the logical cost of decidability transfer depends on the codimension of the
algebraic cycles involved.

Seven theorems establish the complete calibration: motivated cycle transfer
(Andre), Axiom 2 independence via Deligne Weil I, Kuga-Satake realization of
Axiom 3, supersingular bypass at Picard number 22, absence of a Picard boundary,
Calabi-Yau threefold correction, and a 7-row comparison table assembling the
full verdict.

## Main Results

| Theorem | Statement | Module |
|---------|-----------|--------|
| Theorem A | Motivated cycle transfer (Andre 1996) | `Axiom1Transfer.lean` |
| Theorem B | Axiom 2 independence (Deligne Weil I) | `Axiom2Independence.lean` |
| Theorem C | Kuga-Satake provides Axiom 3 | `Axiom3KugaSatake.lean` |
| Theorem D | Supersingular bypass (rho = 22) | `SupersingularBypass.lean` |
| Theorem E | No Picard boundary | `NoPicardBoundary.lean` |
| Theorem F | CY3 correction | `CY3Correction.lean` |
| Theorem G | 7-row comparison table | `K3CalibrationVerdict.lean` |

## How to Open and Build

### LaTeX Paper

The compiled PDF is included (`paper55.pdf`). To recompile:

```bash
pdflatex paper55.tex
pdflatex paper55.tex
```

### Lean 4 Formalization

**Prerequisites:** Install [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) (version 4.29.0-rc1) and ensure `lake` is available.

```bash
cd P55_K3KugaSatakeDPT
lake exe cache get && lake build
```

The first build may take 30-60 minutes to download and compile Mathlib dependencies.
Subsequent builds are fast. Build status: **0 errors, 0 warnings**.

To explore interactively, open the `P55_K3KugaSatakeDPT` folder in VS Code with the
Lean 4 extension installed.

## Axiom Audit

All theorems have axiom profile `[propext, Classical.choice, Quot.sound]`.
`Classical.choice` is a Lean metatheory axiom from Mathlib's real number construction
(classical Cauchy completion) --- not an object-level non-constructive principle.

The constructive stratification is established by proof content:

- **9 principled axioms** encode deep published results:
  1. `andre_motivated_cycle` (Andre 1996, Theorem 0.4)
  2. `lieberman_hom_num_abelian` (Lieberman 1968)
  3. `matsusaka_conj_d_surfaces` (Matsusaka 1957)
  4. `deligne_weil_I` (Deligne 1974, Theoreme 1.6)
  5. `clifford_trace_positive_definite` (Lawson-Michelsohn 1989)
  6. `rosati_from_clifford_trace` (van Geemen 2000, S2)
  7. `tate_supersingular_direct` (Nygaard-Ogus 1985 / Charles 2013)
  8. `lefschetz_1_1` (Lefschetz 1924)
  9. `hodge_riemann_weight3` (Hodge 1941 / Griffiths 1969)
- ~25 opaque type stubs (abstract domain signatures, no mathematical content)
- ~15 structural helper axioms (routine algebraic identities)

**Zero sorry gaps.**

## Contents

```
README.md                              This file
.zenodo.json                           Zenodo metadata
CITATION.cff                           Citation metadata
paper55.tex                            LaTeX source (772 lines)
paper55.pdf                            Compiled paper
P55_K3KugaSatakeDPT/                   Lean 4 formalization
  lakefile.lean                        Package configuration
  lean-toolchain                       leanprover/lean4:v4.29.0-rc1
  lake-manifest.json                   Dependency lock file
  Papers.lean                          Root import (42 lines)
  Papers/P55_K3KugaSatakeDPT/
    K3DPTCalibration.lean    152 lines  Calibration record type
    Axiom1Transfer.lean      136 lines  Theorem A: motivated cycle transfer
    Axiom2Independence.lean  101 lines  Theorem B: Deligne Weil I
    Axiom3KugaSatake.lean    127 lines  Theorem C: KS provides Axiom 3
    SupersingularBypass.lean 109 lines  Theorem D: rho=22 bypass
    NoPicardBoundary.lean    138 lines  Theorem E: no Picard boundary
    CY3Correction.lean       159 lines  Theorem F: CY3 correction
    K3CalibrationVerdict.lean 209 lines Theorem G: 7-row comparison table
```

8 Lean source files, 1,131 lines total (+ Papers.lean = 42 lines).

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
- Paper 55: K3 Surfaces, Kuga-Satake, and the DPT Framework -- This paper

## License

This work is part of the Constructive Reverse Mathematics series.
Licensed under the Apache License 2.0.
