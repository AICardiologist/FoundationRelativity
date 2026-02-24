# Paper 57: The Complete Class-Number-1 Landscape for Exotic Weil Self-Intersection

**All Nine Imaginary Quadratic Fields with h_K = 1**

**Paper 57 in the Constructive Reverse Mathematics and Arithmetic Geometry Series**

Paul Chun-Kit Lee (dr.paul.c.lee@gmail.com), February 2026

## Overview

This Lean 4 formalization extends Paper 56 to **all nine** class-number-1 imaginary
quadratic fields. By the Baker--Heegner--Stark theorem, the complete list of
imaginary quadratic fields K = Q(sqrt(-d)) with class number h_K = 1 is:

  d in {1, 2, 3, 7, 11, 19, 43, 67, 163}

For each field, we compute the trace matrix, verify the discriminant via
`native_decide`, derive the Weil class degree via the cyclic conductor theorem
(disc(F) = conductor^2, so d_0 = conductor), and assemble the full 9-row
pattern table with Heuristic Regularity (HR) and Dispensability of Physical
Totality (DPT) verdicts.

The Lean project P57_CompleteClassNumber1 comprises 3 active modules (~918 lines)
plus 1 deprecated module, totaling 1,257 lines of Lean 4 (+ Papers.lean = 25 lines).
Sorry budget: 1 principled axiom (`weil_class_degree_eq_conductor`), 0 gaps.

## Results Table

All nine class-number-1 imaginary quadratic fields:

| d | Field K | disc(F) | Weil class degree d_0 |
|----:|---------|--------:|----------------------:|
| 1 | Q(i) | 81 | 9 |
| 2 | Q(sqrt(-2)) | 361 | 19 |
| 3 | Q(sqrt(-3)) | 49 | 7 |
| 7 | Q(sqrt(-7)) | 169 | 13 |
| 11 | Q(sqrt(-11)) | 1369 | 37 |
| 19 | Q(sqrt(-19)) | 3721 | 61 |
| 43 | Q(sqrt(-43)) | 6241 | 79 |
| 67 | Q(sqrt(-67)) | 26569 | 163 |
| 163 | Q(sqrt(-163)) | 9409 | 97 |

All nine discriminant computations are machine-verified via `native_decide`.
All nine Gram matrix instantiations are machine-verified.

## How to Open and Build

### LaTeX Paper

The compiled PDF is included (`paper57.pdf`). To recompile:

```bash
pdflatex paper57.tex
pdflatex paper57.tex
```

### Lean 4 Formalization

**Prerequisites:** Install [elan](https://github.com/leanprover/elan) (Lean version
manager) and ensure `lake` is available. Requires ~8 GB disk space for Mathlib cache.

```bash
cd P57_CompleteClassNumber1
lake exe cache get       # downloads prebuilt Mathlib (~5 min)
lake build               # compiles Paper 57 source files (~2-5 min)
```

A successful build produces 0 errors and 0 warnings.

## Axiom Audit

All theorems have axiom profile `[propext, Classical.choice, Quot.sound]` plus
one principled axiom:

| Axiom | Role |
|-------|------|
| `weil_class_degree_eq_conductor` | Cyclic conductor theorem: Weil class degree equals the conductor |

`Classical.choice` is a Lean metatheory axiom from Mathlib's real number
construction (classical Cauchy completion) -- not an object-level
non-constructive principle.

**1 principled axiom. 0 sorry. 0 gaps.**

## Contents

```
zenodo/
  README.md                              This file
  .zenodo.json                           Zenodo metadata
  CITATION.cff                           Citation metadata
  paper57.tex                            LaTeX source (598 lines)
  paper57.pdf                            Compiled paper
  P57_CompleteClassNumber1/              Lean 4 formalization
    lakefile.lean                        Package configuration
    lean-toolchain                       leanprover/lean4:v4.29.0-rc1
    lake-manifest.json                   Dependency lock file
    Papers.lean                          Root import (25 lines)
    Papers/P57_CompleteClassNumber1/
      NumberFieldData.lean               206 lines  9 trace matrices, disc(F) via native_decide
      GramMatrixDerivation.lean          418 lines  9 fields, d_0^2 = disc(F), Gram verifications
      PatternAndVerdict.lean             294 lines  9-row pattern table, HR, DPT verdict
      GramMatrixDerivation_v3_deprecated.lean
                                         339 lines  Deprecated v3 (det(G)=disc(F) is false in general)
```

Active modules: ~918 lines. Total including deprecated: 1,257 lines (+ 25 lines Papers.lean).

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
- Paper 57: Complete class-number-1 landscape for exotic Weil self-intersection -- This paper

## License

Apache 2.0 (code) / CC-BY 4.0 (paper).
