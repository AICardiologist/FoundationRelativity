# Paper 58: Class Number Correction for Exotic Weil Classes on CM Abelian Fourfolds

**Paper 58 in the Constructive Reverse Mathematics Series**

Paul Chun-Kit Lee (dr.paul.c.lee@gmail.com), February 2026

DOI: [10.5281/zenodo.18734718](https://doi.org/10.5281/zenodo.18734718)

## Overview

Papers 56--57 established the formula h = f for the Hermitian self-intersection of
exotic Weil classes on CM abelian fourfolds, where f is the conductor of the cyclic
Galois totally real cubic and h_K = 1. This paper extends to h_K > 1.

The corrected formula is:

    h * Nm(a) = f

where a is the Steinitz class of the integral Weil lattice, uniquely determined by
the norm condition h = f/Nm(a) in Nm(K^x). The topological volume det(G) = f^2 |D_K|
is an absolute geometric invariant; the class group redistributes it between the
Hermitian metric h and the lattice density Nm(a).

**Test field:** K = Q(sqrt(-5)), h_K = 2, |D_K| = 20.

**Key results:**
- 4 of 9 conductors split in K: f = 7 (non-free), 9 (free), 61 (free), 163 (non-free)
- 5 conductors are inert: f = 13, 19, 37, 79, 97
- Steinitz class forced by decidable norm obstruction (mod-5 infinite descent)
- All Gram matrix determinants verified by `native_decide`

## Main Results

| Theorem | Statement |
|---------|-----------|
| `paper58_summary_K5` | 9 conductors: 4 split, 5 inert, all verified |
| `gramFree_det` | Free template: det(!![2f,0;0,10f]) = 20f^2 |
| `gramNonFree_det` | Non-free template: det(!![4f,2f;2f,6f]) = 20f^2 |
| `gram_volume_invariant` | Both templates give det = f^2 * |D_K| |
| `not_rational_norm_mod5` | For f = 2,3 mod 5: x^2 + 5y^2 = fz^2 has no nonzero solution |
| `seven_not_rational_norm_K5` | 7 is not a rational norm in Q(sqrt(-5))^x |
| `onesixtythree_not_rational_norm_K5` | 163 is not a rational norm in Q(sqrt(-5))^x |
| `nine_is_norm_K5` | 9 = 2^2 + 5*1^2 (free witness) |
| `sixtyone_is_norm_K5` | 61 = 4^2 + 5*3^2 (free witness) |
| `seven_half_is_norm_K5` | 7*2 = 3^2 + 5*1^2 (non-free witness) |
| `onesixtythree_half_is_norm_K5` | 163*2 = 9^2 + 5*7^2 (non-free witness) |
| `steinitz_forced_nontrivial_K5_f7` | f=7: free blocked, non-free works |
| `steinitz_forced_nontrivial_K5_f163` | f=163: free blocked, non-free works |

## Conductor Classification

| f | Split? | Steinitz | Nm(a) | h | det(G) | f^2 * 20 |
|---|--------|----------|-------|---|--------|----------|
| 7 | Yes | non-free | 2 | 7/2 | 980 | 980 |
| 9 | Yes | free | 1 | 9 | 1620 | 1620 |
| 13 | No | inert | -- | -- | -- | 3380 |
| 19 | No | inert | -- | -- | -- | 7220 |
| 37 | No | inert | -- | -- | -- | 27380 |
| 61 | Yes | free | 1 | 61 | 74420 | 74420 |
| 79 | No | inert | -- | -- | -- | 124820 |
| 97 | No | inert | -- | -- | -- | 188180 |
| 163 | Yes | non-free | 2 | 163/2 | 531380 | 531380 |

## How to Open and Build

### LaTeX Paper

The compiled PDF is included (`paper58.pdf`). To recompile:

```bash
pdflatex paper58.tex
pdflatex paper58.tex
```

### Lean 4 Formalization

**Prerequisites:** Install [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) (version 4.29.0-rc1) and ensure `lake` is available.

```bash
cd P58_ClassNumber
lake exe cache get && lake build
```

The first build may take 30-60 minutes to download and compile Mathlib dependencies.
Subsequent builds are fast. Build status: **0 errors, 0 warnings**.

To explore interactively, open the `P58_ClassNumber` folder in VS Code with the
Lean 4 extension installed.

## Axiom Audit

All theorems have axiom profile `[propext, Classical.choice, Quot.sound]`.
`Classical.choice` is a Lean metatheory axiom from Mathlib's real number construction
(classical Cauchy completion) --- not an object-level non-constructive principle.

The constructive content is established by proof structure:

- **Norm witnesses** (`nine_is_norm_K5`, `sixtyone_is_norm_K5`, etc.): depend only
  on `propext` --- purely constructive explicit witnesses.
- **Norm obstruction** (`not_rational_norm_mod5`): uses infinite descent on |z|,
  with ZMod 5 arithmetic verified by `decide`. Classical.choice from ZMod infrastructure.
- **Gram determinants**: verified by `native_decide` on concrete 2x2 integer matrices.
- **Inert classification**: verified by `decide` on ZMod f for each conductor.

**Zero custom axioms. Zero sorry.**

## Contents

```
README.md                              This file
paper58.tex                            LaTeX source (revised, Paper 45 format)
paper58.pdf                            Compiled paper (9 pages)
REPRODUCIBILITY.md                     Reproducibility guide
P58_ClassNumber/                       Lean 4 formalization
  lakefile.lean                        Package configuration
  lean-toolchain                       leanprover/lean4:v4.29.0-rc1
  lake-manifest.json                   Dependency lock file
  Papers.lean                          Root import
  Papers/P58_ClassNumber/
    Defs.lean             109 lines    Core structures and K = Q(sqrt(-5))
    GramMatrix.lean       118 lines    Gram templates and per-conductor matrices
    NormObstruction.lean  234 lines    Mod-5 descent, norm witnesses, inert/split
    ClassNumberExamples.lean 178 lines WeilLatticeData for all 9 conductors
    Completeness.lean      82 lines    Summary theorem and universal verification
    Main.lean              78 lines    Root module and axiom audit
```

6 Lean source files, 799 lines total.

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
- Paper 58: Class number correction for exotic Weil classes -- This paper

## License

This work is part of the Constructive Reverse Mathematics series.
