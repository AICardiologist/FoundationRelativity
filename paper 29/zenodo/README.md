# Paper 29: Fekete's Subadditive Lemma is Equivalent to LPO

**Paper 29 in the Constructive Reverse Mathematics Series**

Paul Chun-Kit Lee (dr.paul.c.lee@gmail.com), February 2026

DOI: [10.5281/zenodo.18632776](https://doi.org/10.5281/zenodo.18632776)

## Overview

This Lean 4 formalization proves that Fekete's Subadditive Lemma --- the assertion
that every subadditive sequence with u(n)/n bounded below converges --- is
**equivalent to the Limited Principle of Omniscience (LPO)** over Bishop-style
constructive mathematics (BISH).

The equivalence is established in two directions:

- **Backward direction (fully proved)**: `FeketeConvergence -> LPO`. Given any
  binary sequence alpha, encode it into a mock free energy F_n = -n * x_n where
  x_n = 1 iff exists k < n, alpha(k) = true. This F is subadditive with
  F_n/n >= -1. Applying Fekete's lemma and evaluating at a sufficiently large
  truncation decides LPO.

- **Forward direction (axiomatized)**: `LPO -> FeketeConvergence`. Composes two
  literature results: LPO implies the Bolzano-Cauchy property of the reals
  (Bridges-Vita 2006, Theorem 2.1.5), and the Bolzano-Cauchy property implies
  Fekete convergence (classical Fekete proof, available in Mathlib as
  `Subadditive.tendsto_lim`).

## Main Results

| Theorem | Statement | Status |
|---------|-----------|--------|
| `lpo_of_fekete` | FeketeConvergence -> LPO | Fully proved (zero sorry) |
| `fekete_of_lpo` | LPO -> FeketeConvergence | Axiomatized (two cited results) |
| `fekete_iff_lpo` | FeketeConvergence <-> LPO | Equivalence |

## Physical Significance

This result establishes a three-tier hierarchy for thermodynamic-limit convergence:

| Route | Logical cost | Example |
|-------|-------------|---------|
| Exact solution (closed-form modulus) | BISH | 1D Ising (Papers 8, 9) |
| Cluster expansion (exponential decay) | BISH | High-temperature lattice gases |
| Generic subadditivity (Fekete) | LPO | This paper |

The LPO cost becomes ineliminable when explicit finite-size bounds are
unavailable --- typically near phase transitions where correlation lengths diverge.
This resolves Paper 10's Open Problem 1 on whether LPO-equivalence is specific to
the 1D Ising encoding or generic to subadditivity.

## How to Open and Build

### LaTeX Paper

The compiled PDF is included (`paper29_fekete_lpo.pdf`). To recompile:

```bash
pdflatex paper29_fekete_lpo.tex
pdflatex paper29_fekete_lpo.tex
```

### Lean 4 Formalization

**Prerequisites:** Install [elan](https://github.com/leanprover/elan) (Lean version
manager) and ensure `lake` is available. Requires ~8 GB disk space for Mathlib cache.

```bash
cd P29_FeketeLPO
lake exe cache get       # downloads prebuilt Mathlib (~5 min)
lake build               # compiles Paper 29 source files (~2-5 min)
```

A successful build produces 0 errors, 0 warnings, and 0 sorries.

### Verify Axiom Profile

After building, the axiom audits in `Main.lean` produce:

```lean
-- Backward direction (no custom axioms):
#print axioms Papers.P29.lpo_of_fekete
-- [propext, Classical.choice, Quot.sound]

-- Full equivalence (two cited axioms):
#print axioms Papers.P29.fekete_iff_lpo
-- [propext, Classical.choice, Quot.sound, Papers.P29.bmc_of_lpo, Papers.P29.fekete_of_bmc]
```

## Axiom Audit

All theorems have axiom profile `[propext, Classical.choice, Quot.sound]` plus, for
the forward direction, two explicitly cited literature axioms. `Classical.choice` is
a Lean metatheory axiom from Mathlib's real number construction (classical Cauchy
completion) --- not an object-level non-constructive principle.

| Axiom | Citation |
|-------|----------|
| `bmc_of_lpo` | Bridges and Vita, *Techniques of Constructive Analysis* (2006), Theorem 2.1.5 |
| `fekete_of_bmc` | Classical Fekete proof; available in Mathlib as `Subadditive.tendsto_lim` |

**Zero custom axioms in the backward direction. Zero sorry.**

## Contents

```
README.md                              This file
paper29_fekete_lpo.tex                 LaTeX source
paper29_fekete_lpo.pdf                 Compiled paper
P29_FeketeLPO/                         Lean 4 formalization
  lakefile.lean                        Package configuration
  lean-toolchain                       leanprover/lean4:v4.28.0-rc1
  lake-manifest.json                   Dependency lock file
  Papers.lean                          Root import
  Papers/P29_FeketeLPO/
    Defs.lean              87 lines    Core definitions: LPO, BMC, FeketeConvergence, encoding
    Indicator.lean        118 lines    hasTrue/indicator properties: monotonicity, witnesses
    Subadditive.lean      103 lines    Subadditivity + lower bound proofs
    Decision.lean         117 lines    Main theorem: FeketeConvergence -> LPO
    Forward.lean           43 lines    Axiomatized: LPO -> BMC -> FeketeConvergence
    Main.lean              81 lines    Assembly: FeketeConvergence <-> LPO + axiom audit
```

6 Lean source files, 549 lines total.

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
- Paper 29: Fekete's Subadditive Lemma and LPO -- This paper

## License

Apache 2.0 (code) / CC-BY 4.0 (paper).
