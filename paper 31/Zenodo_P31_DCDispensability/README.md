# Paper 31: The Physical Dispensability of Dependent Choice

**Paper 31 in the Constructive Reverse Mathematics Series**

Paul Chun-Kit Lee (dr.paul.c.lee@gmail.com), February 2026

## Overview

This paper establishes that every empirically accessible prediction from Dependent
Choice (DC) --- including Birkhoff's Pointwise Ergodic Theorem and the Strong Law
of Large Numbers --- is recoverable in BISH+LPO without invoking DC.

The core mathematical insight: DC's content reduces to a quantifier swap (moving
the universal quantifier inside vs. outside a measure), which has no empirical
manifestation since experiments operate with quantifiers outside the measure.

Together with Papers 29 and 30, this completes the argument that the logical
constitution of empirically accessible physics is BISH+LPO --- one axiom beyond
Bishop's constructive mathematics.

## Main Results

| Theorem | Statement | Level |
|---------|-----------|-------|
| `chebyshev_wlln_bound` | WLLN bound via Chebyshev | BISH (zero axioms) |
| `met_empirical_bound` | MET provides empirical convergence | LPO (via CC) |
| `slln_empirical_content_is_wlln` | WLLN captures all empirical SLLN predictions | -- |
| `met_implies_empirical` | MET provides all empirical Birkhoff predictions | -- |
| `dc_physically_dispensable` | DC is physically dispensable | LPO |
| `bish_lpo_empirically_complete` | Master theorem: BISH+LPO suffices | LPO |

## The Quantifier Swap

DC's mathematical content in this context is the swap:

- **Empirical (WLLN/MET):** For all epsilon, delta > 0, there exists N such that
  P({|error| >= epsilon}) < delta
- **Ontological (SLLN/Birkhoff):** P({omega | for all epsilon > 0, there exists N
  such that for all n >= N, |error(n,omega)| < epsilon}) = 1

Since experimenters must choose (epsilon, delta) before observing outcomes, physical
measurements operate with quantifiers outside the measure. The swap is empirically
void.

## Three-Paper Arc (Papers 29-31)

| Paper | Result | Mechanism |
|-------|--------|-----------|
| 29 | LPO is physically real | Fekete <-> LPO; phase transitions exist |
| 30 | FT is dispensable | Approximate EVT from BMC, not FT |
| 31 | DC is dispensable | WLLN/MET from CC, not SLLN/Birkhoff |

## How to Open and Build

### LaTeX Paper

The compiled PDF is included (`paper31.pdf`). To recompile:

```bash
pdflatex paper31.tex
pdflatex paper31.tex
```

### Lean 4 Formalization

**Prerequisites:** Install [elan](https://github.com/leanprover/elan) (Lean version
manager) and ensure `lake` is available. Requires ~8 GB disk space for Mathlib cache.

```bash
cd P31_DCDispensability
lake exe cache get       # downloads prebuilt Mathlib (~5 min)
lake build               # compiles Paper 31 source files (~2-5 min)
```

A successful build produces 0 errors, 0 warnings, and 0 sorries.

## Axiom Audit

All theorems have axiom profile `[propext, Classical.choice, Quot.sound]` plus
explicitly cited literature axioms. `Classical.choice` is a Lean metatheory axiom from
Mathlib's real number construction --- not an object-level non-constructive principle.

| Axiom | Citation |
|-------|----------|
| `cc_of_lpo` | Ishihara (2006) |
| `slln_implies_wlln` | Standard probability theory |
| `birkhoff_implies_met` | Standard ergodic theory |
| `met_markov_composition` | MET + Markov's inequality -> probability bound |
| `ontological_implies_empirical` | Almost-sure -> in probability |

**Fully proved (zero custom axioms):**
- `chebyshev_wlln_bound` --- pure arithmetic, no choice needed
- `met_empirical_bound` --- pure filter extraction, no choice needed

**Zero sorry.**

## Contents

```
README.md                              This file
paper31.tex                            LaTeX source
paper31.pdf                            Compiled paper
P31_DCDispensability/                  Lean 4 formalization
  lakefile.lean                        Package configuration
  lean-toolchain                       leanprover/lean4:v4.28.0-rc1
  lake-manifest.json                   Dependency lock file
  Papers.lean                          Root import
  Papers/P31_DCDispensability/
    Defs.lean             153 lines    LPO, CC, DC, WLLN, SLLN, MET, Birkhoff
    WLLN.lean             129 lines    Chebyshev WLLN bound (BISH)
    Ergodic.lean          133 lines    MET empirical bound, Birkhoff gap
    Dispensability.lean   182 lines    DC dispensability, quantifier swap
    Main.lean             107 lines    Master theorem + axiom audit
```

5 Lean source files, 704 lines total.

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
- Paper 31: Physical dispensability of Dependent Choice -- This paper

## License

Apache 2.0 (code) / CC-BY 4.0 (paper).
