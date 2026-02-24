# Paper 39: Beyond LPO --- The Thermodynamic Stratification of Physical Undecidability

**Paper 39 in the Constructive Reverse Mathematics Series**

Paul Chun-Kit Lee (dr.paul.c.lee@gmail.com), February 2026

## Overview

While Papers 36-38 showed all known undecidabilities are LPO (Sigma-1-zero),
this paper proves the ceiling is NOT Sigma-1-zero. A modified Cubitt encoding ---
running a Turing machine on all inputs simultaneously via Robinson tiling with
perimeter counters --- encodes the Sigma-2-zero-complete Finiteness Problem.

The Thermodynamic Stratification Theorem shows: extensive observables (energy
density, magnetization) cap at LPO via Fekete's lemma, while intensive
observables (spectral gap) reach LPO-prime (Turing jump of LPO). Empirical
physics (finite precision) remains capped at LPO.

## Main Results

| Theorem | Statement | Level |
|---------|-----------|-------|
| `generic_gap_sigma2_complete` | Generic spectral gap is Sigma-2-zero-complete | LPO' |
| `extensive_ceiling_lpo` | Extensive observables cap at LPO | LPO |
| `thermodynamic_stratification` | Complexity bifurcates on thermodynamic scaling | -- |
| `promise_gap_lpo` | Promise-gapped physics caps at LPO | LPO |

## How to Open and Build

### LaTeX Paper

The compiled PDF is included (`paper39.pdf`). To recompile:

```bash
pdflatex paper39.tex
pdflatex paper39.tex
```

### Lean 4 Formalization

**Prerequisites:** Install [elan](https://github.com/leanprover/elan) (Lean version
manager) and ensure `lake` is available. Requires ~8 GB disk space for Mathlib cache.

```bash
cd P39_Sigma2
lake exe cache get       # downloads prebuilt Mathlib (~5 min)
lake build               # compiles Paper 39 source files (~2-5 min)
```

A successful build produces 0 errors, 0 warnings, and 0 sorries.

## Contents

```
README.md                                This file
paper39.tex                              LaTeX source
paper39.pdf                              Compiled paper
P39_Sigma2/                              Lean 4 formalization
  lakefile.lean                          Package configuration
  lean-toolchain                         leanprover/lean4:v4.28.0-rc1
  Papers.lean                            Root import
  Papers/P39_Sigma2/
    Defs.lean                            Arithmetic hierarchy, LPO' definitions
    ArithmeticHierarchy.lean             Sigma-2/Pi-2 characterization
    ModifiedEncoding.lean                Robinson tiling + perimeter counters
    GenericGapSigma2.lean                Generic gap is Sigma-2-complete
    ExtensiveCeiling.lean                Extensive observables cap at LPO
    PromiseGapRecovery.lean              Promise gap recovery to LPO
    Stratification.lean                  Thermodynamic stratification theorem
    Main.lean                            Master theorem
```

8 Lean source files.

## License

Apache 2.0 (code) / CC-BY 4.0 (paper).
