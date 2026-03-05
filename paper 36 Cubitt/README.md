# Paper 36: Stratifying Spectral Gap Undecidability (Cubitt's Theorem Is LPO)

**Paper 36 in the Constructive Reverse Mathematics Series**

Paul Chun-Kit Lee (dr.paul.c.lee@gmail.com), February 2026

DOI: [10.5281/zenodo.18642620](https://doi.org/10.5281/zenodo.18642620)

## Overview

Cubitt, Perez-Garcia and Wolf (2015) proved that determining whether a many-body
Hamiltonian is gapped or gapless is undecidable. This paper stratifies their
result through the constructive hierarchy and establishes that Cubitt's
undecidability is Turing-Weihrauch equivalent to LPO over BISH.

The key insight: macroscopic quantum undecidability costs exactly one
thermodynamic limit. The same LPO that is already required for phase transitions
(Paper 29), running coupling constants (Paper 32), and the continuum limit
(Paper 33) also decides the spectral gap.

## Main Results

| Theorem | Statement | Level |
|---------|-----------|-------|
| `finite_volume_gap_is_bish` | Finite-volume spectral gap is computable | BISH |
| `thermo_limit_iff_lpo` | Thermodynamic limit <-> LPO | LPO |
| `pointwise_gap_decidable` | Each instance decidable given LPO | LPO |
| `physical_gap_zero_test_iff_wlpo` | Gap zero-test <-> WLPO | WLPO |
| `gap_function_not_computable` | Uniform gap function is not computable | -- |
| `cubitt_is_lpo` | Uniform decidability <-> LPO | LPO |
| `stratification_theorem` | Master theorem: complete stratification | LPO |

## CRM Classification

| Feature | Logical cost | Why |
|---------|-------------|-----|
| Finite-volume gap | BISH | Finite-dimensional eigenvalue |
| Thermodynamic limit | LPO | BMC for sequence of gaps |
| Pointwise decidability | LPO | Instance-by-instance |
| Gap zero-test (Delta = 0 v Delta != 0) | WLPO | Negative disjunct; subsumed by LPO |
| Uniform decidability | LPO | Halting reduction |
| Not computable (without oracle) | -- | Halting problem |

**Note on WLPO formulation:** The zero-test uses the negative disjunct
Delta != 0 (not Delta > 0). The positive formulation Delta = 0 v Delta > 0
would be LPO, not WLPO. Upgrading Delta != 0 to Delta > 0 requires
Markov's Principle, and WLPO + MP = LPO.

## How to Open and Build

### LaTeX Paper

The compiled PDF is included (`paper36.pdf`). To recompile:

```bash
pdflatex paper36.tex
pdflatex paper36.tex
```

### Lean 4 Formalization

**Prerequisites:** Install [elan](https://github.com/leanprover/elan) (Lean version
manager) and ensure `lake` is available. Requires ~8 GB disk space for Mathlib cache.

```bash
cd P36_CubittStratification
lake exe cache get       # downloads prebuilt Mathlib (~5 min)
lake build               # compiles Paper 36 source files (~2-5 min)
```

A successful build produces 0 errors, 0 warnings, and 0 sorries.

## Axiom Audit

All theorems have axiom profile `[propext, Classical.choice, Quot.sound]` plus
explicitly cited axioms. `Classical.choice` is a Lean metatheory axiom from
Mathlib's real number construction --- not an object-level non-constructive principle.

**Bridge lemmas (axiomatized physics from CPgW):**

| Axiom | Content |
|-------|---------|
| `cpgw_encoding_computable` | M -> H(M) is computable |
| `cpgw_gapped_of_not_halts` | not halts -> gap > 0 |
| `cpgw_gapless_of_halts` | halts -> gap = 0 |
| `cpgw_halting_asymptotics` | Halting case convergence |
| `cpgw_nonhalting_asymptotics` | Non-halting case convergence |
| `cpgw_gap_dichotomy` | Gap in {0} U [gamma, infinity) |
| `cpgw_finite_gap_computable` | Finite-volume eigenvalue computation |
| `tm_from_seq` / `tm_from_seq_halts` | Sequence-to-TM encoding |

**Constructive principles:**

| Axiom | Citation |
|-------|----------|
| `bmc_of_lpo` | Bridges and Vita (2006), Theorem 2.1.5 |
| `wlpo_of_lpo` | Standard CRM hierarchy |
| `halting_problem_undecidable` | Turing (1936) |
| `wlpo_to_zero_test` / `zero_test_to_wlpo` | WLPO <-> zero-test (negative formulation) |

**Zero sorry.**

## Contents

```
README.md                              This file
paper36.tex                            LaTeX source
paper36.pdf                            Compiled paper
P36_CubittStratification/              Lean 4 formalization
  lakefile.lean                        Package configuration
  lean-toolchain                       leanprover/lean4:v4.28.0-rc1
  lake-manifest.json                   Dependency lock file
  Papers.lean                          Root import
  Papers/P36_CubittStratification/
    Defs.lean              80 lines    TM, LPO, WLPO, spectral gap, thermo limit
    BridgeLemmas.lean     100 lines    CPgW bridge axioms
    FiniteGap.lean         50 lines    Theorem 1: finite-volume gap (BISH)
    ThermoLimit.lean      102 lines    Theorem 2: thermo limit <-> LPO
    Pointwise.lean         50 lines    Theorem 3: pointwise decidability (LPO)
    ZeroTest.lean          73 lines    Theorem 4: gap zero-test <-> WLPO
    UniformDecidability.lean 113 lines Theorem 5: uniform decidability <-> LPO
    Main.lean              99 lines    Master theorem + axiom audit
```

8 Lean source files, 667 lines total.

## License

Apache 2.0 (code) / CC-BY 4.0 (paper).
