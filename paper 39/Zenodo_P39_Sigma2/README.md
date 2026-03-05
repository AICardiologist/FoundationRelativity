# Paper 39: Physics Reaches Sigma-2-zero --- The Physical Stratification of Undecidability

**Paper 39 in the Constructive Reverse Mathematics Series**

Paul Chun-Kit Lee (dr.paul.c.lee@gmail.com), February 2026

## Overview

While Papers 36--38 showed all known physical undecidabilities are LPO (Sigma-1-zero),
this paper proves the ceiling is NOT Sigma-1-zero. A modified Cubitt encoding ---
running a Turing machine on all inputs simultaneously via Robinson tiling with
perimeter counters --- encodes the Sigma-2-zero-complete Finiteness Problem into the spectral gap.

The Physical Stratification Theorem shows: the arithmetic complexity of a physical
observable is determined by its epistemic mode (exact vs promise-gapped vs empirical),
NOT by its thermodynamic scaling (extensive vs intensive):

- **Platonic exact physics** (no promise gap): LPO_jump (Sigma-2-zero)
- **Promise-gapped physics** (Cubitt promise): LPO (Sigma-1-zero)
- **Empirical physics** (finite precision): LPO (Sigma-1-zero)

**v2 erratum:** v1 incorrectly claimed extensive observables cap at LPO.
Counterexample: x_n = 1/n is decreasing with all terms positive but limit 0.
The exact zero-test for ANY decreasing non-negative sequence is Sigma-2-zero,
requiring LPO_jump. The promise gap (not thermodynamic scaling) is what
collapses Sigma-2-zero to Sigma-1-zero. Also fixed: LPO_jump definition
corrected from Bool to Prop (Bool made oracle premise a tautology).

## Main Results

| Theorem | Statement | Level |
|---------|-----------|-------|
| A `modified_hamiltonian` | Modified Cubitt encoding: gapped iff finite halting set | axiom |
| B `generic_gap_iff_lpo_jump` | Generic spectral gap (no promise) iff LPO_jump | LPO_jump |
| C `promise_gapped_caps_at_lpo` | Promise-gapped physics caps at LPO | LPO |
| D `exact_zero_test_iff_lpo_jump` | Exact zero-test for decreasing sequences iff LPO_jump | LPO_jump |
| E `physical_stratification` | Master: epistemic mode determines arithmetic level | -- |

## Axiom Inventory

Custom bridge axioms (13 load-bearing + 1 documentary):

| Axiom | Purpose | Load-bearing? |
|-------|---------|:---:|
| `halting_seq` | TM step function | Yes |
| `halts_within` | Bounded halting predicate | Yes |
| `halts_within_decidable` | Bounded halting is BISH | Yes |
| `tm_from_seq`, `tm_from_seq_halts` | TM encoding from binary sequences | Yes |
| `modified_hamiltonian` | Cubitt encoding M -> H*(M) | Yes |
| `is_gapped`, `is_gapless`, `gapped_iff_not_gapless` | Spectral gap properties | Yes |
| `modified_gapped_iff_finite` | Gapped iff finite halting set | Yes |
| `modified_gapless_iff_infinite` | Gapless iff infinite halting set | Yes |
| `finiteness_is_sigma2_complete` | FIN is Sigma-2-zero-complete | Yes |
| `bmc_from_subadditive` | Fekete/BMC limit existence (LPO) | Yes |
| `exact_zero_test_requires_lpo_jump` | Zero-test implies LPO_jump | Yes |
| `lpo_jump_decides_exact_zero_test` | LPO_jump implies zero-test | Yes |
| `promise_gap_sigma1_test`, `empirical_gap_sigma1` | Promise/empirical cap | Yes |
| `gap_less_than` | Empirical gap comparison | Documentary |

Plus Lean infrastructure: `propext`, `Classical.choice`, `Quot.sound`.

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
paper39.pdf                              Compiled paper (14 pages)
zenodo_metadata.txt                      Zenodo upload metadata
P39_Sigma2/                              Lean 4 formalization
  lakefile.lean                          Package configuration
  lean-toolchain                         leanprover/lean4:v4.28.0-rc1
  Papers.lean                            Root import
  Papers/P39_Sigma2/
    Defs.lean                            LPO_jump, DecreasingSeqWithLimit, zero-test defs
    ArithmeticHierarchy.lean             Sigma-2/Pi-2 characterization
    ModifiedEncoding.lean                Robinson tiling + perimeter counters
    GenericGapSigma2.lean                Generic gap is Sigma-2-complete
    ExtensiveCeiling.lean                Exact zero-test theorem (Sigma-2)
    PromiseGapRecovery.lean              Promise gap recovery to LPO
    Stratification.lean                  Physical stratification theorem
    Main.lean                            Master theorem + axiom audit
archive/                                 Pre-fix versions (v1, v2 intermediate)
```

873 lines Lean 4 across 8 source files.

## Dependencies

- Papers 29 (Fekete/BMC = LPO), 36-38 (Cubitt stratification, Wang tiling)
- Cubitt-Perez-Garcia-Wolf (2015), Bausch-Cubitt-Ozols (2018)
- Rogers (1967) for Sigma-2-zero-completeness of Finiteness Problem
- Brattka-Gherardi-Pauly (2012) for Weihrauch degree framework

## License

Apache 2.0 (code) / CC-BY 4.0 (paper).
