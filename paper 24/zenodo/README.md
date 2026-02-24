# Paper 24: LLPO Equivalence via Kochen-Specker Contextuality

**The Constructive Cost of Single-System No-Go Theorems**

Paper 24 in the Constructive Reverse Mathematics Series
Paul C.-K. Lee (NYU), February 2026

DOI: 10.5281/zenodo.18604317

## Overview

This Lean 4 formalization establishes that Kochen-Specker contextuality has the same
constructive cost (LLPO) as Bell nonlocality (Paper 21), despite being a physically
distinct phenomenon. The KS sign decision -- the assertion that at least one measurement
context lacks predetermined values -- is equivalent to LLPO over BISH.

This is the second LLPO calibration in the series, confirming the structural identity
between Bell nonlocality and KS contextuality.

## Main Results

| Theorem | Statement |
|---------|-----------|
| `cega_uncolorable` | The CEGA 18-vector KS graph is uncolorable (BISH) |
| `llpo_iff_ks_sign` | LLPO <-> KSSignDecision |
| `ks_stratification` | Three-level: (BISH) uncolorability, (LLPO <-> KSSignDecision), (WLPO -> LLPO) |

## Structural Finding

Two physically distinct quantum no-go theorems share identical logical cost:

| Phenomenon | Physics | Logical Cost | Paper |
|------------|---------|-------------|-------|
| Bell nonlocality | Spatially separated systems | LLPO | 21 |
| KS contextuality | Single-system measurements | LLPO | 24 |

CRM reveals that Bell nonlocality and KS contextuality are the same logical
phenomenon -- "disjunction without constructive witness" -- in different physical clothing.

## How to Open and Build

### LaTeX Paper

The compiled PDF is included (`paper24_writeup.pdf`). To recompile from source:

```bash
pdflatex paper24_writeup
bibtex paper24_writeup
pdflatex paper24_writeup
pdflatex paper24_writeup
```

### Lean 4 Formalization

**Prerequisites:** Install [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) (version 4.28.0-rc1) and ensure `lake` is available.

```bash
cd P24_KochenSpecker
lake build    # Downloads Mathlib, then builds (0 errors, 0 warnings, 0 sorry)
```

The first build may take 30-60 minutes to download and compile Mathlib dependencies.
Subsequent builds are fast (seconds). The `native_decide` proof (Uncolorability.lean)
requires compiled Lean and completes in ~4 seconds over 2^18 = 262,144 candidate colorings.

To explore interactively, open the `P24_KochenSpecker` folder in VS Code with the
Lean 4 extension installed.

## Axiom Audit

**ONE custom axiom:** `llpo_real_of_llpo` (LLPO -> real sign decision).

This is the standard constructive equivalence (Ishihara 2006, Bridges-Richman 1987),
identical to Paper 21's axiom profile -- confirming the structural identity of Bell
and KS logical costs.

Additionally, `Lean.ofReduceBool` and `Lean.trustCompiler` appear from `native_decide`
-- these are Lean kernel axioms, not custom mathematical axioms.

## Contents

```
README.md                              This file
paper24_writeup.tex                    LaTeX source (~1577 lines)
paper24_writeup.pdf                    Compiled paper (~20 pages)
paper24_references.bib                 Bibliography (~275 lines)
paper24_kochen_specker_llpo_proof.md   Proof specification (883 lines)
P24_KochenSpecker/                     Lean 4 formalization
  lakefile.lean                        Package configuration
  lean-toolchain                       leanprover/lean4:v4.28.0-rc1
  Papers.lean                          Root import
  lake-manifest.json                   Dependency lock file
  README.md                            Lean project documentation
  Papers/P24_KochenSpecker/
    Defs/
      KSGraph.lean                     KS graph structure and coloring definitions
      CEGAData.lean                    CEGA 18-vector graph (9 contexts)
      LLPO.lean                        LLPO, LPO, WLPO definitions and hierarchy
      EncodedAsymmetry.lean            Geometric series encoding, KSSignDecision
    PartA/
      Uncolorability.lean              cega_uncolorable (by native_decide)
      FiniteSearch.lean                Finite context witness extraction
      PartA_Main.lean                  Part A summary
    PartB/
      SignIff.lean                     Sign-iff lemmas (under AtMostOne)
      Forward.lean                     LLPO -> KSSignDecision
      Backward.lean                    KSSignDecision -> LLPO (novel direction)
      PartB_Main.lean                  llpo_iff_ks_sign
    Main/
      Stratification.lean              ks_stratification (three-level)
      AxiomAudit.lean                  Comprehensive #print axioms
    Main.lean                          Root imports
```

16 Lean files, ~887 lines total.

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
- Paper 10: Logical geography of mathematical physics -- DOI: 10.5281/zenodo.18580342 [v 2.0 Technical Synthesis of Papers 1-16]
- Paper 11: Entanglement, CHSH, Tsirelson bound -- DOI: 10.5281/zenodo.18527676
- Paper 12: Constructive history of mathematical physics -- DOI: 10.5281/zenodo.18581707 [v 2.0 Historical Synthesis of Papers 1-16]
- Paper 13: Event horizon as logical boundary -- DOI: 10.5281/zenodo.18529007
- Paper 14: Quantum decoherence -- DOI: 10.5281/zenodo.18569068
- Paper 15: Noether theorem -- DOI: 10.5281/zenodo.18572494
- Paper 16: Technical note: Born rule -- DOI: 10.5281/zenodo.18575377
- Paper 17: Bekenstein-Hawking formula -- DOI: 10.5281/zenodo.18597306
- Paper 18: Fermion mass hierarchy and scaffolding principle -- DOI: 10.5281/zenodo.18600243
- Paper 19: WKB tunneling and LLPO -- DOI: 10.5281/zenodo.18602596
- Paper 20: Observable-dependent logical cost, 1D Ising magnetization and WLPO -- DOI: 10.5281/zenodo.18603079
- Paper 21: Bell nonlocality and LLPO -- DOI: 10.5281/zenodo.18603251
- Paper 22: Markov's Principle and radioactive decay -- DOI: 10.5281/zenodo.18603503
- Paper 23: Fan Theorem and optimization -- DOI: 10.5281/zenodo.18604312
- Paper 24: Kochen-Specker contextuality and LLPO -- DOI: 10.5281/zenodo.18604317

## License

This work is part of the Constructive Reverse Mathematics series.
