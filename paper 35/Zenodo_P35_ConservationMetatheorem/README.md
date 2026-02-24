# Paper 35: The Logical Constitution of Empirical Physics --- A Conservation Metatheorem

**Paper 35 in the Constructive Reverse Mathematics Series**

Paul Chun-Kit Lee (dr.paul.c.lee@gmail.com), February 2026

## Overview

This paper proves the Conservation Metatheorem: the logical constitution of
empirically accessible physics is BISH+LPO. This is a structural consequence of
two facts:

1. **Theorem A (BISH Conservation):** Empirical predictions are finite compositions
   of computable functions at computable inputs --- they remain in BISH.
2. **Theorem B (Limit Boundary):** The only idealizations that increase logical
   cost are completed limits:
   - With an explicit Cauchy modulus: BISH (no cost)
   - Without modulus (bounded monotone): LPO (via BMC)
   - Equality decisions on limits: WLPO (subsumed by LPO)

The metatheorem is validated by **Theorem C (Exhaustiveness):** all 38 calibration
entries across Papers 2--34 are at or below LPO. **Theorem D** shows the three
mechanisms (BMC, Cauchy completeness, bounded supremum existence) are equivalent
to each other and to LPO.

## Main Results

| Theorem | Statement | Level |
|---------|-----------|-------|
| `bish_conservation` | Finite compositions preserve BISH | BISH |
| `limit_with_modulus_is_bish` | Modulus → BISH (no cost) | BISH |
| `bounded_monotone_limit_requires_lpo` | No modulus → LPO via BMC | LPO |
| `lpo_subsumes_all` | LPO → WLPO ∧ LLPO | LPO |
| `no_entry_exceeds_lpo` | All 38 calibrations ≤ LPO | -- |
| `mechanism_equivalence` | BMC ↔ Cauchy ↔ Sup | -- |
| `conservation_metatheorem` | Master theorem | LPO |

## The Four Theorems

| Theorem | Content | Level |
|---------|---------|-------|
| A | Finite compositions of computable functions at computable inputs are BISH | BISH |
| B1 | Limit with modulus → BISH | BISH |
| B2 | Bounded monotone limit without modulus → LPO | LPO |
| B3 | Limit equality decision → WLPO ⊆ LPO | WLPO |
| C | All 38 calibration entries are ≤ LPO | -- |
| D | Three LPO mechanisms are equivalent | -- |

## How to Open and Build

### LaTeX Paper

The compiled PDF is included (`paper35.pdf`). To recompile:

```bash
pdflatex paper35.tex
pdflatex paper35.tex
```

### Lean 4 Formalization

**Prerequisites:** Install [elan](https://github.com/leanprover/elan) (Lean version
manager) and ensure `lake` is available. Requires ~8 GB disk space for Mathlib cache.

```bash
cd P35_ConservationMetatheorem
lake exe cache get       # downloads prebuilt Mathlib (~5 min)
lake build               # compiles Paper 35 source files (~2-5 min)
```

A successful build produces 0 errors, 0 warnings, and 0 sorries.

## Axiom Audit

All theorems have axiom profile `[propext, Classical.choice, Quot.sound]` plus
explicitly cited axioms. `Classical.choice` is a Lean metatheory axiom from
Mathlib's real number construction --- not an object-level non-constructive principle.

| Axiom | Citation |
|-------|----------|
| `bmc_of_lpo` | Bridges and Vita, *Techniques of Constructive Analysis* (2006), Theorem 2.1.5 |
| `lpo_of_bmc` | BMC → LPO (reverse direction for Theorem D) |
| `wlpo_of_lpo` | Standard CRM hierarchy |
| `llpo_of_wlpo` | Standard CRM hierarchy |
| `bmc_implies_cauchy_complete` | Mechanism equivalence M1 → M2 |
| `cauchy_complete_implies_sup` | Mechanism equivalence M2 → M3 |
| `sup_implies_bmc` | Mechanism equivalence M3 → M1 |

**Zero sorry. Theorem A (BISH conservation) needs NO axioms beyond Lean
foundations --- it is pure BISH.**

## Contents

```
README.md                                 This file
paper35.tex                               LaTeX source
paper35.pdf                               Compiled paper
P35_ConservationMetatheorem/              Lean 4 formalization
  lakefile.lean                           Package configuration
  lean-toolchain                          leanprover/lean4:v4.28.0-rc1
  lake-manifest.json                      Dependency lock file
  Papers.lean                             Root import
  Papers/P35_ConservationMetatheorem/
    Defs.lean             136 lines       LPO, WLPO, LLPO, BMC, compositions, limits
    Composition.lean       66 lines       Theorem A: BISH conservation
    LimitBoundary.lean     65 lines       Theorem B1-B2: limit boundary
    WLPOBoundary.lean      65 lines       Theorem B3: WLPO boundary
    CalibrationTable.lean  98 lines       Theorem C: 38-entry exhaustiveness
    Mechanisms.lean       105 lines       Theorem D: mechanism equivalence
    Main.lean              92 lines       Master theorem + axiom audit
```

7 Lean source files, 627 lines total.

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
- Paper 10: Logical geography of mathematical physics -- DOI: 10.5281/zenodo.18627193
- Paper 11: Entanglement, CHSH, Tsirelson bound -- DOI: 10.5281/zenodo.18527676
- Paper 12: Constructive history of mathematical physics -- DOI: 10.5281/zenodo.18627283
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
- Paper 25: Ergodic theorems and laws of large numbers -- DOI: 10.5281/zenodo.18615453
- Paper 26: Bidual gap detection, Godel sequences -- DOI: 10.5281/zenodo.18615457
- Paper 27: IVT as mechanism behind LLPO in Bell physics -- DOI: 10.5281/zenodo.18615459
- Paper 28: Classical mechanics -- DOI: 10.5281/zenodo.18616620
- Paper 29: Fekete's Subadditive Lemma and LPO -- DOI: 10.5281/zenodo.18643617
- Paper 30: Physical dispensability of the Fan Theorem -- DOI: 10.5281/zenodo.18638394
- Paper 31: Physical dispensability of Dependent Choice -- DOI: 10.5281/zenodo.18645578
- Paper 32: QED one-loop renormalization, Landau pole -- DOI: 10.5281/zenodo.18642598
- Paper 33: QCD one-loop renormalization and confinement -- DOI: 10.5281/zenodo.18642610
- Paper 34: Scattering amplitudes are constructively computable -- DOI: 10.5281/zenodo.18642612
- Paper 35: The logical constitution of empirical physics -- This paper

## License

Apache 2.0 (code) / CC-BY 4.0 (paper).
