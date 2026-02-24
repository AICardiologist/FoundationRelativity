# Paper 10 — The Logical Geography of Mathematical Physics (v3.0)

**Technical Synthesis of Papers 2–24**

**Author:** Paul Chun-Kit Lee (New York University)
**Date:** February 2026
**Series:** Constructive Reverse Mathematics for Mathematical Physics

## Abstract

This paper assembles the complete calibration table for the Constructive Reverse Mathematics (CRM) programme applied to mathematical physics. Across nineteen companion papers (Papers 2–9, 11, 13–24), approximately 40 physical propositions from nine domains — statistical mechanics, quantum mechanics, general relativity, quantum information, quantum field theory, quantum gravity, particle physics, semiclassical mechanics, and quantum foundations — have been classified by their exact logical cost over Bishop's constructive mathematics (BISH). The results, totalling approximately 18,500 lines of Lean 4 code verified against Mathlib, populate six levels of the constructive hierarchy: BISH, LLPO, WLPO, LPO, the Fan Theorem (FT), and Markov's Principle (MP), with the hierarchy forming a partial order with three mutually independent branches. The programme also establishes observable-dependent logical cost (the same physical system requiring different principles for different observables) and detects hidden structural identities (Bell nonlocality and Kochen–Specker contextuality sharing identical logical cost at LLPO despite being physically distinct phenomena).

## Contents

```
paper10_logical_geography.tex    LaTeX source (27 pages)
paper10_logical_geography.pdf    Compiled PDF
README.md                        This file
```

## What This Paper Contains

Paper 10 is the **technical synthesis** of the CRM series. It does not contain original proofs or Lean formalizations; instead it:

1. **Calibration table** (~40 entries): Every physical proposition classified by the series, organized by logical cost (BISH through LPO, plus FT and MP)
2. **Hasse diagram**: The partial order of constructive principles populated by physical calibrations, showing the tree structure with three independent branches
3. **Executive summary**: Per-paper overview of all 19 companion papers (Papers 2–24)
4. **Machine verification report**: Certification levels, axiom audits, and line counts for each formalization
5. **Verified results**: One subsection per companion paper (§5.1–§5.19)
6. **The Programme's Development** (NEW in v3.0): Narrative account of how the programme evolved through four phases — pre-LPO exploration, BISH-LPO systematic era, frontier probing, and refinement/new axes — with per-paper intellectual history (~7 pages)
7. **Structural analysis**: Observable-dependent cost, structural identity detection (Bell ≡ KS at LLPO), diagnostic power (MP for tunneling controversy, DC_ω for measurement problem)
8. **Open problems**: 14 problems including 3 resolved by Papers 17–24

## Key Results

### The Hierarchy (populated)

| Principle | Papers | Physical Content |
|-----------|--------|-----------------|
| BISH | 5, 6, 8A, 9, 11, 15A, 16A, 17A,C, 18, 19A, 21A, 24A | Finite computations, algebraic identities, uncertainty relations |
| LLPO | 19B, 21B, 24B | WKB turning points, Bell disjunction, KS sign decision |
| WLPO | 2, 7, 20 | Bidual gap, reflexivity, phase classification |
| MP | 22 | Radioactive decay (eventual detection) |
| DC_ω | 16B | Born rule (measurement convergence) |
| FT | 23 | Compact optimization (EVT on [a,b]) |
| LPO | 4, 8B, 13, 14, 15B, 17B, 19C | Spectral theory, thermodynamic limits, event horizons, decoherence, BH entropy |

### Conceptual Advances in v3.0

- **LLPO populated**: Three independent physical calibrations resolve the v2.0 gap (Problem 3a)
- **Fan Theorem branch**: Third independent branch of the hierarchy (independent of omniscience chain and MP)
- **Observable-dependent cost**: Same 1D Ising model at four different logical costs depending on observable
- **Structural identity**: Bell nonlocality ≡ KS contextuality at LLPO — detected by CRM, invisible to informal analysis
- **Diagnostic power**: Tunneling traversal time controversy diagnosed as MP disagreement

## Complete Paper List

- Paper 2: Bidual gap and WLPO — DOI: 10.5281/zenodo.17107493
- Paper 4: Quantum spectra axiom calibration — DOI: 10.5281/zenodo.17059483
- Paper 5: Schwarzschild curvature verification — DOI: 10.5281/zenodo.18489703
- Paper 6: Heisenberg uncertainty (v2, CRM over Mathlib) — DOI: 10.5281/zenodo.18519836
- Paper 7: Physical bidual gap, trace-class operators — DOI: 10.5281/zenodo.18527559
- Paper 8: 1D Ising model and LPO — DOI: 10.5281/zenodo.18516813
- Paper 9: Ising formulation-invariance — DOI: 10.5281/zenodo.18517570
- Paper 10: Logical geography of mathematical physics — DOI: 10.5281/zenodo.18580342 [this paper, v3.0]
- Paper 11: Entanglement, CHSH, Tsirelson bound — DOI: 10.5281/zenodo.18527676
- Paper 12: Constructive history of mathematical physics — DOI: 10.5281/zenodo.18581707 [v3.0 Historical Synthesis]
- Paper 13: Event horizon as logical boundary — DOI: 10.5281/zenodo.18529007
- Paper 14: Quantum decoherence — DOI: 10.5281/zenodo.18569068
- Paper 15: Noether theorem — DOI: 10.5281/zenodo.18572494
- Paper 16: Technical note: Born rule — DOI: 10.5281/zenodo.18575377
- Paper 17: Bekenstein-Hawking formula — DOI: 10.5281/zenodo.18597306
- Paper 18: Fermion mass hierarchy and scaffolding principle — DOI: 10.5281/zenodo.18600243
- Paper 19: WKB tunneling and LLPO — DOI: 10.5281/zenodo.18602596
- Paper 20: Observable-dependent logical cost, 1D Ising magnetization and WLPO — DOI: 10.5281/zenodo.18603079
- Paper 21: Bell nonlocality and LLPO — DOI: 10.5281/zenodo.18603251
- Paper 22: Markov's Principle and radioactive decay — DOI: 10.5281/zenodo.18603503
- Paper 23: Fan Theorem and optimization — DOI: 10.5281/zenodo.18604312
- Paper 24: Kochen-Specker contextuality and LLPO — DOI: 10.5281/zenodo.18604317

## Series

Paper 10 in the Constructive Reverse Mathematics series.
Full archive: [Zenodo DOI 10.5281/zenodo.18580342](https://doi.org/10.5281/zenodo.18580342)

## License

This work is released for academic use.
