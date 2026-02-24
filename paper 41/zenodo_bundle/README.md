# Paper 41: The Diagnostic in Action — Axiom Calibration of the AdS/CFT Correspondence

**Author:** Paul Chun-Kit Lee (New York University)
**DOI:** 10.5281/zenodo.18654780

## Summary

The holographic dictionary is an axiom-preserving map. For every computation
examined — from vacuum RT through the FLM quantum correction to the island
formula for the information paradox — bulk and boundary carry identical axiom
cost. The Fan Theorem builds the Platonic surface in the unobservable bulk;
the boundary computes the observable entropy without it.

## Contents

- `paper41.pdf` — compiled paper (24 pages, 5 figures)
- `paper41.tex` — LaTeX source
- `P41_AdSCFT/` — complete Lean 4 formalization (955 lines, 8 modules)

## Build Instructions

Requirements: Lean 4 v4.28.0-rc1 with Mathlib (commit pinned in `lake-manifest.json`).

```bash
cd P41_AdSCFT
lake exe cache get
lake build
```

Result: 0 errors, 0 warnings, 0 sorry.

## Lean Modules

| Module | Lines | Description |
|---|---|---|
| Defs.lean | 245 | Types, CRM hierarchy, bridge axioms |
| VacuumAdS3.lean | 75 | Vacuum RT calibration (BISH) |
| ThermalBTZ.lean | 109 | BTZ entropy and phase transition |
| FLMCorrection.lean | 94 | FLM quantum correction (BISH) |
| QESScaffolding.lean | 119 | QES infimum vs. minimizer separation |
| IslandFormula.lean | 77 | Island formula and Page curve |
| CalibrationTable.lean | 130 | 12-row calibration table + consistency proofs |
| Main.lean | 106 | Master theorem and axiom audit |
| **Total** | **955** | |

## Key Results

- 12 bridge axioms (physics input)
- 35 theorems (7 genuine proofs, 28 bridge axiom assemblies)
- Master theorem axiom profile: 5 bridge axioms + propext, Classical.choice, Quot.sound

## License

CC BY 4.0
