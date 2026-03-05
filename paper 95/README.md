# Paper 95: The BSD Squeeze

**CRMLint Decomposition of the Gross-Zagier-Kolyvagin Proof**

Paper 95 of the Constructive Reverse Mathematics Series.
Fourteenth CRMLint Squeeze application.

**DOI:** [10.5281/zenodo.18821019](https://doi.org/10.5281/zenodo.18821019)

## Summary

The Gross-Zagier-Kolyvagin proof of BSD for analytic rank <= 1 is the only proven case among the currently open Clay Millennium Problems. This paper applies the CRMLint Squeeze protocol to decompose the proof pipeline into BISH and CLASS components, using the elliptic curve 37a1 (y^2 + y = x^3 - x, rank 1) as computational test case.

## Main Results

- **Theorem A (Modular Symbol Core):** Hecke eigenvalue arithmetic for 37a1 is strictly BISH. 28 sub-results (point counts, recurrence, multiplicativity, Hasse bounds), all `native_decide`.
- **Theorem B (GZK Squeeze):** The proof decomposes as 15 BISH + 6 CLASS = 21 components (71% constructive). BISH core verified; CLASS shell axiomatized.
- **Theorem C (Detection/Existence Bifurcation):** Detecting the Heegner point via canonical height positivity is BISH; bounding Mordell-Weil rank via the Euler system is CLASS. Same pattern as Paper 94 (CY3 normal functions).
- **Theorem D (BSD Formula Audit):** Algebraic side (regulator, torsion, Tamagawa) is BISH; analytic side (L-value) is CLASS. Confirms Paper 48 calibration.

## Lean 4 Build Instructions

```bash
cd P95_BSDSqueeze
lake build
```

**Requirements:** Lean 4 v4.29.0-rc2, Mathlib v4.29.0-rc2 (fetched automatically by `lake build`).

**Build stats:** 796 lines, 58 theorems, 0 sorry, 0 errors.

## Bundle Structure

| File | Lines | Content |
|------|------:|---------|
| CRMLevel.lean | 47 | CRM hierarchy enum (BISH through CLASS) |
| HeckeData.lean | 173 | Hecke eigenvalues, point counts, recurrence, Hasse bounds |
| HeegnerData.lean | 168 | Heegner point, canonical height, Silverman bounds, search bound |
| GZKAxioms.lean | 133 | Documentary axiom stubs (5 CLASS, 2 BISH) |
| Paper95_BSDSqueeze.lean | 270 | Theorems A-D, assembly, #print axioms |
| Papers.lean | 5 | Root import module |

## Axiom Inventory

| Theorem | Axioms | Classification |
|---------|--------|---------------|
| `modular_symbol_core` | `Lean.ofReduceBool` only | BISH (native_decide) |
| `gzk_bish_count` | `Lean.ofReduceBool` only | BISH (native_decide) |
| `naive_height_bounded` | propext, Classical.choice, Quot.sound | BISH (linarith; Classical.choice is infrastructure) |
| `detection_existence_bifurcation` | infrastructure + 4 documentary axioms | Mixed (BISH detection + CLASS existence) |
| `bsd_formula_audit` | infrastructure + 1 documentary axiom | Mixed (BISH algebraic + CLASS analytic) |
| `bsd_squeeze_complete` | infrastructure + 5 documentary axioms | Assembly |

**Documentary axioms** (boundary declarations, not used in constructive path):
- `analytic_continuation` / `analytic_continuation_CLASS` (CLASS)
- `gross_zagier_formula` / `gross_zagier_CLASS` (CLASS)
- `kolyvagin_euler_system` / `kolyvagin_CLASS` (CLASS)
- `chebotarev_density` / `chebotarev_CLASS` (CLASS)
- `cassels_pairing` / `cassels_CLASS` (CLASS)
- `effective_chebotarev` / `effective_chebotarev_BISH` (BISH)
- `nonarchimedean_heights` / `nonarchimedean_BISH` (BISH)

## Dependencies

- Paper 48 (DOI: 10.5281/zenodo.18683400): LPO calibration of BSD conjecture
- Paper 51 (DOI: 10.5281/zenodo.18732168): Archimedean rescue, Silverman bounds
- Paper 94 (DOI: 10.5281/zenodo.18820969): Normal Function Squeeze, detection/existence pattern

## Author

Paul Chun-Kit Lee, New York University, Brooklyn, New York.

## License

Creative Commons Attribution 4.0 International (CC BY 4.0).
