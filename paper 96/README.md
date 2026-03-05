# Paper 96: The Root Number Bifurcation

**CRM Cost of BSD Detection Controlled by Root Number w = ±1**

Paper 96 of the Constructive Reverse Mathematics Series.
Fifteenth CRMLint Squeeze application.

## Summary

The CRM cost of BSD detection is controlled by the root number w = ±1. For w = +1 (rank 0), detection is BISH via modular symbols: L(E,1)/Ω⁺ is a rational number, checked nonzero by norm_num. For w = -1 (rank 1), detection is CLASS via Gross-Zagier (requires Rankin-Selberg). Existence is CLASS regardless of root number. Test cases: 11a1 (rank 0, w = +1) and 37a1 (rank 1, w = -1).

## Main Results

- **Theorem A (Rank 0 Modular Symbol Core):** L(E,1)/Ω⁺ = 1/5 ≠ 0 for 11a1. Five point counts, four Hecke recurrences, four multiplicativity checks, fourteen Hasse bounds, all `native_decide`. Modular symbol by `norm_num`. Pure finite arithmetic: BISH.
- **Theorem B (Root Number Bifurcation):** Detection is BISH for w = +1, CLASS for w = -1. Existence is CLASS regardless. Proved by `rfl` alone — zero axioms.
- **Theorem C (Descent Excision):** Rank bound for 37a1 via 2-descent (BISH), without Kolyvagin. Sha finiteness irreducibly CLASS.
- **Theorem D (Universal Detection/Existence Table):** Across four Squeeze campaigns (Hodge, CY3, BSD rank 1, BSD rank 0), existence is universally CLASS. Detection is BISH except when forced to CLASS by root number w = -1.

## Lean 4 Build Instructions

```bash
cd P96_RootNumberBifurcation
lake build
```

**Requirements:** Lean 4 v4.29.0-rc2, Mathlib v4.29.0-rc2 (fetched automatically by `lake build`).

**Build stats:** 1,033 lines, 86 theorems, 0 sorry, 0 errors.

## Bundle Structure

| File | Lines | Content |
|------|------:|---------|
| CRMLevel.lean | 47 | CRM hierarchy enum (BISH through CLASS) |
| HeckeData11a1.lean | 153 | Hecke eigenvalues, point counts, recurrence, Hasse bounds for 11a1 |
| ModularSymbol.lean | 73 | Modular symbol L(E,1)/Ω⁺ = 1/5, nonzero by norm_num |
| BSDRank0.lean | 174 | BSD formula, torsion, Tamagawa, Sha; CRM audit (10 BISH + 3 CLASS) |
| HeckeData37a1.lean | 97 | Hecke eigenvalues and data for 37a1 (self-contained) |
| Descent37a1.lean | 111 | 2-descent excision, Kolyvagin excision meta-theorem |
| Bifurcation.lean | 149 | Root number bifurcation, cross-programme comparison table |
| Paper96_Assembly.lean | 221 | Theorems A-D, master assembly, #print axioms |
| Papers.lean | 8 | Root import module |

## Axiom Inventory

| Theorem | Axioms | Classification |
|---------|--------|---------------|
| `theorem_A_modular_symbol_core` | `Lean.ofReduceBool`, infra | BISH (native_decide + norm_num) |
| `theorem_B_root_number_bifurcation` | *none* | Structural (rfl only) |
| `theorem_C_descent_excision` | `propext` only | BISH + structural |
| `theorem_D_universal_table` | `Lean.ofReduceBool` | BISH (native_decide) |
| `bsd_formula_matches_modular_symbol` | `propext`, `Classical.choice`, `Quot.sound` | BISH (Classical.choice is Q-infrastructure) |
| `rank0_bish_count` | `Lean.ofReduceBool` only | BISH (native_decide) |

**Documentary axioms** (boundary declarations, never invoked in proof path):
- `analytic_continuation_11a1` / `analytic_continuation_11a1_CLASS` (CLASS)
- `kato_euler_system_11a1` / `kato_euler_system_11a1_CLASS` (CLASS)
- `sha_finite_11a1` / `sha_finite_11a1_CLASS` (CLASS)
- `gross_zagier_formula` / `gross_zagier_CLASS` (CLASS)
- `kolyvagin_euler_system` / `kolyvagin_CLASS` (CLASS)
- `rankin_selberg_integral` / `rankin_selberg_CLASS` (CLASS)
- `selmer2_computation` (CAS documentary axiom)
- `modular_symbol_is_L_ratio` (documentary axiom)

## Dependencies

- Paper 95 (DOI pending): BSD Squeeze for 37a1 (rank 1, w = -1)
- Paper 94 (DOI pending): Griffiths Group Squeeze (CY3 detection/existence pattern)
- Paper 89 (DOI: 10.5281/zenodo.18809909): Hodge palindromic bifurcation
- Paper 48 (DOI: 10.5281/zenodo.18683400): LPO calibration of BSD conjecture

## Author

Paul Chun-Kit Lee, New York University, Brooklyn, New York.

## License

Creative Commons Attribution 4.0 International (CC BY 4.0).
