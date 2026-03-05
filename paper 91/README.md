# Paper 91: The Logical Cost of Unconditional Hodge

**A CRM Audit of the Markman-Floccari-Fu Theorem**
Paper 91 of the Constructive Reverse Mathematics Series

## Summary

In February 2025, Markman (arXiv:2502.03415) unconditionally proved the Hodge Conjecture for all abelian fourfolds of Weil type. This paper subjects Markman's proof to the CRMLint Squeeze protocol, classifying its logical cost in the CRM hierarchy.

## Main Results

- **Theorem A**: Markman's proof decomposes into 4 BISH + 5 CLASS components. The CLASS boundary nodes are: Fourier-Mukai kernel existence (Zorn), Orlov representability (Brown), Schoen cycle specialization (compactness), Buchweitz-Flenner semi-regularity (analytic), and secant line existence (generic existence).

- **Theorem B**: The CRMLint Squeeze (P84-89) achieves 90% BISH (18/20) conditional on VHC. Markman achieves 44% BISH (4/9) unconditional. The Squeeze is informationally more efficient. (Granularity caveat: the two decompositions are at different resolutions.)

- **Theorem C**: Markman's unconditional result shows VHC is consistent (not refuted) for the exotic Weil class on the universal genus-4 family. The Squeeze's conditional prediction is independently confirmed.

- **Theorem D**: The de Rham-Betti comparison isomorphism (underlying the cycle class map cl: CH^2 -> H^4) is irreducibly CLASS. The "20/0 ratio" is logically impossible; best achievable is 19/1.

## Lean 4 Build Instructions

```bash
cd P91_MarkmanAudit/
lake build
```

Toolchain: `leanprover/lean4:v4.29.0-rc2`. Requires Mathlib.

## Lean Bundle Structure

| File | Lines | Content |
|------|-------|---------|
| CRMLevel.lean | 61 | CRM hierarchy (reused from P72-74, P87) |
| MarkmanAudit.lean | 222 | Theorems A, B, C + Hodge Horizon robustness |
| CycleClassMap.lean | 101 | Theorem D + impossibility of 20/0 |
| CycleData.lean | 177 | CAS-emitted palindromic cycle identities |
| Paper91_MarkmanAudit.lean | 105 | Main file: imports + axiom inventory + #print axioms |
| **Total** | **666** | |

## Axiom Inventory

**Documentary axioms** (encode external theorems, not invoked in proofs):
- `markman_theorem` — Markman 2025
- `crmlint_squeeze_conditional` — Papers 88-89
- `uniform_hodge_iff_wlpo_p87` — Paper 87
- `cycle_class_map_cost` — CRM level of cl
- `cycle_class_map_is_class` — cl is CLASS

**Infrastructure axioms** (from Lean/Mathlib):
- `propext`, `Quot.sound` — expected for ring tactic over Z

**No `Classical.choice` in any proof. Zero `sorry`.**

## CAS Script

`palindromic_cycle.py` — Python/SymPy script extending P86's Kani-Rosen verification to the 2-parameter palindromic subfamily. Emits `CycleData.lean`.

```bash
python3 palindromic_cycle.py
```

## Dependencies

- Papers 84-89 (Hodge campaign)
- Paper 87 (Hodge Horizon = WLPO)
- Paper 90 (18/2 ratio synthesis)
- Markman, arXiv:2502.03415 (2025)
- Floccari-Fu, arXiv:2504.13607 (2025)

## Author

Paul Chun-Kit Lee, New York University, Brooklyn, New York
