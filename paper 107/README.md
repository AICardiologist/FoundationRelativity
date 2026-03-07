# Paper 107: The Condensed GAGA Conjecture

**Paper 107 of the Constructive Reverse Mathematics Series**
*First CRM Prediction Paper*

## Summary

This paper formulates the first *predictive* conjecture of the CRM program: the Clausen-Scholze condensed reformulation of Serre's GAGA theorem will reduce the CRM cost of GAGA descent from CLASS to at most BISH + WKL + WLPO ≤ LPO. If correct, the overall CRM cost of the regular holonomic Riemann-Hilbert correspondence (Paper 106) drops from CLASS to LPO, with Deligne's canonical extension (the floor function on ℝ) as the sole non-constructive bottleneck.

## Main Results

- **Conjecture A (Condensed GAGA Deflation):** Condensed GAGA eliminates Montel's theorem, reducing CRM cost from CLASS to ≤ LPO.
- **Corollary B (Riemann-Hilbert Descent):** Under Conjecture A, CRM(RH_reg) drops from CLASS to LPO.
- **Theorem C (Falsifiability Wager):** The Archimedean Obstruction Thesis (Paper 98) is strictly falsifiable at the RH correspondence.

## Lean 4 Bundle

Located in `P107_CondensedGAGA/`.

### Build Instructions

```bash
cd P107_CondensedGAGA
lake build
```

Requires: `leanprover/lean4:v4.29.0-rc2`, Mathlib v4.29.0-rc2.

### File Structure

| File | Lines | Content |
|------|-------|---------|
| `CRMLevel.lean` | 139 | CRM partial order with WKL, WKL_WLPO, join, incomparability |
| `CondensedGAGA.lean` | 233 | API contract: axioms, composites, predictions |

### Axiom Inventory

**CRMLevel.lean:**
- `#print axioms wkl_join_wlpo` → (none) — pure `rfl`

**CondensedGAGA.lean:**
- `#print axioms classical_rh` → `build_rh`, `classical_gaga`, `deligne_extension` (CLASS path)
- `#print axioms condensed_rh` → `build_rh`, `condensed_gaga`, `deligne_extension` (LPO path, no `classical_gaga`)

**Axioms (typed API contract):**
- `build_rh` — combinator: GAGA + Deligne → RH equivalence (structural, no CRM cost)
- `classical_gaga` — Serre GAGA via Montel (CLASS)
- `condensed_gaga` — Clausen-Scholze liquid GAGA (WLPO + WKL)
- `deligne_extension` — Deligne canonical extension (LPO)
- `lte_exactness_bish` — Breen-Deligne resolution is finitary (BISH, documentary)
- `montel_is_class` — Montel's theorem requires LEM (CLASS, documentary)

### Classical.choice Audit

All theorems over ℝ in Mathlib show `Classical.choice` due to totalized inverse 0⁻¹ = 0. This is infrastructure, not logical content. Constructive stratification is established by the typed axiom architecture.

## Dependencies

- Paper 106: CRM audit of the Riemann-Hilbert correspondence
- Paper 98: The Archimedean Obstruction Thesis
- Paper 99: AOT validation via Hecke theta series

## License

CC BY 4.0
