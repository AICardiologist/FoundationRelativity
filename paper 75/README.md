# Paper 75: Conservation Test — CRM Calibration of the Genestier-Lafforgue Local Langlands Parametrization

**Paper 75, Constructive Reverse Mathematics Series**

Paul Chun-Kit Lee, New York University, Brooklyn, NY

## Summary

This paper applies the DPT framework (Papers 72-74) as an external diagnostic on the Genestier-Lafforgue semisimple local Langlands parametrization for arbitrary reductive G. The Fargues-Scholze proof decomposes into three independently calibrated layers:

1. **Algebraic layer** (solidification): BISH — Mittag-Leffler holds trivially via split epimorphisms of finite sets.
2. **Homological layer** (K-injective resolutions): CLASS via Zorn's lemma — Cech bypass fails (infinite cohomological dimension).
3. **Geometric layer** (v-topology): CLASS via BPI (Boolean Prime Ideal theorem).

The **statement** costs only BISH + WLPO: Schur's lemma applied to the Bernstein center deterministically extracts the semisimple parameter (no existential search), and the residual cost is the trace equality test (WLPO, Paper 74).

## Main Results

- **Theorem A** (Stratification): fs_proof_cost = CLASS.
- **Theorem B** (Statement Cost): gl_statement_cost = WLPO.
- **Theorem C** (Conservation Gap): WLPO < CLASS (two-level gap).
- **Theorem D** (DPT Prediction): Axiom 2 predicts WLPO; observed WLPO. Prediction confirmed.

## Lean 4 Bundle

**Directory:** `P75_ConservationTest/`
**Toolchain:** `leanprover/lean4:v4.29.0-rc2`
**Build:** `cd P75_ConservationTest && lake build`
**Lines:** ~180 lines
**Sorry count:** 0
**Propext:** 0
**Classical.choice:** 0

### File Structure

| File | Lines | Content |
|------|-------|---------|
| `Defs.lean` | ~80 | CRM hierarchy, proof layers, 4 opaque+axiom pairs |
| `Stratification.lean` | ~55 | Layer costs, proof cost = CLASS |
| `Conservation.lean` | ~65 | Gap theorem, DPT prediction, assembly |
| `Main.lean` | ~25 | Entry point, `#check` statements |

### Axiom Inventory (4 axioms)

| Axiom | Value | Reference |
|-------|-------|-----------|
| `algebraic_layer_cost_eq` | BISH | Clausen-Scholze (2019) |
| `homological_layer_cost_eq` | CLASS | Fargues-Scholze (2021) |
| `geometric_layer_cost_eq` | CLASS | Scholze (2017) |
| `gl_statement_cost_eq` | WLPO | Paper 74, Bernstein (1984) |

### Dependencies

- Mathlib4 (via `Mathlib.Order.Defs.PartialOrder`)

## Paper

- `paper75.tex` — LaTeX source (15 pages)
- `paper75.pdf` — compiled PDF
