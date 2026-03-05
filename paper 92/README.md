# Paper 92: Breaking the Bézout Wall: Trace Vanishing to Dimension 16 via Zariski Grid Specialization — A CRMLint Squeeze

**Paper 92 of the Constructive Reverse Mathematics Series**

Author: Paul Chun-Kit Lee (NYU)

**DOI:** [10.5281/zenodo.18816696](https://doi.org/10.5281/zenodo.18816696)

## Summary

Extends the Gauss-Manin trace vanishing pipeline from genus 4 (Papers 84-89) to genera 5-8, proving that the exotic Weil class on the Jacobian of the universal odd hyperelliptic family is cohomologically flat in dimensions 10, 12, 14, and 16.

**Key result:** For genus 5, the connection trace vanishes as an explicit polynomial identity in Z[a1,a2,a3,a4]. For genera 6-8, symbolic expansion triggers exponential intermediate expression swell; we bypass this via Zariski Grid Specialization (evaluate at concrete integer fibers, invoke Schwartz-Zippel). The CRM classification remains BISH throughout.

## Main Results

- **Theorem A:** Explicit trace vanishing for genus 5 (polynomial identity, `ring`)
- **Theorem B:** Grid trace vanishing for genera 6-8 (integer arithmetic, `norm_num`)
- **Theorem C:** Schwartz-Zippel classification — grid verification is BISH
- **Theorem D:** CRM Audit — 94 verified theorems, 0 sorry, 0 Classical.choice

## CRM Classification

| Component | Level | Verification |
|-----------|-------|-------------|
| Griffiths tau+ = 0 (genus 5) | BISH | `ring` |
| Grid tau+ = 0 (genera 6-8) | BISH | `norm_num` |
| Schwartz-Zippel lift | BISH | axiom stub |
| Shioda Fermat anchor | CLASS | axiom stub |
| Atiyah deformation bridge | CLASS | axiom stub |
| Higher secant sheaf existence | CLASS | axiom stub |

Overall: CLASS (conditional on VHC). BISH core: 94/94 verified theorems.

## Lean 4 Bundle

- **File:** `P92_HigherHodge/Papers/P92_HigherHodge/Paper92_HigherHodge.lean`
- **Lines:** 333
- **Theorems:** 94 (4 ring + 90 norm_num)
- **Sorry:** 0
- **Classical.choice:** 0
- **Toolchain:** Lean 4 v4.29.0-rc2 + Mathlib

### Build Instructions

```bash
cd P92_HigherHodge
lake exe cache get   # download Mathlib cache
lake build           # ~85s on Apple M-series
```

### Axiom Inventory

Lean infrastructure:
- `propext` (propositional extensionality)
- `Quot.sound` (quotient soundness)

CRM content axioms:
- `schwartz_zippel_grid_vanishing` — grid density implies generic vanishing (BISH)
- `shioda_fermat_anchor` — Shioda's theorem on Fermat surfaces (CLASS)
- `atiyah_deformation_bridge` — Atiyah class / Gauss-Manin trace (CLASS)
- `higher_secant_sheaf_existence` — Markman-type sheaf construction (CLASS)

## Computation Scripts

- `fast_symbolic.py` — Symbolic Griffiths reduction for genus 5 (~191s)
- `higher_hodge_grid.py` — Zariski Grid Specialization for genera 6-8 (~1.2s)

## Dependencies

- Papers 80-82: Griffiths pole reduction pipeline
- Papers 84-89: Genus-4 trace vanishing and Squeeze methodology
- Paper 76: CRMLint design
- Paper 91: Markman audit (higher secant sheaf reference)
