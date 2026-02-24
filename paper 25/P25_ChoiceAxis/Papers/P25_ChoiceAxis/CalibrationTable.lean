/-
Papers/P25_ChoiceAxis/CalibrationTable.lean
Paper 25: Updated CRM Calibration Table

This module documents the full two-axis calibration table integrating
the choice hierarchy (this paper) with the omniscience hierarchy (prior papers).

No theorems — pure documentation.
-/

namespace Papers.P25_ChoiceAxis

/-!
# CRM Calibration Table (Updated)

## Axis 1: Omniscience Hierarchy (from prior papers)

| Principle | Physical Calibration           | Paper |
|-----------|--------------------------------|-------|
| WLPO      | Bidual gap (ℓ∞/c₀)            | 2     |
| LLPO      | Bell's theorem / EPR           | 21    |
| LPO       | Thermodynamic separation       | —     |

## Axis 2: Choice Hierarchy (this paper)

| Principle | Physical Calibration                          | Section |
|-----------|-----------------------------------------------|---------|
| AC₀       | Single quantum measurement / Born rule        | III     |
| CC        | Mean ergodic theorem; weak law of large numbers | I, III |
| DC        | Pointwise ergodic theorem; strong law of large numbers | II, III |
| Full AC   | No physical calibration (pathologies only)     | IV      |

## Orthogonal Principles (from prior papers)

| Principle | Physical Calibration              | Paper |
|-----------|-----------------------------------|-------|
| MP        | Radioactive decay / unbounded search | 22   |
| FT        | Optimization on compact spaces     | 23   |

## Key Insight

The choice hierarchy has genuine physical content:
- **Ensemble/statistical behavior** (what labs verify) requires CC
- **Individual trajectory behavior** (idealized convergence) requires DC
- **Full AC** produces only mathematical pathologies with no physical content

## DC Ceiling Thesis

Conjecture: No calibratable physical theorem requires more than DC.
The Solovay model (ZF + DC + "all sets Lebesgue measurable") is the
natural set-theoretic home for mathematical physics.
-/

end Papers.P25_ChoiceAxis
