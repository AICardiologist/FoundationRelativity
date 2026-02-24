# Paper 23: The Fan Theorem and the Constructive Cost of Optimization

**Free Energy Extrema on Compact Parameter Spaces**

Paper 23 in the Constructive Reverse Mathematics Series
Paul C.-K. Lee (NYU), February 2026

## Overview

This Lean 4 formalization establishes that the assertion "a continuous function on a compact interval attains its extremum" — the Extreme Value Theorem (EVT) — is equivalent to the Fan Theorem (FT) over BISH, and instantiates this equivalence through free energy optimization in the 1D Ising model.

This is the first CRM calibration at the Fan Theorem, adding a **third independent branch** to the calibration hierarchy:

```
        LPO
       / | \
      /  |  \
   WLPO  MP  ...
    |
   LLPO
    |
   BISH            FT (independent of all above)
```

## Main Results

| Theorem | Statement |
|---------|-----------|
| `ft_iff_compact_opt` | FanTheorem ↔ CompactOptimization |
| `evt_max_iff_evt_min` | EVT_max ↔ EVT_min |
| `ising_opt_of_ft` | FT → Ising free energy attains its minimum on [a, b] |
| `fan_stratification` | Three-branch partial order (omniscience + MP + FT) |
| `finite_opt_bish` | Finite-grid optimization is BISH |

## Axiom Audit

**ZERO custom axioms.** Every theorem depends only on Mathlib infrastructure:

- `propext`, `Classical.choice`, `Quot.sound`

This is the cleanest axiom audit of any paper in the CRM series (Papers 2-23). Achieved by defining `FanTheorem := EVT_max` directly; the equivalence with the bar-theoretic Fan Theorem is by citation (Berger 2005, Bridges-Vita 2006).

## Project Structure

```
P23_FanTheorem/
  lakefile.lean
  lean-toolchain          (leanprover/lean4:v4.28.0-rc1)
  Papers.lean
  Papers/P23_FanTheorem/
    Defs/
      EVT.lean             EVT_max, EVT_min, CompactOptimization, FanTheorem
      IsingFreeEnergy.lean isingFreeEnergy, positivity helpers
      Principles.lean      LPO, WLPO, LLPO, MP, hierarchy proofs
      Rescaling.lean       rescale/unscale between [0,1] and [a,b]
    PartA/
      Continuity.lean      isingFreeEnergy_continuous
      FiniteOpt.lean       finite_opt_bish (Finset.exists_min_image)
      PartA_Main.lean      Summary and axiom audit
    PartB/
      EVTEquiv.lean        EVT_max ↔ EVT_min (negate f)
      CompactOpt.lean      EVT_min ↔ CompactOptimization (rescaling)
      PartB_Main.lean      ft_iff_compact_opt
    Main/
      PhysicalInstance.lean  ising_opt_of_ft
      Stratification.lean    fan_stratification (three-branch)
      AxiomAudit.lean        Comprehensive #print axioms
    Main.lean                Root imports
```

14 files, ~684 lines.

## Build

```bash
lake build    # 0 errors, 0 warnings, 0 sorry
```

Requires Lean 4.28.0-rc1 and Mathlib.

## The 1D Ising Model: Four Logical Costs

The same physical system — the 1D Ising model with free energy f(beta, J) = -log(2 cosh(beta J)) — now exhibits four distinct logical costs across Papers 8, 20, 22, and 23:

| Question | Principle | Paper |
|----------|-----------|-------|
| Finite-volume computation | BISH | 8 (Part A) |
| Thermodynamic limit existence | LPO | 8 (Part B) |
| Phase classification (magnetization zero-test) | WLPO | 20 |
| Parameter-space optimization | FT | 23 |

## References

- Berger (2005), "The Fan Theorem and Uniform Continuity", CiE 2005
- Bridges and Vita (2006), *Techniques of Constructive Analysis*, Springer
- Julian and Richman (2002), "A Constructive Proof of Bolzano's Theorem"
