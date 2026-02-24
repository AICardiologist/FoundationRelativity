# Paper 49: The Hodge Conjecture and Constructive Omniscience

## Overview

Lean 4 formalization and companion paper for the constructive reverse mathematics (CRM) calibration of the Hodge Conjecture. This is Paper 49 of the Constructive Reverse Mathematics series.

## Main Results

| Theorem | Statement | Strength |
|---------|-----------|----------|
| H1 | Hodge type (r,r) decidability ↔ LPO(ℂ) | BISH ↔ BISH + LPO |
| H2 | Rationality decidability → LPO(ℂ) | BISH |
| H3a | Hodge-Riemann form positive-definite on (r,r)-classes | BISH (from axiom) |
| H3b | Polarization blind to rational lattice | BISH (from axiom) |
| H4 | Numerical equivalence decidable in BISH | BISH |
| H5a | Hodge class detection requires LPO | BISH |
| H5b | With Hodge Conjecture, verification reduces to BISH + MP | BISH (from conjecture) |
| H5c | Neither polarization nor algebraic descent alone suffices | Assembly |

## Build Status

- **Errors:** 0
- **Warnings:** 0
- **Sorries:** 0
- **Custom axioms:** 28 (cohomology infrastructure + encoding axioms)

## File Structure

```
P49_Hodge/
  Papers/P49_Hodge/
    Defs.lean          -- 306 lines, definitions and 28 axioms
    H1_HodgeTypeLPO.lean  -- 86 lines, Hodge type ↔ LPO
    H2_RationalityLPO.lean -- 67 lines, rationality → LPO
    H3_Polarization.lean   -- 102 lines, polarization available but blind
    H4_CycleVerify.lean    -- 126 lines, cycle verification in BISH
    H5_Nexus.lean          -- 130 lines, the nexus theorem
    Main.lean              -- 208 lines, summary + axiom audits
  Papers.lean
  lakefile.lean
  lean-toolchain

paper49.pdf            -- Companion paper (15 pages)
```

## Requirements

- Lean 4: `leanprover/lean4:v4.29.0-rc1`
- Mathlib4 (fetched automatically by Lake)

## Build Instructions

```bash
cd P49_Hodge
lake build
```

## Author

Paul Chun-Kit Lee, New York University

## License

Creative Commons Attribution 4.0 International (CC BY 4.0)
