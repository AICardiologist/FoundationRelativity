# Paper 3A Axiom Index

**Last Updated**: September 2025  
**Status**: Active Development  
**Target**: 0 sorries, minimal axioms for framework

## Overview

Paper 3A uses axioms only for:
1. **Independence assertions** between axes (WLPO ⊥ FT)
2. **Height calibrations** for specific theorems
3. **Future work placeholders** (DC_ω axis)

## Axiom Categories

### 1. Independence Axioms (2 axioms)

These assert orthogonality between logical principles:

```lean
axiom ft_independent_of_wlpo : FT ⊬ WLPO
axiom wlpo_independent_of_ft : WLPO ⊬ FT
```

**Justification**: Classical independence results from constructive reverse mathematics.

### 2. Height Calibration Axioms (4 axioms)

These provide exact heights for key theorems:

```lean
axiom gap_height_one : uniformization_height gap = 1  -- On WLPO axis
axiom uct_height_one : uniformization_height UCT = 1   -- On FT axis
axiom gap_not_height_zero : ¬(uniformization_height gap = 0)
axiom uct_not_height_zero : ¬(uniformization_height UCT = 0)
```

**Justification**: Proven results from Papers 1-2 and classical CRM.

### 3. DC_ω Placeholders (2 axioms)

Future work for Paper 3C:

```lean
axiom dc_omega_independent_of_wlpo : DC_ω ⊬ WLPO
axiom dc_omega_independent_of_ft : DC_ω ⊬ FT
```

**Status**: Outside CI, earmarked for future development.

## Total Count

**Paper 3A Axioms**: 8 (all justified by external results)
- Independence: 2
- Height calibrations: 4  
- Future work: 2

## Comparison with Paper 3B

Paper 3B (frozen) has 21 axioms for proof-theoretic scaffolding.
Paper 3A and 3B share NO axioms - they are completely separate.

## Verification

Run to check Paper 3A axioms:
```bash
lake build Papers.P3_2CatFramework.Paper3A_Main
grep -r "axiom " Papers/P3_2CatFramework --include="*.lean" | \
  grep -v "ProofTheory" | grep -v "old_3b"
```

## Principles

1. **No sorries**: All incomplete proofs must be axiomatized explicitly
2. **External justification**: Each axiom references published results
3. **Minimal surface**: Use axioms only where mathematically necessary
4. **Clear separation**: No overlap with Paper 3B's axiom budget