# Paper 3A Axiom Index

**Last Updated**: September 2025  
**Status**: Axiom-Free Implementation  
**Target**: 0 sorries, 0 axioms achieved

## Overview

**Paper 3A is completely axiom-free.** All independence results and height characterizations are demonstrated through assumption-parametric patterns without introducing axioms to the framework.

## Implementation Strategy

### Assumption-Parametric Modules

Instead of axioms, Paper 3A uses:

1. **HeightOracle structures** in FT_Frontier.lean:
```lean
structure HeightOracle where
  heightAt : Axis → WitnessFamily → Option Nat
  gap_wlpo : heightAt WLPO_axis GapFamily = some 1
  gap_ft   : heightAt FT_axis GapFamily = some 0
  -- etc.
```

2. **Variable sections** in Examples/:
```lean
section HeightDemonstration
variable
  (h_gap_WLPO : HeightAt WLPO_axis GapWitness = some 1)
  (h_gap_FT   : HeightAt FT_axis GapWitness = some 0)
-- Theorems using these assumptions
end HeightDemonstration
```

### What This Achieves

- **Independence demonstrations** without axioms
- **Height calibrations** as parametric theorems
- **Clean CI verification** (no sorries, no axioms)
- **Framework extensibility** without axiom burden

## Total Count

**Paper 3A Axioms**: 0 (fully axiom-free implementation)

3A modules are axiom-free; independence and per-axis heights are supplied via assumption-parametric oracles in demo modules. No ProofTheory axioms are imported in 3A.

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