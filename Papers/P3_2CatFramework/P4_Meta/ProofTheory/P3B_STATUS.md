# Paper 3B Status

> **Reminder:** We still have **17 Paper-3B axioms**. Near-term plan removes **2** (PR-2A), aiming for **15**.  
> Keep PRs small, green, and budget-reducing; avoid introducing new Ax. items.

## Current State (2025-08-31)

### ✅ Completed PRs
- **PR #129**: Initial Paper 3B framework (21 axioms)
- **PR #130**: Discharge arithmetization propagation (28 → 26 axioms)
- **PR #133**: Discharge WLPO/LPO upper bounds (28 → 26 axioms)
- **PR #134**: Collision documentation improvements (no budget change)
- **PR #135**: CI tooling enhancements (per-file reporting, cross-platform)

### 📊 Axiom Budget Progress
```
Initial:  30 axioms (21 Paper-3B + 9 base)
PR-1:     28 axioms (-2 arithmetization propagation)
PR-4:     26 axioms (-2 WLPO/LPO upper bounds)
Current:  26 axioms (17 Paper-3B + 9 base)
Target:   24 axioms (after PR-2A)
```

### 🎯 Next Immediate Steps

#### PR-2A: Parametric Tags (26 → 24 axioms)
- Make `ConTag` and `RfnTag` take Theory parameter
- Achieve definitional equality with semantic formulas
- Removes 2 tag-semantics bridge axioms
- Enables collision bridge discharge

#### PR-5: Core Definability (24 → 22-23 axioms)
- Target `Sigma1_Bot` and/or `Bot_is_FalseInN`
- Use existing arithmetization infrastructure
- Small, focused proof internalization

### 🔒 Permanent Axioms (likely to remain)
- 5 classical lower bounds (G1, G2, RFN, WLPO, LPO independence)
- 2 height comparison (ordinal analysis results)
- 2 hierarchy strictness (cons/refl proper)
- 1 limit behavior (LClass_omega_eq_PA)

### 📈 Success Metrics
- **Primary**: Axiom count reduction (26 → 24 → 22)
- **Secondary**: Clean `#print axioms` output for key theorems
- **Tertiary**: Maintainable code with clear discharge paths

## Development Guidelines

1. **Every PR must either**:
   - Reduce axiom count, OR
   - Improve tooling/docs without adding axioms

2. **Before opening a PR**:
   - Run `./.ci/check_axioms.sh` locally
   - Check `#print axioms` for new theorems
   - Update AXIOM_INDEX.md if count changes

3. **CI will enforce**:
   - Total axiom budget ≤ 26
   - All axioms in `namespace Ax`
   - No sorries in ProofTheory modules

## Resources
- [ROADMAP.md](./ROADMAP.md) - Detailed discharge plan
- [AXIOM_INDEX.md](../../documentation/AXIOM_INDEX.md) - Complete axiom inventory
- CI script: `./.ci/check_axioms.sh` (with `MAX_AXIOMS_OVERRIDE` for testing)