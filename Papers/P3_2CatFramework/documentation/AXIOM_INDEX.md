# Paper 3B Axiom Index

> **⚠️ AXIOM BUDGET LOCKED AT 22**: Future PRs must not increase this count. CI will fail if axioms > 22.

This document tracks all axioms used in the Paper 3B proof-theoretic framework.
All axioms are now in the `Ax` namespace for consistent naming and easy tracking.

## Summary Statistics
- **Total Axioms**: 22 (13 Paper 3B specific + 9 base theory infrastructure)
  - **Paper 3B Specific**: 13 axioms (BUDGET LOCKED - enforced by CI)
  - **Base Theory Infrastructure**: 9 axioms (HA, PA, EA, ISigma1, etc.)
- **Namespace**: All axioms use `Ax.` prefix for consistency
- **Discharge Plan**: 5 axioms are placeholders for future internalization
- **Permanent**: 18 axioms (9 Paper 3B classical + 9 base theory)

### Recent Progress
- **PR-1**: ✅ Discharged `LCons_arithmetization_instance` and `LReflect_arithmetization_instance` - now derived from Core.ExtendIter_arithmetization
- **PR-4**: ✅ Discharged `WLPO_height_upper` and `LPO_height_upper` - now proved via Extend_Proves
- **PR-2A**: ✅ Discharged `cons_tag_refines` and `rfn_tag_refines` - tags now parametric and defeq to semantics
- **PR-5a**: ✅ Discharged `Sigma1_Bot` - now a theorem via schematic Σ₁ definition
- **PR-5b**: ✅ Discharged `Bot_is_FalseInN` - now a theorem via AtomTrueInN schematic evaluation

## Axioms by Category

### Instance Propagation (0 axioms - DISCHARGED ✅)
*Successfully discharged in PR-1 by deriving from Core.ExtendIter_arithmetization*

~~1. `Ax.LCons_arithmetization_instance` - Extension preserves arithmetization for LCons~~ DISCHARGED
~~2. `Ax.LReflect_arithmetization_instance` - Extension preserves arithmetization for LReflect~~ DISCHARGED

### Schematic Tag Refinements (0 axioms - DISCHARGED ✅)
*Successfully discharged in PR-2A by making tags parametric and defeq to semantic formulas*

~~3. `Ax.cons_tag_refines` - Links ConTag(n) to ConsistencyFormula(LCons T0 n)~~ DISCHARGED
~~4. `Ax.rfn_tag_refines` - Links RfnTag(n) to RFN_Sigma1_Formula(LReflect T0 n)~~ DISCHARGED

### Collision Axioms (4 axioms)
*Split into cross-ladder bridge and height comparison*

#### Cross-ladder bridge (2 axioms - dischargeable via PR-2)
5. `Ax.collision_tag` - RfnTag implies ConTag at each stage
   - Discharge path: Derive from RFN_implies_Con + tag-semantics bridge
6. `Ax.collision_step_semantic` - Semantic version of collision
   - Discharge path: Follow from collision_tag once tags = semantics

#### Height comparison (2 axioms - likely permanent)
7. `Ax.reflection_dominates_consistency_axiom` - Ladder morphism preservation
   - Encodes ω^CK_1 dominance from ordinal analysis
8. `Ax.reflection_height_dominance` - Converse height comparison
   - Classical result about reflection's strength

### Classical Lower Bounds (5 axioms)
*Permanent: These encode classical proof-theoretic results*

9. `Ax.G1_lower` - Gödel's first incompleteness theorem
10. `Ax.G2_lower` - Gödel's second incompleteness theorem
11. `Ax.RFN_lower` - Reflection does not prove its own reflection
12. `Ax.cons_hierarchy_proper` - Consistency hierarchy is strict
13. `Ax.refl_hierarchy_proper` - Reflection hierarchy is strict

### Classicality Bounds (2 axioms - upper bounds DISCHARGED ✅)
*Lower bounds permanent (independence results)*

~~14. `Ax.WLPO_height_upper` - WLPO at height 1~~ DISCHARGED via Extend_Proves
~~15. `Ax.LPO_height_upper` - LPO at height 2~~ DISCHARGED via Extend_Proves
14. `Ax.WLPO_lower` - WLPO independence from HA (permanent)
15. `Ax.LPO_lower` - LPO independence from HA+EM_Σ₀ (permanent)

### Core Axioms (1 axiom)
*Discharge plan: Basic arithmetization facts*

~~16. `Ax.Sigma1_Bot` - Bot is a Σ₁ formula~~ DISCHARGED (PR-5a: theorem via schematic definition)
~~17. `Ax.Bot_is_FalseInN` - Bot is false in standard model~~ DISCHARGED (PR-5b: theorem via AtomTrueInN)
16. `Ax.con_implies_godel` - Con implies Gödel sentence

### Limit Behavior (1 axiom)
*Discharge plan: Prove via ordinal analysis*

17. `Ax.LClass_omega_eq_PA` - Limit of classicality ladder

## Core Theorem Dependencies

Via `#print axioms` diagnostics:

- `collision_step` depends on: [propext, Ax.collision_tag]
- `RFN_implies_Con` depends on: [propext] (Bot_is_FalseInN and Sigma1_Bot are now theorems)
- `reflection_dominates_consistency` depends on: [Ax.reflection_dominates_consistency_axiom]
- `godel_height_cert` depends on: [propext, Ax.con_implies_godel]

## Discharge Priority

High priority (enables many others):
1. Instance propagation axioms
2. Tag refinement axioms
3. `proves_RFN_implies_proves_Con`

Medium priority (specific applications):
4. Collision axioms
5. Classicality upper bounds

Low priority (classical, may remain as axioms):
6. Classical lower bounds
7. Independence results

## Usage in Modules

- **Progressions.lean**: Uses 5 axioms (instance, refinement, limit)
- **Heights.lean**: Uses 11 axioms (bounds, hierarchies, connection)
- **Collisions.lean**: Uses 4 axioms (collision, morphism, dominance)
- **Reflection.lean**: Uses 3 axioms (internalization, iteration)

## Notes

All axioms include provenance documentation explaining their mathematical source and whether they are intended for future discharge or will remain as named classical results.