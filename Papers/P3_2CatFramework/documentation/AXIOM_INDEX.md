# Paper 3B Axiom Index

> **⚠️ AXIOM BUDGET UPDATE**: Currently at 21 axioms (PR-7: collision_tag discharged, replaced by RFN_to_Con_formula)
> **BUDGET LOCKED AT 21**

This document tracks all axioms used in the Paper 3B proof-theoretic framework.
All axioms are now in the `Ax` namespace for consistent naming and easy tracking.

## Summary Statistics
- **Total Axioms**: 21 (12 Paper 3B specific + 9 base theory infrastructure)
  - **Paper 3B Specific**: 12 axioms (collision_tag discharged but RFN_to_Con_formula added for internalization)
  - **Base Theory Infrastructure**: 9 axioms (HA, PA, EA, ISigma1, etc.)
- **Namespace**: All axioms use `Ax.` prefix for consistency
- **Note**: PR-7 trades collision_tag for cleaner RFN_to_Con_formula internalization axiom
- **Permanent**: 20 axioms (11 Paper 3B + 9 base theory)

### Recent Progress
- **PR-1**: ✅ Discharged `LCons_arithmetization_instance` and `LReflect_arithmetization_instance` - now derived from Core.ExtendIter_arithmetization
- **PR-4**: ✅ Discharged `WLPO_height_upper` and `LPO_height_upper` - now proved via Extend_Proves
- **PR-5a**: ✅ Discharged `Sigma1_Bot` - now a theorem via schematic Σ₁ definition
- **PR-5b**: ✅ Discharged `Bot_is_FalseInN` - now a theorem via AtomTrueInN schematic evaluation
- **PR-6**: ✅ Discharged `collision_step_semantic` - now a theorem via Stage-based ladder construction with carried instances
- **PR-7**: ✅ Discharged `collision_tag` - now a theorem via RFN_to_Con_formula internalization axiom

## Axioms by Category

### Instance Propagation (0 axioms - DISCHARGED ✅)
*Successfully discharged in PR-1 by deriving from Core.ExtendIter_arithmetization*

~~1. `Ax.LCons_arithmetization_instance` - Extension preserves arithmetization for LCons~~ DISCHARGED
~~2. `Ax.LReflect_arithmetization_instance` - Extension preserves arithmetization for LReflect~~ DISCHARGED

### Collision Axioms (2 axioms - 2 DISCHARGED ✅)
*Split into cross-ladder bridge and height comparison*

#### Cross-ladder bridge (0 axioms - ALL DISCHARGED)
~~5. `Ax.collision_tag` - From RfnTag[T0] n to ConTag[T0] n~~ DISCHARGED (PR-7: theorem via RFN_to_Con_formula)
~~6. `Ax.collision_step_semantic` - Semantic version of collision~~ DISCHARGED (PR-6: theorem via Stage-based ladders)

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

### Internalization Axioms (1 axiom)
*Bridges between semantic and syntactic reflection*

16. `RFN_to_Con_formula` - Internalization: RFN_Sigma1_Formula T implies ConsistencyFormula T
   - Discharge path: Requires full internalization infrastructure

### Core Axioms (1 axiom)
*Discharge plan: Basic arithmetization facts*

~~17. `Ax.Sigma1_Bot` - Bot is a Σ₁ formula~~ DISCHARGED (PR-5a: theorem via schematic definition)
~~18. `Ax.Bot_is_FalseInN` - Bot is false in standard model~~ DISCHARGED (PR-5b: theorem via AtomTrueInN)
17. `Ax.con_implies_godel` - Con implies Gödel sentence

### Limit Behavior (1 axiom)
*Discharge plan: Prove via ordinal analysis*

18. `Ax.LClass_omega_eq_PA` - Limit of classicality ladder

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