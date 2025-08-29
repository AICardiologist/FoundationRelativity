# Paper 3B Axiom Index

This document tracks all axioms used in the Paper 3B proof-theoretic framework.
All axioms are now in the `Ax` namespace for consistent naming and easy tracking.

## Summary Statistics
- **Total Axioms**: 21
- **Namespace**: All axioms use `Ax.` prefix for consistency
- **Discharge Plan**: 12 axioms are placeholders for future internalization
- **Permanent**: 9 axioms encode classical results (Gödel, Feferman)

## Axioms by Category

### Instance Propagation (2 axioms)
*Discharge plan: Show that Extend preserves arithmetization*

1. `Ax.LCons_arithmetization_instance` - Extension preserves arithmetization for LCons
2. `Ax.LReflect_arithmetization_instance` - Extension preserves arithmetization for LReflect

### Schematic Tag Refinements (2 axioms)
*Discharge plan: Connect tags to semantic formulas via arithmetization*

3. `Ax.cons_tag_refines` - Links ConTag(n) to ConsistencyFormula(LCons T0 n)
4. `Ax.rfn_tag_refines` - Links RfnTag(n) to RFN_Sigma1_Formula(LReflect T0 n)

### Collision Axioms (4 axioms)
*Discharge plan: Route through internalized RFN→Con theorem*

5. `Ax.collision_tag` - RfnTag implies ConTag at each stage
6. `Ax.collision_step_semantic` - Semantic version of collision
7. `Ax.reflection_dominates_consistency_axiom` - Ladder morphism preservation
8. `Ax.reflection_height_dominance` - Height comparison

### Classical Lower Bounds (5 axioms)
*Permanent: These encode classical proof-theoretic results*

9. `Ax.G1_lower` - Gödel's first incompleteness theorem
10. `Ax.G2_lower` - Gödel's second incompleteness theorem
11. `Ax.RFN_lower` - Reflection does not prove its own reflection
12. `Ax.cons_hierarchy_proper` - Consistency hierarchy is strict
13. `Ax.refl_hierarchy_proper` - Reflection hierarchy is strict

### Classicality Bounds (4 axioms)
*Mixed: Upper bounds dischargeable, lower bounds permanent*

14. `Ax.WLPO_height_upper` - WLPO at height 1 (dischargeable)
15. `Ax.LPO_height_upper` - LPO at height 2 (dischargeable)
16. `Ax.WLPO_lower` - WLPO independence from HA (permanent)
17. `Ax.LPO_lower` - LPO independence from HA+EM_Σ₀ (permanent)

### Core Axioms (3 axioms)
*Discharge plan: Basic arithmetization facts*

18. `Ax.Sigma1_Bot` - Bot is a Σ₁ formula
19. `Ax.Bot_is_FalseInN` - Bot is false in standard model
20. `Ax.con_implies_godel` - Con implies Gödel sentence

### Limit Behavior (1 axiom)
*Discharge plan: Prove via ordinal analysis*

21. `Ax.LClass_omega_eq_PA` - Limit of classicality ladder

## Core Theorem Dependencies

Via `#print axioms` diagnostics:

- `collision_step` depends on: [propext, Ax.collision_tag]
- `RFN_implies_Con` depends on: [Ax.Bot_is_FalseInN, Ax.Sigma1_Bot]
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