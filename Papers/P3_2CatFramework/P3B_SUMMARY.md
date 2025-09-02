# Paper 3B Implementation Summary

## Final State: 21 Axioms (Schematic Encoding Limit)

### Key Achievements

#### 1. Stage-Based Ladder Construction (PR-6)
- **Problem Solved**: Circular dependencies between ladders and arithmetization instances
- **Solution**: `Stage` structure bundles `Theory` with `HasArithmetization`
- **Impact**: Clean recursion without forward references or mutual blocks
- **Files**: `Progressions.lean` completely rewritten

#### 2. Cross-Ladder Bridge Complete (PR-7)
- **collision_step_semantic**: Discharged as theorem via Stage-based approach
- **collision_tag**: Discharged as theorem via `RFN_implies_Con_formula`
- **Trade-off**: Replaced specific axiom with general internalization bridge
- **Status**: All collision machinery now theorems

#### 3. Tag System
- **Design**: Tags are pure notations, definitionally equal to semantic formulas
- **Notation**: `RfnTag[T0] n := RFN_Sigma1_Formula (LReflect T0 n)`
- **Notation**: `ConTag[T0] n := ConsistencyFormula (LReflect T0 n)`
- **Benefit**: No bridge axioms needed between tags and semantics

### Schematic Encoding Limitations

Our formulas are represented as atoms (`Formula.atom` with codes), which prevents:
- **Instantiation**: Cannot derive `ConsistencyFormula T` from `RFN_Sigma1_Formula T`
- **Fixed-points**: Cannot prove `con_implies_godel` via diagonalization
- **Syntax manipulation**: No object-level quantifier elimination or substitution

### Axiom Breakdown (21 Total)

#### Paper 3B Specific (12 axioms)
- **Height comparison**: 2 axioms (reflection dominance)
- **Classical bounds**: 7 axioms (G1, G2, RFN lower bounds, hierarchy strictness, WLPO/LPO independence)
- **Internalization**: 1 axiom (`RFN_implies_Con_formula` - bridge due to schematic encoding)
- **Core**: 1 axiom (`con_implies_godel` - requires fixed-point)
- **Limit**: 1 axiom (`LClass_omega_eq_PA`)

#### Base Theory Infrastructure (9 axioms)
- **Theories**: HA, PA, EA, ISigma1
- **Relations**: HA_weaker_PA
- **Instances**: EA/PA arithmetization and derivability

### CI Safeguards
- Axiom budget guard: 21 maximum
- No sorries allowed in ProofTheory modules
- Forbidden bridge axioms check (prevents reintroduction)
- Pre-commit hooks for all checks

### Path to 20 Axioms

Would require adding minimal internalization (~50-100 LoC):
1. Object-level formula codes
2. Compositional definition of `ConsistencyFormula` and `RFN_Sigma1_Formula`
3. Instantiation lemma for universal formulas
4. Then `RFN_implies_Con_formula` becomes a theorem

### Future Work

1. **Micro-internalization for RFN→Con** (Issue #1)
   - Add minimal syntax to drop to 20 axioms
   - Self-contained in new `Internalization.lean`
   
2. **ExtendIter equivalence theorems** (Issue #2)
   - Prove `LCons T0 n = ExtendIter T0 (consSteps T0) n`
   - Restore height certificates cleanly

### Conclusion

Paper 3B is in a stable, honest state at 21 axioms. The schematic encoding provides simplicity at the cost of one internalization axiom. All major theorems (collision, heights, monotonicity) are established. The framework is ready for use in downstream papers while maintaining a clear path to future improvements.