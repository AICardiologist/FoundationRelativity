# Paper 2 Dependency Documentation

**Generated**: August 13, 2025  
**Purpose**: Complete dependency analysis for Paper 2 BidualGap proofs

## 1. Forward Dependency Tree (Top-Down)

### Main Theorem
```
gap_equiv_wlpo : BidualGapStrong.{0} ↔ WLPO
├── Location: HB/WLPO_to_Gap_HB.lean
├── Status: ✅ Complete (0 sorries)
└── Axioms: [propext, Classical.choice, Quot.sound, 
             dual_is_banach_c0_from_WLPO, dual_is_banach_c0_dual_from_WLPO]
```

### Forward Direction Dependencies
```
gap_implies_wlpo : BidualGapStrong → WLPO
├── Location: HB/WLPO_to_Gap_HB.lean:22
├── Delegates to: Papers.P2.Constructive.WLPO_of_gap
└── Dependencies:
    └── WLPO_of_gap : BidualGapStrong → WLPO
        ├── Location: Constructive/Ishihara.lean:227
        ├── Status: ✅ Complete (0 sorries)
        ├── Axioms: [propext, Classical.choice, Quot.sound]
        └── Dependencies:
            ├── Papers.P2_BidualGap.Basic (definitions)
            └── Papers.P2_BidualGap.Constructive.DualStructure
                └── Only uses definitions (no sorry lemmas):
                    ├── OpNorm.HasOpNorm
                    ├── OpNorm.UnitBall
                    └── OpNorm.valueSet
```

### Reverse Direction Dependencies
```
wlpo_implies_gap : WLPO → BidualGapStrong.{0}
├── Location: HB/WLPO_to_Gap_HB.lean:88
├── Status: ✅ Complete (uses axioms)
├── Key Construction: Direct witness G = S ∘ Φ₁ in c₀**
└── Dependencies:
    └── Papers.P2_BidualGap.HB.DirectDual
        ├── Status: ✅ Complete (0 sorries)
        ├── Provides: Standard basis e, coordinate functionals δ, witness G
        └── Dependencies:
            ├── Papers.P2_BidualGap.HB.SimpleFacts
            └── Papers.P2_BidualGap.Basic
```

### Quotient Framework Dependencies
```
iotaBar_injective : Function.Injective iotaBar
├── Location: Gap/Quotients.lean:707
├── Status: ✅ Complete (0 sorries)
├── Key Technique: ε=1/2 contradiction argument
└── Dependencies:
    ├── BooleanAtInfinity (quotient type 𝒫(ℕ)/Fin)
    ├── SeqModC0 (quotient type ℝ^ℕ/c₀)
    └── Supporting modules:
        ├── Gap/Indicator.lean (χ characteristic functions)
        ├── Gap/IndicatorSpec.lean (c₀-spec equivalence)
        ├── Gap/C0Spec.lean (tail smallness characterization)
        └── Gap/Iota.lean (ι embedding and lattice homomorphism)
```

## 2. Reverse Dependency Tree (Bottom-Up)

### Base Definitions Layer
```
Papers.P2_BidualGap.Basic
├── Defines: BidualGapStrong, WLPO, DualIsBanach
├── Universe: Type u (polymorphic)
└── Used by:
    ├── Constructive/Ishihara.lean
    ├── HB/WLPO_to_Gap_HB.lean
    ├── HB/DirectDual.lean
    └── HB/SimpleFacts.lean
```

### Indicator Theory Layer
```
Gap/Indicator.lean
├── Defines: chi (characteristic functions)
├── Properties: Basic arithmetic of indicators
└── Used by:
    ├── Gap/IndicatorSpec.lean
    └── Gap/Quotients.lean

Gap/IndicatorSpec.lean
├── Defines: c₀Spec predicate
├── Key theorem: finite △ ↔ c₀Spec
└── Used by:
    └── Gap/Quotients.lean

Gap/C0Spec.lean
├── Defines: EqModC0Spec equivalence
├── Properties: Tail smallness characterization
└── Used by:
    └── Gap/Quotients.lean

Gap/Iota.lean
├── Defines: ι : Set ℕ → (ℕ → ℝ)
├── Properties: Lattice homomorphism laws
└── Used by:
    └── Gap/Quotients.lean
```

### Constructive Layer
```
Constructive/DualStructure.lean
├── Defines: OpNorm.HasOpNorm, UnitBall, valueSet
├── Contains: 4 obsolete lemmas with sorries (marked deprecated)
├── Note: Only definitions used, not sorry lemmas
└── Used by:
    └── Constructive/Ishihara.lean
        └── Used by: HB/WLPO_to_Gap_HB.lean
```

### HB (Hahn-Banach Alternative) Layer
```
HB/SimpleFacts.lean
├── Provides: Basic facts about c₀ and ℓ∞
└── Used by:
    ├── HB/DirectDual.lean
    └── HB/WLPO_to_Gap_HB.lean

HB/DirectDual.lean
├── Defines: e (basis), δ (coordinate functionals), G (witness)
├── Status: ✅ Complete (0 sorries)
└── Used by:
    └── HB/WLPO_to_Gap_HB.lean
```

## 3. Files with Sorries (Status Report)

### Active Files with Sorries
- **Constructive/DualStructure.lean**: 4 sorries in obsolete lemmas (marked @[deprecated])
  - `hasOperatorNorm_to_hasOpNorm` - NOT USED
  - `hasOpNorm_to_hasOperatorNorm` - NOT USED  
  - `lub_exists_for_valueSet_of_WLPO` - NOT USED
  - Note: Only clean definitions are used by Ishihara.lean

### Obsolete Files (Should be removed/archived)
- **WLPO_Equiv_Gap.lean**: 1 sorry (old stub, superseded by HB/WLPO_to_Gap_HB)
- **test/Axioms.lean**: 1 sorry (old test file)
- **Constructive/CReal_obsolete/**: Multiple sorries (obsolete CReal construction)

## 4. Compilation Order

For a clean build from scratch:

1. **Base layer**: Basic.lean
2. **Indicator theory**: Indicator → IndicatorSpec → C0Spec → Iota
3. **Constructive definitions**: DualStructure.lean (definitions only)
4. **HB constructions**: SimpleFacts → DirectDual
5. **Main proofs**: Ishihara → WLPO_to_Gap_HB
6. **Quotient framework**: Quotients (can build in parallel)

## 5. Key Insights

### Clean Theorem Chain
The main theorem `gap_equiv_wlpo` is completely clean:
- Forward direction uses Ishihara's constructive argument
- Reverse direction uses direct construction G = S ∘ Φ₁
- No sorry contamination in the proof chain

### Obsolete Code Isolation
The 4 sorries in DualStructure.lean are in lemmas that:
- Were part of an earlier bridging approach
- Are marked @[deprecated]
- Are NOT used by any active proof

### Modular Architecture
The codebase has clear separation:
- **Gap/**: Quotient and indicator framework (Sprint A-B work)
- **HB/**: Direct construction approach (Sprint D work)
- **Constructive/**: WLPO ⇒ Gap direction (original approach)

## 6. Testing Coverage

### Files with Test Suites
- Gap/QuotientsTests.lean
- Gap/IndicatorSpecTests.lean
- Gap/IndicatorEventualTests.lean
- Gap/C0SpecTests.lean
- Gap/IotaTests.lean
- Gap/BooleanSubLatticeTests.lean

### Main Theorem Verification
```lean
import Papers.P2_BidualGap.HB.WLPO_to_Gap_HB
open Papers.P2.HB
#check gap_equiv_wlpo  -- Should show: BidualGapStrong ↔ WLPO
#print axioms gap_equiv_wlpo  -- Should show only standard axioms + dual_is_banach assumptions
```