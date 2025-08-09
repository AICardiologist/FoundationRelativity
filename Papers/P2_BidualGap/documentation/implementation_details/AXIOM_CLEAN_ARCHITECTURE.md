# Axiom-Clean Architecture: Gap → WLPO Implementation

## Overview

The axiom-clean implementation of `WLPO_of_gap : BidualGapStrong → WLPO` achieved a major breakthrough by using a **direct Prop-level proof** that avoids complex witness extraction and infrastructure dependencies.

## Key Innovation: Direct Prop-Level Approach

### Previous Challenge
Earlier attempts used complex constructive real number frameworks and quotient constructions that:
- Required extensive infrastructure (CReal, quotient operations)
- Hit Prop→Type elimination issues when extracting witnesses  
- Suffered from mathlib API version drift
- Had universe metavariable complications

### Breakthrough Solution
The axiom-clean implementation uses a **direct construction in Prop**:

```lean
theorem WLPO_of_gap (hGap : BidualGapStrong) : WLPO := by
  classical
  -- Direct proof without witness extraction
```

## Architecture Components

### 1. Core Definitions (`Basic.lean`)
```lean
-- Strong bidual gap condition  
def BidualGapStrong : Prop :=
  ∃ (X : Type*) (_ : NormedAddCommGroup X) (_ : NormedSpace ℝ X) (_ : CompleteSpace X),
    DualIsBanach X ∧ DualIsBanach (X →L[ℝ] ℝ) ∧
    ¬ Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X)

-- Weak Limited Principle of Omniscience
def WLPO : Prop :=
  ∀ (α : ℕ → Bool), (∀ n, α n = false) ∨ ¬ (∀ n, α n = false)
```

### 2. Helper Lemmas (`Constructive/Ishihara.lean`)

#### Approximate Supremum Selection
```lean
lemma exists_on_unitBall_gt_half_opNorm {E} [NormedAddCommGroup E] [NormedSpace ℝ E] 
  [CompleteSpace E] (T : E →L[ℝ] ℝ) (hT : T ≠ 0) :
  ∃ x : E, ‖x‖ ≤ 1 ∧ (‖T‖ / 2) < ‖T x‖
```

**Key Features**:
- Uses contradiction approach with global bounds
- Avoids fragile API patterns through explicit calc chains
- Robust across mathlib versions

#### Operator Norm Existence  
```lean
lemma hasOpNorm_CLF {X} [NormedAddCommGroup X] [NormedSpace ℝ X] (h : X →L[ℝ] ℝ) :
  OpNorm.HasOpNorm (X:=X) h
```

**Key Features**:
- Uses classical completeness of ℝ via `sSup` and `isLUB_csSup`
- Avoids complex constructive completeness proofs

### 3. Main Theorem Architecture

#### Universe-Polymorphic Kernel
```lean
structure IshiharaKernel (X : Type _) [NormedAddCommGroup X] [NormedSpace ℝ X] where
  y     : (X →L[ℝ] ℝ) →L[ℝ] ℝ     -- Gap element
  f     : X →L[ℝ] ℝ                -- Base functional (zero)
  g     : (ℕ → Bool) → (X →L[ℝ] ℝ)  -- Encoding family
  δ     : ℝ                         -- Uniform gap
  -- Separation and logical properties...
```

**Key Innovation**: Universe polymorphism `Type _` prevents metavariable issues

#### Direct Decision Procedure
```lean  
theorem WLPO_of_kernel {X : Type _} [NormedAddCommGroup X] [NormedSpace ℝ X] 
  [CompleteSpace X] (K : IshiharaKernel X) : WLPO := by
  intro α
  have h := K.sep α  -- |y(f + g α)| = 0 ∨ δ ≤ |y(f + g α)|
  rcases h with h0 | hpos
  -- Decision based on gap separation
```

## Technical Innovations

### 1. API Stabilization Patterns
- **Explicit rewrites** instead of fragile `simp` pattern matching
- **Robust lemma selection** avoiding version-specific names  
- **Universe-safe instantiation** with explicit `(X := X)` parameters

### 2. Axiom Minimization
The proof uses only standard classical axioms:
- `Classical.choice`: Standard axiom of choice
- `propext`: Propositional extensionality  
- `Quot.sound`: Quotient soundness
- **No `sorryAx`**: Completely proof-complete

### 3. Mathlib Version Resistance
- Avoids deprecated function names
- Uses stable core lemmas (`norm_add_le`, `le_opNorm`, etc.)
- Explicit type annotations prevent inference failures

## Verification

### Axiom Checking
```bash
lake env lean Scripts/AxiomCheck.lean

# Output:
# 'Papers.P2.Constructive.WLPO_of_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Build Verification  
```bash
lake build Papers.P2_BidualGap.Constructive.Ishihara
# Should build successfully with only linter warnings
```

## Comparison with Previous Approaches

| Aspect | Previous CReal Approach | Axiom-Clean Approach |
|--------|------------------------|---------------------|
| **Infrastructure** | Complex quotient framework | Direct functional analysis |
| **Axioms** | Unknown (never completed) | Only standard classical |
| **API Dependencies** | Fragile quotient operations | Stable norm/completeness lemmas |
| **Universe Issues** | Metavariable problems | Polymorphic with explicit instantiation |
| **Development Time** | Months of infrastructure | Direct mathematical proof |

## Implications

This architecture demonstrates that:
1. **Direct Prop-level proofs** can avoid complex witness extraction
2. **Careful API selection** provides mathlib version stability
3. **Universe polymorphism** solves metavariable issues elegantly  
4. **Mathematical insight** (approximate supremum) is more powerful than framework complexity

The success suggests that similar direct approaches may work for other foundation-relative results, avoiding the need for extensive constructive infrastructure in classical contexts.