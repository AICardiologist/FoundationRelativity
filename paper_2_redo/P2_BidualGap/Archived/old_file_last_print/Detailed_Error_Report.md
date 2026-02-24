# Detailed Error and Sorry Report for QuotSeparation.lean

## 10 Compilation Errors (8 actual + 2 meta)

### 1. **Line 36: Type mismatch in q construction**
```lean
error: type mismatch
  Submodule.mkQ_apply Scl x
has type
  Scl.mkQ x = Submodule.Quotient.mk x : Prop
```
- **Location**: In the proof of norm bound for `LinearMap.mkContinuous`
- **Issue**: The `convert` tactic expects an equality but gets the wrong type

### 2. **Line 48: NormedAddCommGroup instance failure**
```lean
error: type mismatch
  Submodule.Quotient.normedAddCommGroup
has type
  (S : Submodule ?m.34004 ?m.34002) → [hS : IsClosed ↑S] → NormedAddCommGroup (?m.34002 ⧸ S)
```
- **Issue**: Missing `IsClosed` instance for `Scl`

### 3. **Line 51: NormedSpace type mismatch**
```lean
error: type mismatch
  Submodule.Quotient.normedSpace ?m.38677
```
- **Issue**: Wrong type signature for normedSpace

### 4. **Line 51: Application type mismatch**
```lean
error: Application type mismatch: In the application
  Submodule.Quotient.normedSpace ℝ
the argument ℝ
```
- **Issue**: Incorrect argument order or type

### 5. **Line 76: Typeclass instance stuck (metavariables)**
```lean
error: typeclass instance problem is stuck
  NormedSpace ℝ ?m.52268
```
- **Location**: In `exists_extension_norm_eq` call
- **Issue**: Can't infer NormedSpace for the quotient

### 6. **Line 82: Another typeclass instance stuck**
```lean
error: typeclass instance problem is stuck
  NormedSpace ℝ ?m.90226
```
- **Location**: In `g_on_quot_y` proof
- **Issue**: Similar instance inference failure

### 7. **Line 95: Unsolved goals**
```lean
error: unsolved goals
⊢ g_on_quot (q constOne) = 1
```
- **Location**: In `F_constOne` proof
- **Issue**: The simp tactic doesn't close the goal

### 8. **Line 103: Tactic 'assumption' failed**
```lean
error: tactic 'assumption' failed
s : E
hs : s ∈ ↑Scl
this : True
⊢ g_on_quot (sorry s) = 0
```
- **Location**: In `F_vanishes_on_Scl` proof
- **Issue**: Wrong goal state, has `sorry s` instead of proper term

### 9-10. **Meta errors**
- `error: Lean exited with code 1`
- `error: build failed`

## 6 Sorrys with Context

### 1. **Line 25: `isClosed_Scl`**
```lean
lemma isClosed_Scl : IsClosed (Scl : Set E) := by
  -- vanish at ∞ is a closed property in sup norm on ℕ
  sorry
```
- **Purpose**: Prove the topological closure is closed
- **Blocker**: Should be `Submodule.isClosed_topologicalClosure`

### 2. **Line 29: `constOne_not_mem_Scl`**
```lean
lemma constOne_not_mem_Scl : constOne ∉ Scl := by
  -- follows from SimpleFacts Fact A + linearity of toBCF + closure preserves non-membership
  sorry
```
- **Purpose**: Show constant 1 is not in closed span of c₀
- **Blocker**: Needs SimpleFacts + closure argument

### 3. **Line 69: `f₀` definition**
```lean
private noncomputable def f₀ : K →L[ℝ] ℝ := 
  sorry -- Linear functional on span{y} with f₀(y) = 1 and norm bound
```
- **Purpose**: Define functional on 1D subspace span{y}
- **Blocker**: Complex construction with LinearEquiv.toSpanSingleton

### 4. **Line 72: `f₀_y` property**
```lean
private lemma f₀_y : f₀ ⟨y, y_mem⟩ = 1 := 
  sorry -- By construction of f₀
```
- **Purpose**: Verify f₀ sends y to 1
- **Blocker**: Depends on f₀ construction

### 5-6. **Implicit sorrys in proofs**
- In `g_on_quot_y` (line 80-89): Proof incomplete, doesn't establish equality
- In `F_vanishes_on_Scl` (line 98-104): Has a `sorry` term appearing in goal

## Root Causes

1. **Instance resolution failing**: The quotient space instances aren't being found correctly
2. **API mismatch**: The exact signatures in this mathlib version differ from expected
3. **1D functional construction**: The LinearEquiv.toSpanSingleton approach needs careful setup
4. **Type inference**: Lean can't infer types in the HB extension context

## What Would Fix This

1. Add explicit `haveI : IsClosed (Scl : Set E) := isClosed_Scl` before instances
2. Use explicit type annotations in HB extension call
3. Complete the 1D functional construction properly
4. Fix the convert tactic in q construction (use rw instead)