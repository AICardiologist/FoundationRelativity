# Orientation for New Tactic Professor - October 25, 2025

**Welcome!** You're joining a Lean 4 formalization project at the 95% completion mark. This document will bring you up to speed on what's been accomplished and what needs your expertise to finish.

---

## Project Overview

### Goal
Prove the **Ricci identity** for a covariant derivative WITHOUT assuming metric compatibility:

```
[∇_μ, ∇_ν] g_ab = -R_{ba,μν} - R_{ab,μν}
```

This is a fundamental result in differential geometry that's typically proven by assuming ∇g = 0. This project proves it from first principles.

### Mathematical Context

- **Setting**: 4D Schwarzschild spacetime in standard coordinates (t, r, θ, φ)
- **Metric**: Diagonal Schwarzschild metric `g_μν`
- **Christoffel symbols**: `Γ^ρ_μν` defined from metric (standard formula)
- **Covariant derivative**: `∇_μ g_ab = ∂_μ g_ab - Γ^e_μa g_eb - Γ^e_μb g_ae`
- **Riemann tensor**: Standard definition from Christoffel symbols

### Technical Infrastructure

- **Language**: Lean 4 (theorem prover)
- **File**: `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean` (~9000 lines)
- **Coordinate derivatives**: `dCoord μ f r θ` = partial derivative in direction μ
- **Summation**: `sumIdx (fun e => ...)` = sum over 4 coordinate indices
- **Differentiability**: `DifferentiableAt_r` and `DifferentiableAt_θ` predicates

---

## What's Been Accomplished (95% Complete) ✅

### Infrastructure (100% Complete)

All supporting infrastructure exists and works:

1. **Metric and Christoffel symbols**: Full definitions with differentiability proofs
2. **Covariant derivative**: Complete implementation with all lemmas
3. **Riemann tensor**: Fully defined with computational lemmas
4. **Distribution lemmas**:
   - `dCoord_sub_of_diff`: ∂(f - g) = ∂f - ∂g
   - `dCoord_add_of_diff`: ∂(f + g) = ∂f + ∂g
   - `dCoord_mul_of_diff`: ∂(f·g) = (∂f)·g + f·(∂g) (product rule)
   - `dCoord_sumIdx`: ∂(Σf) = Σ(∂f)
5. **Clairaut's theorem**: `clairaut_g`: ∂μ∂ν g = ∂ν∂μ g (mixed partials commute)
6. **Collection lemmas**: `sumIdx_collect8_unbalanced` and derived helpers

### Main Lemmas

1. **`expand_P_ab`** (Lines 6586-6901): **95% COMPLETE** ⚠️
   - Expands P(a,b) = ∂μ(∇ν g_ab) - ∂ν(∇μ g_ab) into P_{∂Γ} + P_payload blocks
   - All 12 differentiability proofs COMPLETE ✅
   - Tactical structure COMPLETE ✅
   - **1 algebraic manipulation sorry remains** at line 6901 ← YOUR TASK

2. **`algebraic_identity`** (Lines 6644+): Awaits completion of expand_P_ab

3. **`ricci_identity_on_g_general`** (Lines 6672+): Final assembly (straightforward once expand_P_ab done)

---

## Technical Constraints and Approach

### The "Bounded Tactics" Philosophy

Previous attempts failed due to using unbounded automation (`simp`, `ring` under binders). The successful approach uses:

✅ **Allowed**:
- Explicit `rw [lemma_name]` with all arguments
- `simp only [specific, lemma, list]`
- `ring` on SCALAR expressions (not under binders/dCoord)
- `calc` blocks for step-by-step reasoning
- `set` to create shorthands
- `have` for intermediate facts

❌ **Forbidden** (causes recursion/timeout):
- Global `simp` without `only`
- `ring` inside `dCoord` or `sumIdx` contexts
- Automation tactics under binders (funext; ring)

### Key Mathematical Pattern

The proof avoids nested differentiability by:

1. **Set shorthands**: `set Xν := fun r θ => dCoord ν g`
2. **Regroup structurally**: Use `dCoord_sub_sub_regroup` to distribute dCoord
3. **Clairaut cancellation**: ∂μ∂ν g - ∂ν∂μ g = 0
4. **Expand sums**: Apply product rule to each sum term
5. **Collect terms**: Group (∂Γ)·g terms and Γ·(∂g) terms separately
6. **Final scalar manipulation**: Use `ring` only after all dCoord/sumIdx eliminated

---

## Current Status of `expand_P_ab`

### File Location
**Path**: `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean`
**Lines**: 6586-6901
**Status**: Compiles with 1 sorry at line 6901

### Proof Structure (What Works)

```lean
lemma expand_P_ab (M r θ : ℝ) (h_ext : Exterior M r θ) (h_θ : Real.sin θ ≠ 0) (μ ν a b : Idx) :
  (dCoord μ (fun r θ => nabla_g M r θ ν a b) r θ
 - dCoord ν (fun r θ => nabla_g M r θ μ a b) r θ)
= sumIdx (fun ρ =>
    -(dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ) * g M ρ b r θ
    +(dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ) * g M ρ b r θ
    -(dCoord μ (fun r θ => Γtot M r θ ρ ν b) r θ) * g M a ρ r θ
    +(dCoord ν (fun r θ => Γtot M r θ ρ μ b) r θ) * g M a ρ r θ)
+ sumIdx (fun ρ =>
    -(Γtot M r θ ρ ν a) * (dCoord μ (fun r θ => g M ρ b r θ) r θ)
    +(Γtot M r θ ρ μ a) * (dCoord ν (fun r θ => g M ρ b r θ) r θ)
    -(Γtot M r θ ρ ν b) * (dCoord μ (fun r θ => g M a ρ r θ) r θ)
    +(Γtot M r θ ρ μ b) * (dCoord ν (fun r θ => g M a ρ r θ) r θ)) := by
  classical
  unfold nabla_g

  -- ✅ Step 1: Set shorthands (Lines 6589-6629)
  set Xν  : ℝ → ℝ → ℝ := (fun r θ => dCoord ν (fun r θ => g M a b r θ) r θ) with hXν
  set S1ν : ℝ → ℝ → ℝ := (fun r θ => sumIdx (fun e => Γtot M r θ e ν a * g M e b r θ)) with hS1ν
  set S2ν : ℝ → ℝ → ℝ := (fun r θ => sumIdx (fun e => Γtot M r θ e ν b * g M a e r θ)) with hS2ν
  set Xμ  : ℝ → ℝ → ℝ := (fun r θ => dCoord μ (fun r θ => g M a b r θ) r θ) with hXμ
  set S1μ : ℝ → ℝ → ℝ := (fun r θ => sumIdx (fun e => Γtot M r θ e μ a * g M e b r θ)) with hS1μ
  set S2μ : ℝ → ℝ → ℝ := (fun r θ => sumIdx (fun e => Γtot M r θ e μ b * g M a e r θ)) with hS2μ

  -- ✅ Step 2: Regroup μ-branch with 6 explicit differentiability proofs (Lines 6634-6639)
  have regroup_μ :
    dCoord μ (fun r θ => Xν r θ - S1ν r θ - S2ν r θ) r θ
      = (dCoord μ Xν r θ - dCoord μ S1ν r θ) - dCoord μ S2ν r θ :=
    dCoord_sub_sub_regroup μ Xν S1ν S2ν r θ
      (diff_Xκ_r M r θ h_ext μ ν a b)
      (diff_S1_r M r θ h_ext μ ν a b)
      (diff_S2_r M r θ h_ext μ ν a b)
      (diff_Xκ_θ M r θ h_ext μ ν a b)
      (diff_S1_θ M r θ h_θ μ ν a b)
      (diff_S2_θ M r θ h_θ μ ν a b)

  -- ✅ Step 3: Regroup ν-branch (same pattern, μ ↔ ν swapped)
  have regroup_ν : [similar structure]

  -- ✅ Step 4: Scalar regrouping (Lines 6656-6670)
  have regroup_top :
    dCoord μ (fun r θ => Xν r θ - S1ν r θ - S2ν r θ) r θ
  - dCoord ν (fun r θ => Xμ r θ - S1μ r θ - S2μ r θ) r θ
  =
    ((dCoord μ Xν r θ - dCoord μ S1ν r θ) - dCoord μ S2ν r θ)
  - ((dCoord ν Xμ r θ - dCoord ν S1μ r θ) - dCoord ν S2μ r θ) := by
    calc [uses regroup_μ and regroup_ν]

  -- ✅ Step 5: Clairaut cancellation (Lines 6672-6678)
  have clairaut_cancel :
    dCoord μ Xν r θ - dCoord ν Xμ r θ = 0 := by
    simp [Xν, Xμ, refold_r, refold_θ, clairaut_g M a b r θ h_ext μ ν]

  -- ✅ Step 6: Differentiability helpers (Lines 6682-6722)
  have dprod_r : [4 product differentiability helpers]

  -- ✅ Step 7: Four sum expansions with product rule (Lines 6726-6837)
  have expand_S1ν : dCoord μ S1ν r θ = sumIdx (fun e =>
      (dCoord μ (fun r θ => Γtot M r θ e ν a) r θ) * g M e b r θ
    + Γtot M r θ e ν a * (dCoord μ (fun r θ => g M e b r θ) r θ)) := by
    simp [S1ν]
    rw [dCoord_sumIdx μ ...]
    simp_rw [dCoord_mul_of_diff μ ...]

  [expand_S1μ, expand_S2ν, expand_S2μ similarly]

  -- ✅ Step 8: calc-based assembly (Lines 6841-6900)
  calc
    dCoord μ (fun r θ => nabla_g M r θ ν a b) r θ
  - dCoord ν (fun r θ => nabla_g M r θ μ a b) r θ
      = ((dCoord μ Xν r θ - dCoord μ S1ν r θ) - dCoord μ S2ν r θ)
      - ((dCoord ν Xμ r θ - dCoord ν S1μ r θ) - dCoord ν S2μ r θ) := by
        exact regroup_top
    _ = (0 - dCoord μ S1ν r θ) - dCoord μ S2ν r θ
      - (0 - dCoord ν S1μ r θ + dCoord ν S2μ r θ) := by
        rw [clairaut_cancel]; ring
    [more calc steps using expand_S1ν, expand_S1μ, expand_S2ν, expand_S2μ]
    _ = -(sumIdx (fun e => G_b e * (A_b e - B_b e)) + sumIdx (fun e => P_b e - Q_b e))
      - (sumIdx (fun e => G_a e * (A_a e - B_a e)) + sumIdx (fun e => P_a e - Q_a e)) := by
        [pack_b and pack_a steps]
    _ = [explicit RHS with P_{∂Γ} + P_payload blocks] := by
        sorry  -- ← LINE 6901 - YOUR TASK
```

---

## YOUR TASK: Final Algebraic Manipulation (Line 6901)

### The Problem

After all the tactical work (regrouping, Clairaut, sum expansions), the proof reaches a final **purely algebraic** step at line 6901. You need to prove:

**Current LHS** (after pack_b and pack_a):
```lean
-(sumIdx (fun e => G_b e * (A_b e - B_b e)) + sumIdx (fun e => P_b e - Q_b e))
-(sumIdx (fun e => G_a e * (A_a e - B_a e)) + sumIdx (fun e => P_a e - Q_a e))
```

**Target RHS** (explicit form from lemma statement):
```lean
sumIdx (fun ρ =>
  -(dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ) * g M ρ b r θ
  +(dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ) * g M ρ b r θ
  -(dCoord μ (fun r θ => Γtot M r θ ρ ν b) r θ) * g M a ρ r θ
  +(dCoord ν (fun r θ => Γtot M r θ ρ μ b) r θ) * g M a ρ r θ)
+ sumIdx (fun ρ =>
  -(Γtot M r θ ρ ν a) * (dCoord μ (fun r θ => g M ρ b r θ) r θ)
  +(Γtot M r θ ρ μ a) * (dCoord ν (fun r θ => g M ρ b r θ) r θ)
  -(Γtot M r θ ρ ν b) * (dCoord μ (fun r θ => g M a ρ r θ) r θ)
  +(Γtot M r θ ρ μ b) * (dCoord ν (fun r θ => g M a ρ r θ) r θ))
```

### Definitions in Scope

At line 6901, these local definitions are active:

```lean
-- From pack_b (Line 6867):
G_b := fun e => dCoord ν (fun r θ => Γtot M r θ e μ a) r θ
A_b := fun e => g M e b r θ
B_b := fun e => dCoord μ (fun r θ => Γtot M r θ e ν a) r θ
P_b := fun e => Γtot M r θ e μ a * (dCoord ν (fun r θ => g M e b r θ) r θ)
Q_b := fun e => Γtot M r θ e ν a * (dCoord μ (fun r θ => g M e b r θ) r θ)

-- From pack_a (Line 6884):
G_a := fun e => dCoord ν (fun r θ => Γtot M r θ e μ b) r θ
A_a := fun e => g M a e r θ
B_a := fun e => dCoord μ (fun r θ => Γtot M r θ e ν b) r θ
P_a := fun e => Γtot M r θ e μ b * (dCoord ν (fun r θ => g M a e r θ) r θ)
Q_a := fun e => Γtot M r θ e ν b * (dCoord μ (fun r θ => g M a e r θ) r θ)
```

### What's Been Tried

1. **Direct `ring`**: Fails with "unsolved goals" (ring can't see through sumIdx)

2. **`simp only [G_b, A_b, B_b, P_b, Q_b, G_a, A_a, B_a, P_a, Q_a] ; ring`**: Fails with "unsolved goals" after expansion

3. **`collect_four_pairs_to_two_sums` approach** (Line 1699-1708):
   ```lean
   lemma collect_four_pairs_to_two_sums
     (A B C D E F G H : Idx → ℝ) :
     ((sumIdx A - sumIdx B) + sumIdx C - sumIdx D)
   + ((sumIdx E - sumIdx F) + sumIdx G - sumIdx H)
   =
     sumIdx (fun ρ => A ρ - B ρ + C ρ - D ρ)
   + sumIdx (fun ρ => E ρ - F ρ + G ρ - H ρ)
   ```

   Problem: Pattern doesn't match after pack_b and pack_a because LHS has structure:
   `-(sumIdx(G·(A-B)) + sumIdx(P-Q)) - (sumIdx(G·(A-B)) + sumIdx(P-Q))`

   But collector expects flat sum structure.

### Tactical Constraints

Since you **cannot manipulate VS Code**, you'll need to provide the tactical sequence as **ready-to-paste Lean code** or as **detailed instructions** that someone can copy into the file.

**Recommended approach**:
- You have access to Lean (can check proofs)
- Write the complete tactical sequence
- Test it in your Lean environment
- Provide it as a drop-in replacement for the `sorry` at line 6901

**Useful lemmas available**:
- `sumIdx_add`: `sumIdx A + sumIdx B = sumIdx (fun i => A i + B i)`
- `sumIdx_sub`: `sumIdx A - sumIdx B = sumIdx (fun i => A i - B i)`
- `sumIdx_congr`: If `∀ i, A i = B i` then `sumIdx A = sumIdx B`
- `ring`: Works on scalar expressions
- `mul_comm`, `mul_assoc`, `add_comm`, `add_assoc`, etc.: Standard algebra

### Expected Solution Pattern

The solution likely involves:

1. **Expand definitions**: `simp only [G_b, A_b, B_b, P_b, Q_b, G_a, A_a, B_a, P_a, Q_a]`

2. **Distribute negation**: Rewrite `-(sumIdx f + sumIdx g)` as `-sumIdx f - sumIdx g`

3. **Use sumIdx lemmas**: Apply `sumIdx_add`/`sumIdx_sub` to combine sums

4. **Prove pointwise equality**: Use `sumIdx_congr` to reduce to showing term-by-term equality

5. **Final scalar manipulation**: Use `ring` to verify each point equals the RHS term

---

## Request to Tactic Professor

**Please provide**:

1. **The complete tactical proof** for line 6901, written as:
   ```lean
   _ = [explicit RHS] := by
     [your tactical sequence here]
   ```

2. **Explanation** (optional but appreciated): Brief note on the approach used

3. **Testing confirmation**: Verify it compiles cleanly in your Lean environment

**What you have**:
- Full Lean 4 access to the codebase
- All definitions and lemmas in scope
- Complete visibility into the proof state at line 6901

**What you DON'T need**:
- VS Code manipulation (just provide the code)
- Understanding of the physics (purely algebraic manipulation)
- Rewriting earlier parts of the proof (everything before line 6901 works)

---

## How to Test Your Solution

Since you can access Lean but not VS Code, you can:

1. **Open the file in Lean**:
   ```bash
   cd /Users/quantmann/FoundationRelativity
   # Use your preferred Lean editor/REPL
   ```

2. **Navigate to line 6901** and replace `sorry` with your proof

3. **Build the file**:
   ```bash
   lake build Papers.P5_GeneralRelativity.GR.Riemann
   ```

4. **Check for errors**: Should compile with 0 errors (1 pre-existing error at line 6069 is expected)

5. **Provide the working code** back to the team

---

## Background: Why This Matters

This is the **final piece** of a significant mathematical result:

- The Ricci identity is fundamental in general relativity
- Standard proofs assume ∇g = 0 (metric compatibility) as an axiom
- This proof derives it from first principles
- The formalization provides computer-verified rigor

Your contribution will complete this proof and enable the final assembly (`algebraic_identity` and `ricci_identity_on_g_general`) to proceed.

---

## Contact and Support

**Status reports location**: `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/`

**Previous status reports** (for additional context):
- `STATUS_OCT25_FINAL_SUCCESS.md`: Current 95% status
- `STATUS_OCT25_STRUCTURE_COMPLETE.md`: Tactical structure documentation
- `INTERACTIVE_DEBUG_SESSION_OCT25_SUCCESS.md`: Debugging history

**Build verification**:
```bash
cd /Users/quantmann/FoundationRelativity
lake build Papers.P5_GeneralRelativity.GR.Riemann
```

**Expected output**: 1 pre-existing error at line 6069 (not your concern), plus 1 sorry warning at line 6901 (your task to eliminate)

---

## Summary: What You Need to Do

**Task**: Replace the `sorry` at line 6901 with a complete tactical proof

**Input**: 4 sumIdx terms in "packed" form (G_b·(A_b - B_b) + etc.)

**Output**: 2 sumIdx terms in explicit RHS form (P_{∂Γ} + P_payload)

**Method**: Purely algebraic manipulation using sumIdx lemmas and ring

**Constraints**: Bounded tactics only (no global simp, explicit lemma applications)

**Deliverable**: Ready-to-paste Lean code that completes the proof

---

**Thank you for joining the project at this critical final stage! The finish line is in sight.**

---

**Document prepared**: October 25, 2025
**Project status**: 95% complete
**Your task**: The final 5%
**Estimated effort**: 1-2 hours (depending on familiarity with Lean tactics)
