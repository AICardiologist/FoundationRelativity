# DIAGNOSTIC: δ-Insertion Error at Line 9283 - Need JP/Paul Guidance

**Date**: November 5, 2025
**Context**: Priority 3 (δ-insertion) - Error at line 9283 (baseline 9250 + 33 line shift)
**Status**: ⏸ **BLOCKED** - Need guidance on proof strategy

---

## Executive Summary

After successfully completing Priorities 1 (commute/pack cluster) and 2 (derivative goals), I've hit a blocker on Priority 3 (δ-insertion error at line 9283).

**Problem**: The `branches_sum` calc proof at line 9283 fails with "unsolved goals" when trying to apply `rw [← hb, ← ha]`.

**Root Cause**: The lemmas `hb` and `ha` (defined at lines 8831-9039 and 9052-9253) have intermediate calc steps that produce terms like `- sumIdx(...) + rho_core_b`, but their final stated equalities omit the `+ rho_core_b/a` terms. The `branches_sum` proof needs these intermediate forms, not the final forms.

**Request**: Clarification on whether:
1. The proof structure needs to be reorganized to expose intermediate results, OR
2. We need separate lemmas for the "with rho_core" forms, OR
3. There's a different approach to δ-insertion that I'm missing

---

## Error Details

### Location: Riemann.lean:9283

**Error Type**: `unsolved goals`

**Failing Code**:
```lean
have branches_sum :
    (sumIdx B_b)
  - sumIdx (fun ρ => (Γtot M r θ ρ μ a) * (nabla_g M r θ ν ρ b))
  + sumIdx (fun ρ => (Γtot M r θ ρ ν a) * (nabla_g M r θ μ ρ b))
  + (sumIdx B_a)
  - sumIdx (fun ρ => (Γtot M r θ ρ μ b) * (nabla_g M r θ ν a ρ))
  + sumIdx (fun ρ => (Γtot M r θ ρ ν b) * (nabla_g M r θ μ a ρ))
  =
    - sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ)
  - sumIdx (fun ρ => RiemannUp M r θ ρ b μ ν * g M a ρ r θ) := by
  calc
    _ = ( - sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ) + rho_core_b )
      + ( - sumIdx (fun ρ => RiemannUp M r θ ρ b μ ν * g M a ρ r θ) + rho_core_a ) := by
      rw [← hb, ← ha]  -- ❌ FAILS HERE: unsolved goals
```

---

## Analysis

### What `hb` and `ha` Actually Prove

**From goal state inspection**, the lemmas have these signatures:

```lean
hb :
  ((sumIdx B_b - sumIdx fun ρ => Γtot M r θ ρ μ a * nabla_g M r θ ν ρ b) +
      sumIdx fun ρ => Γtot M r θ ρ ν a * nabla_g M r θ μ ρ b) =
    -sumIdx fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ
    -- ❌ NO "+ rho_core_b" here

ha :
  ((sumIdx B_a - sumIdx fun ρ => Γtot M r θ ρ μ b * nabla_g M r θ ν a ρ) +
      sumIdx fun ρ => Γtot M r θ ρ ν b * nabla_g M r θ μ a ρ) =
    -sumIdx fun ρ => RiemannUp M r θ ρ b μ ν * g M a ρ r θ
    -- ❌ NO "+ rho_core_a" here
```

### What the Proof Needs

The `branches_sum` calc proof needs to rewrite the LHS to produce:

```lean
( - sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ) + rho_core_b )
+ ( - sumIdx (fun ρ => RiemannUp M r θ ρ b μ ν * g M a ρ r θ) + rho_core_a )
```

So it needs the "with rho_core" forms, not the final forms.

### Intermediate Calc Steps Exist But Aren't Exposed

Looking at the `hb` definition (lines 8831-9039), there's an intermediate calc step at lines 9025-9039:

```lean
calc
  (sumIdx B_b)
- sumIdx (fun ρ => (Γtot M r θ ρ μ a) * (nabla_g M r θ ν ρ b))
+ sumIdx (fun ρ => (Γtot M r θ ρ ν a) * (nabla_g M r θ μ ρ b))
    = sumIdx (fun ρ => ...) := by ...  -- [step 1]
  _ = - sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ)
    + rho_core_b := by ...  -- ✅ THIS is what we need!
```

But this is buried inside the `hb` calc chain and not accessible as a separate lemma.

---

## Proposed Fix Strategies

### Option A: Extract Intermediate Lemmas ✅ (Recommended)

Create separate lemmas that expose the "with rho_core" forms:

```lean
have hb_with_rho :
  (sumIdx B_b)
  - sumIdx (fun ρ => (Γtot M r θ ρ μ a) * (nabla_g M r θ ν ρ b))
  + sumIdx (fun ρ => (Γtot M r θ ρ ν a) * (nabla_g M r θ μ ρ b))
  = - sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ)
    + rho_core_b := by
  -- [copy the proof from hb's calc chain]

have ha_with_rho :
  (sumIdx B_a)
  - sumIdx (fun ρ => (Γtot M r θ ρ μ b) * (nabla_g M r θ ν a ρ))
  + sumIdx (fun ρ => (Γtot M r θ ρ ν b) * (nabla_g M r θ μ a ρ))
  = - sumIdx (fun ρ => RiemannUp M r θ ρ b μ ν * g M a ρ r θ)
    + rho_core_a := by
  -- [copy the proof from ha's calc chain]
```

Then use `hb_with_rho` and `ha_with_rho` instead of `hb` and `ha` at line 9284.

**Pros**: Clean, minimal changes to existing proofs
**Cons**: Duplicates some proof structure

---

### Option B: Restructure `hb` and `ha` to Return "With Rho" Forms

Change the final equality of `hb` and `ha` to include the rho_core terms:

```lean
have hb :
  (sumIdx B_b)
  - sumIdx (fun ρ => (Γtot M r θ ρ μ a) * (nabla_g M r θ ν ρ b))
  + sumIdx (fun ρ => (Γtot M r θ ρ ν a) * (nabla_g M r θ μ ρ b))
  = - sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ)
    + rho_core_b := by
  -- [existing proof, stopping at the "with rho_core" step]
```

Then add separate "collapsed" lemmas if needed elsewhere:

```lean
have hb_collapsed :
  ... = - sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ) := by
  rw [hb]
  rw [diag_cancel_b]  -- if rho_core_b = 0
  ring
```

**Pros**: More accurate to the intermediate mathematical steps
**Cons**: May break downstream code that uses `hb` and `ha`

---

### Option C: Use Calc Transitivity Directly

Instead of `rw [← hb, ← ha]`, manually inline the calc steps:

```lean
calc
  _ = (sumIdx B_b - sumIdx (fun ρ => ...) + sumIdx (fun ρ => ...))
    + (sumIdx B_a - sumIdx (fun ρ => ...) + sumIdx (fun ρ => ...)) := by
    ring  -- regroup terms
  _ = (- sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ) + rho_core_b)
    + (- sumIdx (fun ρ => RiemannUp M r θ ρ b μ ν * g M a ρ r θ) + rho_core_a) := by
    congr 1
    · [inline hb proof steps]
    · [inline ha proof steps]
```

**Pros**: No need to extract or restructure lemmas
**Cons**: Verbose, duplicates proof logic

---

## Paul's Original Guidance

From Paul's Priority 3:
> **Priority 3: finish δ-insertion contractions**
> - 9250 (now ~9283 after shifts): Use `insert_delta_right_diag`/`insert_delta_left_diag` and collapse remaining deltas

**Observation**: The `insert_delta_right_diag` and `insert_delta_left_diag` are already being used correctly in the `hb` and `ha` proofs (lines 8978 and 9200). The issue isn't with δ-insertion itself, but with how the proof is trying to compose these results.

**Question for Paul**: Is the current proof structure (with rho_core terms appearing and then canceling) the intended design? Or should the δ-insertion produce a different form that doesn't require intermediate rho_core tracking?

---

## Current Progress

**Completed**:
- ✅ Priority 1 (commute/pack cluster): 7 errors eliminated
- ✅ Priority 2 (derivative goals): 2 errors eliminated
- Total errors: 22 → 18 (via Steps 1-8)

**Blocked**:
- ⏸ Priority 3 (δ-insertion): Error 9283 needs proof strategy clarification

---

## Request

**JP/Paul**: Please advise on:

1. **Which fix strategy** (A, B, or C) is architecturally preferred?
2. **Whether the rho_core tracking** is intentional or can be simplified?
3. **If there's a different approach** to δ-insertion I should be using?

Once I have guidance, I can implement the fix and continue with the remaining errors.

---

## Files Involved

**Riemann.lean**:
- Lines 8831-9039: `hb` definition (b-branch with δ-insertion)
- Lines 9052-9253: `ha` definition (a-branch with δ-insertion)
- Lines 9255-9268: `diag_cancel` (proves rho_core_b + rho_core_a = 0)
- Lines 9270-9291: `branches_sum` (FAILS at line 9283)

**Build Log**: `build_step8_final_nov4.txt`

---

**STATUS**: Awaiting guidance before proceeding with Priority 3 fix.
