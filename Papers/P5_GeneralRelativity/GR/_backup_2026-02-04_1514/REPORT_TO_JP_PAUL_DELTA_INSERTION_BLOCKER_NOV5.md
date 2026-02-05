# REPORT TO JP/PAUL: δ-Insertion Blocker - Need Architectural Guidance

**Date**: November 5, 2025
**Status**: 🔴 **BLOCKED** - Attempted fix caused regression (18→20 errors)
**Context**: Phase 2, Priority 3 (δ-insertion) - Error at line ~9193

---

## Executive Summary

I've successfully completed Priorities 1 and 2 (reducing errors from 22→18), but I'm now blocked on Priority 3 (δ-insertion error).

**Problem**: The `branches_sum` proof at line 9193 expects `hb` and `ha` to prove equalities that include intermediate `+ rho_core` terms, but these lemmas appear to not expose those forms in their type signatures.

**Attempted Fix**: I tried adding simple wrapper lemmas `hb_with_rho := hb` and `ha_with_rho := ha`, but this caused a type mismatch error and increased the error count from 18 to 20. I've reverted this change.

**Request**: Need guidance on the correct architectural approach to expose the intermediate "with rho_core" forms.

---

## Progress Report

### ✅ Completed (Steps 1-8)

**Step 6 (Pack→Lemma)**: Eliminated errors 9688, 9702
- Manual pack using `sumIdx_add_distrib.symm` → applied `payload_cancel_all_flipped`
- Pattern: explicit calc chains > placeholder inference

**Step 7 (Commute/Pack Cluster)**: Eliminated 7 errors (8982, 8997, 9014, 9018, 9232)
- Replaced `simpa [neg_mul_right₀]` with explicit `rw` to avoid `HasDistribNeg` recursion
- Used manual `calc` with explicit `ring` instead of `ring` under binders
- Applied `payload_cancel_all_flipped` after packing

**Step 8 (Derivative Goals)**: Eliminated 2 errors (9843, 9954)
- Added missing `dCoord_r_const` infrastructure lemma
- Changed from `simp [h_r, h_θ', dCoord]` to `rw [h_θ', h_r]; simp`
- Key: Keep `dCoord` opaque, substitute zeros first, then apply const lemmas

**Net Progress**: 22 errors → 18 errors (-18.2%)

---

## Current Blocker: Priority 3 (δ-Insertion)

### Error Location: Riemann.lean:9193

**Code**:
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
      rw [← hb, ← ha]  -- ❌ FAILS: unsolved goals
```

**Error**: `unsolved goals` at the `rw [← hb, ← ha]` line

---

## Root Cause Analysis

### What the Proof Needs

The `branches_sum` calc expects `hb` and `ha` to have type signatures:

```lean
hb : LHS_b = RHS_b + rho_core_b
ha : LHS_a = RHS_a + rho_core_a
```

So that `rw [← hb, ← ha]` can rewrite the LHS to include the rho_core terms, which then cancel via `diag_cancel` in the next calc step.

### What `hb` and `ha` Actually Prove

According to the declared type signatures at lines 8831-8836:

```lean
have hb :
  (sumIdx B_b)
  - sumIdx (fun ρ => (Γtot M r θ ρ μ a) * (nabla_g M r θ ν ρ b))
  + sumIdx (fun ρ => (Γtot M r θ ρ ν a) * (nabla_g M r θ μ ρ b))
  =
    - sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ) := by
  -- [calc chain with δ-insertion at lines 8837-9039]
```

**Observation**: The type signature does NOT include `+ rho_core_b`!

### But the calc chain HAS the intermediate form!

Looking at the calc chain inside `hb` (lines 9025-9039):

```lean
_   = - sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ)
    + rho_core_b := by
  simp only [h_rho_core_b]
  rw [h_insert_delta_for_b, ← sumIdx_add_distrib]
  apply sumIdx_congr; intro ρ
  simp only [RiemannUp]
  split_ifs with h_rho_eq_b
  · -- ρ = b case
    subst h_rho_eq_b
    simp only [h_bb_core]
    rw [← scalar_finish_bb]
    ring
  · -- ρ ≠ b case: Kronecker δ = 0
    simp
    ring
```

So the calc chain DOES produce `RHS + rho_core_b` as an intermediate step!

**Key Question**: If the calc proves `LHS = RHS + rho_core_b`, but the type signature of `hb` claims `LHS = RHS`, how does this typecheck? Either:

1. There's another calc step after line 9039 that removes `rho_core_b` (proving `RHS + rho_core_b = RHS` somehow), OR
2. The type signature is wrong, OR
3. I'm misunderstanding the calc chain structure

---

## Attempted Fix & Failure

### What I Tried

Following the diagnostic's "Option A", I added wrapper lemmas:

```lean
have hb_with_rho :
  (sumIdx B_b)
  - sumIdx (fun ρ => (Γtot M r θ ρ μ a) * (nabla_g M r θ ν ρ b))
  + sumIdx (fun ρ => (Γtot M r θ ρ ν a) * (nabla_g M r θ μ ρ b))
  = - sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ)
    + rho_core_b := hb  -- ❌ TYPE MISMATCH

have ha_with_rho :
  (sumIdx B_a)
  - sumIdx (fun ρ => (Γtot M r θ ρ μ b) * (nabla_g M r θ ν a ρ))
  + sumIdx (fun ρ => (Γtot M r θ ρ ν b) * (nabla_g M r θ μ a ρ))
  = - sumIdx (fun ρ => RiemannUp M r θ ρ b μ ν * g M a ρ r θ)
    + rho_core_a := ha  -- ❌ TYPE MISMATCH
```

Then changed line 9193 from `rw [← hb, ← ha]` to `rw [← hb_with_rho, ← ha_with_rho]`.

### Result: Regression

**Build**: Succeeded (exit code 0)
**Error count**: 18 → 20 ❌
**New errors**: Lines 9262, 9269 (type mismatches in wrapper lemmas), 9299 (unsolved goals in rewrite)

**Root cause of failure**: Simple assignment `hb_with_rho := hb` doesn't work because:
- `hb` has type `LHS = RHS`
- `hb_with_rho` declares type `LHS = RHS + rho_core_b`
- These are incompatible types

---

## Questions for JP/Paul

### 1. Architectural Question: What Should `hb` and `ha` Prove?

**Option A**: Should `hb` and `ha` be restructured to prove `LHS = RHS + rho_core` as their FINAL type?

```lean
have hb :
  LHS_b = RHS_b + rho_core_b := by
  -- [existing calc chain up to line 9039]

-- Then add a separate collapsed form if needed elsewhere:
have hb_collapsed : LHS_b = RHS_b := by
  rw [hb, diag_cancel_b_standalone]
  ring
```

**Pros**: More accurate to the intermediate mathematical steps
**Cons**: May break downstream code that uses `hb` and `ha`

---

**Option B**: Should we extract explicit intermediate lemmas with the calc steps copied?

```lean
have hb_with_rho :
  LHS_b = RHS_b + rho_core_b := by
  -- [COPY the proof steps from hb's calc chain, lines 8837-9039]

have ha_with_rho :
  LHS_a = RHS_a + rho_core_a := by
  -- [COPY the proof steps from ha's calc chain]
```

**Pros**: Clean, doesn't modify existing `hb`/`ha`
**Cons**: Duplicates ~200 lines of proof structure

---

**Option C**: Should the `branches_sum` proof be reorganized to NOT need the rho_core forms?

For example, manually inline the δ-insertion steps instead of using `hb` and `ha`:

```lean
calc
  _ = (intermediate_form_b) + (intermediate_form_a) := by
    [inline the relevant parts of hb and ha proofs]
  _ = (RHS_b + rho_core_b) + (RHS_a + rho_core_a) := by
    [δ-insertion steps]
  _ = RHS_b + RHS_a + (rho_core_b + rho_core_a) := by ring
  _ = RHS_b + RHS_a := by rw [diag_cancel]; ring
```

**Pros**: Avoids the type mismatch issue entirely
**Cons**: Verbose, duplicates logic

---

### 2. Clarification Question: calc Chain Structure

Looking at `hb` (lines 8831-9039), I see the calc chain ends at:

```lean
_ = - sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ) + rho_core_b
```

But the TYPE SIGNATURE of `hb` (line 8835-8836) says:

```lean
= - sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ)
```

**Question**: How does this typecheck? Is there a hidden calc step after line 9039 that removes `rho_core_b`? Or does Lean allow the calc to prove "more" than the stated type (e.g., `LHS = RHS + X` satisfies `LHS = RHS` if `X = 0` is known)?

---

### 3. Paul's Original Guidance

From Paul's Priority 3:
> **Priority 3: finish δ-insertion contractions**
> - 9250 (now ~9193 after shifts): Use `insert_delta_right_diag`/`insert_delta_left_diag` and collapse remaining deltas

**Observation**: The `insert_delta_right_diag` and `insert_delta_left_diag` lemmas ARE already being used correctly in the `hb` and `ha` proofs (lines 8978, 9200). The issue isn't with δ-insertion itself, but with how the `branches_sum` proof is trying to compose these results.

**Question**: Is the current proof structure (with rho_core terms appearing and then canceling) the intended design? Or should the δ-insertion produce a different form that doesn't require intermediate rho_core tracking?

---

## Current Status

**Error Count**: 18 (baseline after Steps 1-8)
**Blocker**: δ-insertion error at line 9193
**Action Taken**: Reverted failed fix attempt, back to baseline

**Ready To Proceed**: Once I have guidance on Options A, B, or C (or an alternative approach)

---

## Build Logs

**Baseline (18 errors)**: `build_step8_final_nov4.txt`
**Failed attempt (20 errors)**: `build_step9_delta_insertion_nov5.txt` (now obsolete after revert)

---

## Request

**JP/Paul**: Please advise on:

1. **Which architectural approach** (A, B, C, or other) is preferred?
2. **Why the calc chain typechecks** with the apparent type mismatch?
3. **Whether the rho_core tracking** is intentional or can be simplified?

Once I have this guidance, I can implement the fix cleanly and continue with the remaining errors.

Thank you!

---

**ATTACHMENT**: Diagnostic report with full technical details at:
`DIAGNOSTIC_DELTA_INSERTION_ERROR_9283_NOV5.md`
