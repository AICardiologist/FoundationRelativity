# DIAGNOSTIC: Lemma Exists But simpa Triggers HasDistribNeg - November 10, 2025

**Status**: ⚠️ **LEMMA EXISTS** - But simpa normalization triggers HasDistribNeg recursion
**For**: Paul (Senior Professor)
**From**: Claude Code (Section 1 investigation)
**Result**: 16 errors (no improvement), HasDistribNeg at line 8904

---

## Executive Summary

Applied Paul's final fix exactly as specified. The lemma `insert_delta_right_diag_neg` **DOES EXIST** in Riemann.lean (line 1799). Build completes without "unknown identifier" errors, confirming the lemma is found. However, the `simpa` tactic at line 8904 triggers HasDistribNeg synthesis failure with maximum recursion depth.

**Root Cause Hypothesis**: When `simpa` unfolds `F` and applies `flip_neg_prod`, it attempts to distribute negation through the complex payload expression, triggering HasDistribNeg typeclass search that recurses infinitely.

---

## Finding: Lemmas Exist in Riemann.lean

**Search Results**:
```bash
$ grep -n "insert_delta_right_diag_neg\|insert_delta_left_diag_neg\|flip_neg_prod" Riemann.lean

1787:lemma flip_neg_prod {A B : ℝ} : -(A * B) = (-A) * B := by ring
1799:lemma insert_delta_right_diag_neg
1807:lemma insert_delta_left_diag_neg
8902:        insert_delta_right_diag_neg M r θ b (fun ρ => F ρ)
8904:      simpa [F, flip_neg_prod, mul_comm, mul_left_comm, mul_assoc] using δb
```

**Confirmation**:
- `flip_neg_prod` at line 1787 ✅
- `insert_delta_right_diag_neg` at line 1799 ✅
- `insert_delta_left_diag_neg` at line 1807 ✅
- Used in Paul's fix at lines 8902, 8904 ✅

**Lemma Definition** (lines 1799-1804):
```lean
lemma insert_delta_right_diag_neg
    (M r θ : ℝ) (b : Idx) (F : Idx → ℝ) :
  sumIdx (fun ρ => (-F ρ) * g M ρ b r θ)
    =
  sumIdx (fun ρ => (-F ρ) * g M ρ b r θ * (if ρ = b then 1 else 0)) := by
  exact insert_delta_right_diag M r θ b (fun ρ => -F ρ)
```

**Proof**: Simple wrapper around `insert_delta_right_diag` with negated payload.

---

## Paul's Applied Code (Lines 8893-8904)

```lean
      classical
      -- Name the payload exactly as it appears, to avoid over-simplification under binders.
      let F : Idx → ℝ := fun ρ =>
        ( dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ
        - dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ
        + sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
        - sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) )
      -- Inject the Kronecker δ on the **right** in the presence of the leading minus.
      have δb :=
        insert_delta_right_diag_neg M r θ b (fun ρ => F ρ)
      -- Repackage -(F ρ * g) ↔ (-F ρ) * g pointwise and reassociate.
      simpa [F, flip_neg_prod, mul_comm, mul_left_comm, mul_assoc] using δb
      -- ^^^^ LINE 8904: HasDistribNeg error occurs here
```

**Status**: Code compiles up to line 8904, then fails at `simpa` tactic.

---

## Error at Line 8904

**Full Error**:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8904:6: failed to synthesize
  HasDistribNeg ℝ
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
```

**Location**: The `simpa` line in Paul's fix (line 8904)

**Not an "unknown identifier" error**: This means `insert_delta_right_diag_neg` was found and its type was unified successfully. The error occurs during simplification/rewriting.

---

## Goal vs Lemma Structure Analysis

### Goal Structure (Lines 8880-8892)

**LHS**:
```lean
sumIdx (fun ρ => -( (F ρ) * g M ρ b r θ ))
```

**RHS**:
```lean
sumIdx (fun ρ => -( (F ρ) * g M ρ b r θ ) * (if ρ = b then 1 else 0))
```

**Pattern**: Outer negation on entire product `-(F ρ * g)`

### What `δb` Produces (From insert_delta_right_diag_neg)

**LHS**:
```lean
sumIdx (fun ρ => (-F ρ) * g M ρ b r θ)
```

**RHS**:
```lean
sumIdx (fun ρ => (-F ρ) * g M ρ b r θ * (if ρ = b then 1 else 0))
```

**Pattern**: Negation on payload only: `(-F ρ) * g`

### Conversion Required

By `flip_neg_prod`: `-(A * B) = (-A) * B`, we need:
```
-(F ρ * g M ρ b r θ)  =  (-F ρ) * g M ρ b r θ
```

This should work IF `F ρ` is treated atomically. But...

---

## Root Cause Hypothesis

### The Problem with Unfolding `F`

**Paul's simpa line**:
```lean
simpa [F, flip_neg_prod, mul_comm, mul_left_comm, mul_assoc] using δb
```

**The `[F, ...]` simp set unfolds the let-binding `F`**, replacing it with:
```lean
dCoord μ ... - dCoord ν ... + sumIdx ... - sumIdx ...
```

**Then `flip_neg_prod` tries to apply**:
```
-(F ρ * g)  →  (-F ρ) * g
```

But now `F ρ` is unfolded to a complex expression with `+` and `-`. To compute `(-F ρ)`, Lean needs to distribute the negation:
```
-(dCoord μ ... - dCoord ν ... + sumIdx ... - sumIdx ...)
  =
(-dCoord μ ...) + (dCoord ν ...) - (sumIdx ...) + (sumIdx ...)
```

**This distribution requires `HasDistribNeg` typeclass**, which triggers infinite recursion!

### Why Paul's Design Should Avoid This

Paul's comment says:
> "Name the payload exactly as it appears, to avoid over-simplification under binders."

This suggests `F` should NOT be unfolded during the proof. But `simpa [F, ...]` explicitly unfolds it!

---

## Comparison with Baseline

**Baseline Error** (line 8901 before Paul's fix):
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8901:6: failed to synthesize
  HasDistribNeg ℝ
maximum recursion depth has been reached
```

**After Paul's Fix** (line 8904):
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8904:6: failed to synthesize
  HasDistribNeg ℝ
maximum recursion depth has been reached
```

**Conclusion**: Same error type, just shifted by +3 lines. Paul's fix didn't resolve the HasDistribNeg issue.

---

## Why Isn't `flip_neg_prod` Working?

**`flip_neg_prod` definition** (line 1787):
```lean
lemma flip_neg_prod {A B : ℝ} : -(A * B) = (-A) * B := by ring
```

**Issue**: This lemma works on **atomic** `A` and `B`. But when `simpa` unfolds `F`, it replaces the atomic `F ρ` with a complex expanded expression. Then:

1. `flip_neg_prod` tries to match `-(F ρ * g)` with `-(A * B)` ✅
2. This requires computing `(-F ρ)` where `F ρ` is now the expanded expression ❌
3. Lean tries to simplify `-(expanded expression)` using distributivity rules
4. This triggers `HasDistribNeg` typeclass search
5. Infinite recursion occurs

---

## Possible Solutions

### Option 1: Don't Unfold `F` in simpa

**Change**:
```lean
-- Before:
simpa [F, flip_neg_prod, mul_comm, mul_left_comm, mul_assoc] using δb

-- After:
simpa [flip_neg_prod, mul_comm, mul_left_comm, mul_assoc] using δb
```

**Rationale**: Keep `F` atomic so `flip_neg_prod` works without distributing negation.

**Risk**: May not fully unify goal with lemma conclusion if some unfolding is needed.

### Option 2: Use `show` to Force Goal Shape First

**Change**:
```lean
have δb := insert_delta_right_diag_neg M r θ b (fun ρ => F ρ)
show sumIdx (fun ρ => -(F ρ * g M ρ b r θ)) =
     sumIdx (fun ρ => -(F ρ * g M ρ b r θ) * (if ρ = b then 1 else 0))
simpa [flip_neg_prod, mul_comm, mul_left_comm, mul_assoc] using δb
```

**Rationale**: Explicitly state goal before applying simplification to control unfolding.

### Option 3: Use `rw` Instead of `simpa`

**Change**:
```lean
have δb := insert_delta_right_diag_neg M r θ b (fun ρ => F ρ)
convert δb using 2
· ext ρ; rw [flip_neg_prod]
· ext ρ; rw [flip_neg_prod, mul_assoc]
```

**Rationale**: Manual rewriting avoids simp's aggressive unfolding and normalization.

### Option 4: Add Explicit Negation Distribution Lemma

**Add to infrastructure**:
```lean
lemma neg_payload_expand (A B C D : ℝ) :
  -(A - B + C - D) = (-A) + B - C + D := by ring
```

**Then**:
```lean
simpa [F, flip_neg_prod, neg_payload_expand, mul_comm, mul_left_comm, mul_assoc] using δb
```

**Rationale**: Provide explicit ring-based distribution to bypass HasDistribNeg.

**Risk**: Still requires unfolding `F`, which might have other issues.

### Option 5: Use `calc` Mode for Explicit Steps

**Change**:
```lean
have δb := insert_delta_right_diag_neg M r θ b (fun ρ => F ρ)
calc
  sumIdx (fun ρ => -(F ρ * g M ρ b r θ))
    = sumIdx (fun ρ => (-F ρ) * g M ρ b r θ) := by
        congr; ext ρ; exact flip_neg_prod
  _ = sumIdx (fun ρ => (-F ρ) * g M ρ b r θ * (if ρ = b then 1 else 0)) := by
        exact δb
  _ = sumIdx (fun ρ => -(F ρ * g M ρ b r θ) * (if ρ = b then 1 else 0)) := by
        congr; ext ρ; exact flip_neg_prod.symm
```

**Rationale**: Explicit steps avoid HasDistribNeg by applying `flip_neg_prod` pointwise without unfolding.

---

## Questions for Paul

1. **Should `F` remain atomic during the simpa step?**
   - Your comment suggests yes, but `simpa [F, ...]` unfolds it
   - Is removing `F` from the simp list the intended fix?

2. **Is there a different δ-insertion lemma we should use?**
   - One that doesn't require flipping negation after the fact?
   - E.g., a lemma that directly handles `-(F ρ * g)` structure?

3. **Should we use a different tactic than simpa?**
   - `convert` with manual `rw`?
   - `calc` mode?
   - Something else?

4. **Is HasDistribNeg recursion a known Lean 4 issue here?**
   - Is there a maxRecDepth setting we should adjust?
   - Or is the issue that we're triggering the wrong typeclass search path?

---

## Build Status

**Error Count**: 16 Riemann.lean errors (no change from baseline)

**Error Lines After Paul's Fix** (+3 shift from baseline):
```
8751, 8904, 8919, 8936, 8940, 8969, 9117, 9132, 9150, 9154, 9195, 9432, 9633, 9647, 9716, 9827
```

**Baseline Error Lines** (for comparison):
```
8751, 8901, 8916, 8933, 8937, 8966, 9114, 9129, 9147, 9151, 9192, 9429, 9630, 9644, 9713, 9824
```

**Line Shift**: +3 lines due to Paul's code (was 9 lines, now 12 lines)

---

## Files

**Main File**: `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean`
**Build Log**: `build_b2pp_section1_paul_final_nov10.txt` (16 errors)
**Lemma Location**: Lines 1787, 1799, 1807 (infrastructure)
**Applied Code**: Lines 8893-8904 (Paul's Section 1 fix)
**Error Location**: Line 8904 (simpa tactic)

---

## Recommended Next Step

**Try Option 1** (remove `F` from simpa list):
```lean
simpa [flip_neg_prod, mul_comm, mul_left_comm, mul_assoc] using δb
```

This keeps `F` atomic, allowing `flip_neg_prod` to work without distributing negation through the complex payload.

If that fails, provide Paul with:
- Exact goal state before line 8904
- Exact type of `δb` before simpa
- Request revised approach (Option 2, 3, 4, or 5 above)

---

**Report Date**: November 10, 2025, ~13:00 UTC
**Agent**: Claude Code (Sonnet 4.5)
**Status**: ⏸ AWAITING PAUL'S REVISED SIMPA - Lemma exists but triggers HasDistribNeg
**Error Count**: 16 (baseline unchanged)
