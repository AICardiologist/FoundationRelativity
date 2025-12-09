# Mechanical Triage & Repair Plan for 14 Remaining Errors - November 10, 2025

**Status**: ✅ 14-error baseline restored (16→14 via equality-chaining in Sections 1 & 2)
**For**: Implementation (ready to apply)
**From**: Paul's guidance + Claude Code triage
**Next**: Apply templates systematically to each error site

---

## Summary

Successfully reduced from 16→14 errors by applying Paul's equality-chaining pattern to two δ-insertion sites. The six helpers Paul provided were removed because they used `simpa` internally, which triggered the same HasDistribNeg issues we're avoiding.

**Current state**: 14 errors, all fixable with the same equality-chaining pattern.

---

## Error Inventory (by type)

### Class I: Unsolved Goals (6 errors)
**Lines**: 8751, 8933, 8983, 9169, 9753, 9864
**Cause**: Started `refine sumIdx_congr (fun ρ => ?_)` but didn't finish the pointwise equality
**Fix**: Complete the pointwise goal with explicit `calc` chain

### Class II: Type Mismatch (5 errors)
**Lines**: 8950, 9187, 9469, 9670, 9232
**Cause**: Tried δ-cancellation with `simpa` but payload shape didn't match exactly
**Fix**: Normalize payload pointwise FIRST, then apply δ-cancellation with `.trans`

### Class III: Rewrite Failed (3 errors)
**Lines**: 8954, 9191, 9684
**Cause**: Attempted `rw` outside the binder (can't see inside `fun ρ =>`)
**Fix**: Wrap with `sumIdx_congr` to reach inside the binder

---

## Paste-Ready Templates (from Paul)

### Template A: Rewrite Under sumIdx (pointwise congruence)

```lean
-- Goal shape: sumIdx (fun ρ => LHS ρ) = sumIdx (fun ρ => RHS ρ)

have hpt : ∀ ρ, LHS ρ = RHS ρ := by
  intro ρ
  -- finish with `calc`/`trans`/algebra here (no `simp` or `simpa`)

have := sumIdx_congr hpt
-- `this` is: sumIdx (fun ρ => LHS ρ) = sumIdx (fun ρ => RHS ρ)
```

**When to use**: Anytime a rewrite fails "did not find occurrence." This reaches inside `fun ρ =>`.

### Template B: Normalize Negated Product Pointwise (no simpa)

**Right-metric branch** (want `(-F ρ) * g ...` as left factor):

```lean
have hneg : ∀ ρ, -(F ρ * g M ρ b r θ) = (-F ρ) * g M ρ b r θ := by
  intro ρ
  calc
    -(F ρ * g M ρ b r θ)
        = (-F ρ) * g M ρ b r θ := by exact neg_mul _ _
```

**Left-metric branch** (want `g ... * (-F ρ)`):

```lean
have hnegL : ∀ ρ, -(F ρ * g M a ρ r θ) = g M a ρ r θ * (-F ρ) := by
  intro ρ
  calc
    -(F ρ * g M a ρ r θ)
        = (-F ρ) * g M a ρ r θ := by exact neg_mul _ _
    _   = g M a ρ r θ * (-F ρ) := by exact mul_comm _ _
```

Now lift with `sumIdx_congr` (Template A).

### Template C: δ-Cancellation at Sum Level (no shape guessing, no simpa)

**Right side δ**:

```lean
-- Target: ... * g M ρ b r θ * (if ρ = b then 1 else 0)
have hδ :
  sumIdx (fun ρ => T ρ * g M ρ b r θ * (if ρ = b then 1 else 0))
    = sumIdx (fun ρ => T ρ * g M ρ b r θ) :=
  insert_delta_right_diag M r θ b (fun ρ => T ρ)
```

**Left side δ**:

```lean
-- Target: g M a ρ r θ * T ρ * (if ρ = a then 1 else 0)
have hδ :
  sumIdx (fun ρ => g M a ρ r θ * T ρ * (if ρ = a then 1 else 0))
    = sumIdx (fun ρ => g M a ρ r θ * T ρ) :=
  insert_delta_left_diag M r θ a (fun ρ => T ρ)
```

**Critical**: Must pointwise rearrange payload into EXACT shape first (Template B), then chain `.trans hδ`.

---

## Complete Fix Skeletons

### Right δ Site (b-branch) - Starting from Negated Product

```lean
-- Goal: sumIdx (fun ρ => -(F ρ * g M ρ b r θ) * (if ρ = b then 1 else 0)) = …
have hpack :
  sumIdx (fun ρ => -(F ρ * g M ρ b r θ) * (if ρ = b then 1 else 0))
    = sumIdx (fun ρ => (-F ρ) * g M ρ b r θ * (if ρ = b then 1 else 0)) := by
  refine sumIdx_congr (fun ρ => ?_)
  calc
    -(F ρ * g M ρ b r θ) * (if ρ = b then 1 else 0)
        = ((-F ρ) * g M ρ b r θ) * (if ρ = b then 1 else 0) := by
          exact congrArg (fun t => t * (if ρ = b then 1 else 0)) (neg_mul _ _)
    _   = (-F ρ) * g M ρ b r θ * (if ρ = b then 1 else 0) := (mul_assoc _ _ _).symm

have hδ :
  sumIdx (fun ρ => (-F ρ) * g M ρ b r θ * (if ρ = b then 1 else 0))
    = sumIdx (fun ρ => (-F ρ) * g M ρ b r θ) :=
  insert_delta_right_diag M r θ b (fun ρ => -F ρ)

exact hpack.trans hδ
```

### Left δ Site (a-branch) - Starting from Negated Product

```lean
-- Goal: sumIdx (fun ρ => -(F ρ * g M a ρ r θ) * (if ρ = a then 1 else 0)) = …
have hpack :
  sumIdx (fun ρ => -(F ρ * g M a ρ r θ) * (if ρ = a then 1 else 0))
    = sumIdx (fun ρ => g M a ρ r θ * (-F ρ) * (if ρ = a then 1 else 0)) := by
  refine sumIdx_congr (fun ρ => ?_)
  calc
    -(F ρ * g M a ρ r θ) * (if ρ = a then 1 else 0)
        = ((-F ρ) * g M a ρ r θ) * (if ρ = a then 1 else 0) := by
          exact congrArg (fun t => t * (if ρ = a then 1 else 0)) (neg_mul _ _)
    _   = g M a ρ r θ * (-F ρ) * (if ρ = a then 1 else 0) := by
          -- commute then reassociate, explicitly:
          have : (-F ρ) * g M a ρ r θ = g M a ρ r θ * (-F ρ) := mul_comm _ _
          exact this ▸ (mul_assoc _ _ _).symm

have hδ :
  sumIdx (fun ρ => g M a ρ r θ * (-F ρ) * (if ρ = a then 1 else 0))
    = sumIdx (fun ρ => g M a ρ r θ * (-F ρ)) :=
  insert_delta_left_diag M r θ a (fun ρ => -F ρ)

exact hpack.trans hδ
```

---

## Error-Specific Fix Guide

### Cluster 1: Lines 8751, 8933, 8950, 8954, 8983 (b-branch area)

**Error types present**: Unsolved goals (8751, 8933, 8983), Type mismatch (8950), Rewrite failed (8954)

**Pattern**: Right-side metric (`g M ρ b r θ`), negated product needing flip

**Fix approach**: Apply "Right δ Site" skeleton above
**Key steps**:
1. Lines 8751, 8933, 8983: Complete pointwise equality with explicit `calc`
2. Line 8950: Add `hpack` normalization step before δ-cancellation
3. Line 8954: Wrap rewrite attempt with `sumIdx_congr`

### Cluster 2: Lines 9169, 9187, 9191 (a-branch area)

**Error types present**: Unsolved goals (9169), Type mismatch (9187), Rewrite failed (9191)

**Pattern**: Left-side metric (`g M a ρ r θ`), negated product needing flip + commute

**Fix approach**: Apply "Left δ Site" skeleton above
**Key steps**:
1. Line 9169: Complete pointwise equality with `calc` including `mul_comm`
2. Line 9187: Add `hpack` normalization with commutation before δ-cancellation
3. Line 9191: Wrap rewrite with `sumIdx_congr`

### Cluster 3: Lines 9232, 9469, 9670, 9684 (later blocks)

**Error types present**: Type mismatch (9232, 9469, 9670), Rewrite failed (9684)

**Pattern**: Mixed metric orientations, δ-cancellation attempts with wrong shapes

**Fix approach**: Case-by-case application of appropriate skeleton (check metric orientation)
**Key steps**:
1. Read context to determine if right-metric or left-metric
2. Apply corresponding skeleton from above
3. Chain with `.trans`

### Cluster 4: Lines 9753, 9864 (final pair)

**Error types present**: Unsolved goals (both)

**Pattern**: Incomplete `sumIdx_congr` blocks

**Fix approach**: Close with explicit pointwise `calc`, no simpa
**Key steps**:
1. Add `calc` block inside the `fun ρ => ?_` goal
2. Use `neg_mul`, `mul_assoc`, `congrArg` explicitly
3. Chain final equality

---

## Guardrails (from Paul)

1. ❌ **Do NOT** add global helpers with `@[simp]` or ending in `… := by simpa …`
   - They're brittle under binders (saw 14→21 error spike)

2. ❌ **Do NOT** use `simp` or `simpa` inside `sumIdx_congr`
   - Prefer explicit `calc` chains with `mul_comm`, `mul_assoc`, `neg_mul`, `congrArg`

3. ❌ **Do NOT** try to `simpa using` δ-cancellation lemmas
   - First normalize to exact shape, THEN apply lemma with `.trans`

4. ✅ **DO** normalize pointwise before δ-cancellation
   - Use Template B to get exact shape
   - Then Template C for δ-cancellation
   - Chain with `.trans`

5. ✅ **DO** use `sumIdx_congr` for any rewrite under binder
   - This is the only way to reach inside `fun ρ =>`

---

## Implementation Strategy

**Phase 1** (Quick wins): Fix all "unsolved goals" errors first (6 errors)
- Lines: 8751, 8933, 8983, 9169, 9753, 9864
- Add explicit `calc` blocks to close pointwise equalities
- Expected result: 14→8 errors

**Phase 2** (Type mismatches): Add normalization steps (5 errors)
- Lines: 8950, 9187, 9469, 9670, 9232
- Insert `hpack` step before δ-cancellation
- Chain with `.trans`
- Expected result: 8→3 errors

**Phase 3** (Rewrite failures): Wrap with sumIdx_congr (3 errors)
- Lines: 8954, 9191, 9684
- Replace `rw` with `sumIdx_congr` + pointwise `calc`
- Expected result: 3→0 errors ✅

---

## Why This Works

Paul's explanation:
> "You're eliminating any dependence on simp-side matching under lambdas; all binder-local equalities are proved pointwise and then lifted. That's why this pattern worked in your earlier two fixes and is the right hammer for the remaining clusters too."

The equality-chaining pattern:
1. Goes inside binders explicitly with `sumIdx_congr`
2. Proves equalities pointwise with deterministic `calc` chains
3. Avoids all typeclass search under binders
4. Matches δ-lemmas exactly (no shape guessing)

This is what took us from 16→14, and will take us from 14→0.

---

## Files

**Main file**: `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean`
**Current build**: `build_helpers_removed_nov10.txt` (14 errors, baseline restored)
**Error lines**: 8751, 8933, 8950, 8954, 8983, 9169, 9187, 9191, 9232, 9469, 9670, 9684, 9753, 9864

**Progress tracking**:
- ✅ Section 1 (b-branch δ, line ~8893): Fixed with equality-chaining
- ✅ Section 2 (a-branch δ, line ~9125): Fixed with equality-chaining
- ⏳ Remaining 14 errors: Ready to apply systematic fixes

---

**Report Date**: November 10, 2025
**Status**: ✅ **READY FOR IMPLEMENTATION** - Templates validated, triage complete
**Next**: Apply Phase 1 (unsolved goals) to get quick 14→8 reduction
