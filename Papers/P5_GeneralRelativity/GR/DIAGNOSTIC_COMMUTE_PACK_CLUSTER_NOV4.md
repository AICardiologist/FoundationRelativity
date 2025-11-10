# DIAGNOSTIC: Commute/Pack Cluster Errors - Need Guidance

**Date**: November 4, 2025
**Context**: Step 6 complete (9688/9702 eliminated). Now tackling errors 8982, 8997, 9014, 9018, 9232 (shifted from baseline 8959, 8974, 8991, 8995, 9209)

---

## Summary

Paul's guidance suggested these errors have "similar shapes" to 9688/9702 and should use the "same pack→lemma treatment". However, upon investigation, these errors appear to be in a **different proof structure** and may not be pack→lemma issues.

**Request**: Clarification on whether these errors need:
1. Pack→lemma pattern (similar to 9688/9702), OR
2. Different tactic fixes (replacing `simpa`/`ring` with explicit proofs), OR
3. A hybrid approach

---

## Error Analysis

### Baseline Errors (Step 5)

| Line | Error Type | Description |
|------|-----------|-------------|
| 8959 | `failed to synthesize HasDistribNeg ℝ` | Maximum recursion depth |
| 8974 | `unsolved goals` | Inside `scalar_finish` proof |
| 8991 | `Type mismatch` | `H` has wrong type |
| 8995 | `Tactic rewrite failed` | Pattern not found |
| 9209 | `Tactic rewrite failed` | Pattern not found |

### Current Errors (After Step 6, +23 shift)

| Current Line | Baseline Line | Error Type | Location |
|--------------|---------------|-----------|----------|
| 8982 | 8959 | `failed to synthesize` | `simpa [neg_mul_right₀] using this` |
| 8997 | 8974 | `unsolved goals` | `ring` in `scalar_finish` |
| 9014 | 8991 | `Type mismatch` | `exact H` using failed `scalar_finish` |
| 9018 | 8995 | `Tactic rewrite failed` | `rw` pattern mismatch |
| 9232 | 9209 | `Tactic rewrite failed` | `rw` pattern mismatch |

---

## Code Context Analysis

### Error at Line 8982 (baseline 8959)

**Location**: Inside proof using `insert_delta_right_diag`

```lean
have := insert_delta_right_diag M r θ b (fun ρ =>
  - ( dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ
    - dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ
    + sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
    - sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) ))
-- `-(E * g) = (-E) * g` on both sides.
simpa [neg_mul_right₀] using this  -- ❌ FAILS: HasDistribNeg ℝ recursion
```

**Issue**: `simpa [neg_mul_right₀]` triggers `HasDistribNeg ℝ` recursion (same error we saw in Step 4)

**Question**: Does this need pack→lemma, or should we replace `simpa` with explicit `rw`/`calc`?

---

### Error at Line 8997 (baseline 8974)

**Location**: Inside `scalar_finish` lemma proof

```lean
have scalar_finish :
  ∀ ρ,
    ( -(dCoord μ ...) * g M ρ b r θ
    +  (dCoord ν ...) * g M ρ b r θ )
    +  ( g M ρ b r θ * ( sumIdx (...) - sumIdx (...) ) )
    =
    - ( ( dCoord μ ...
         - dCoord ν ...
         + sumIdx (...)
         - sumIdx (...) )
        * g M ρ b r θ ) := by
  intro ρ
  ring  -- ❌ FAILS: unsolved goals
```

**Issue**: `ring` cannot prove the equality (likely due to complex nested sumIdx or negation structure)

**Question**: Does this need pack→lemma, or should we use manual `calc` with explicit rewrites?

---

### Error at Line 9014 (baseline 8991)

**Location**: Using failed `scalar_finish` result

```lean
calc
  (sumIdx B_b)
- sumIdx (fun ρ => (Γtot M r θ ρ μ a) * (nabla_g M r θ ν ρ b))
+ sumIdx (fun ρ => (Γtot M r θ ρ ν a) * (nabla_g M r θ μ ρ b))
    = sumIdx (fun ρ =>
          - ( dCoord μ ...
             - dCoord ν ...
             + sumIdx (...)
             - sumIdx (...) )
           * g M ρ b r θ) := by
    simp only [nabla_g, RiemannUp, sub_eq_add_neg]
    have H := sumIdx_congr scalar_finish
    exact H  -- ❌ FAILS: Type mismatch (because scalar_finish failed)
```

**Issue**: Cascading failure from `scalar_finish` error at line 8997

**Question**: This will be fixed automatically if `scalar_finish` is fixed, correct?

---

### Errors at Lines 9018, 9232 (baseline 8995, 9209)

**Location**: Attempting to `rw` with failed proofs

```lean
rw [...]  -- ❌ FAILS: Did not find an occurrence of the pattern
```

**Issue**: Pattern matching failures in rewrite tactics (likely cascading from earlier failures)

**Question**: These will be fixed automatically if upstream errors are fixed?

---

## Comparison: 9688/9702 vs 8982-9232

| Aspect | 9688/9702 (Step 6) | 8982-9232 (Current) |
|--------|-------------------|---------------------|
| **Goal Shape** | Four separate `sumIdx` blocks | Nested `sumIdx` inside larger expressions |
| **Fix Pattern** | Pack 4 sums → apply `payload_cancel_all_flipped` | ??? |
| **Error Type** | Type mismatch (shape) | `HasDistribNeg` recursion + `ring` failure |
| **Proof Structure** | Variable assignment → pack → apply lemma | `insert_delta_right_diag` → scalar packaging → calc |

**Observation**: These do NOT appear to be the same pattern as 9688/9702

---

## Proposed Fix Strategies

### Option A: Replace `simpa` to Avoid Recursion

For line 8982, replace:
```lean
simpa [neg_mul_right₀] using this
```

With explicit rewrite:
```lean
calc ... = ... := this
     _ = ... := by simp only [neg_mul_right₀]
```

**Pros**: Avoids `HasDistribNeg` recursion
**Cons**: Doesn't address `scalar_finish` failure at 8997

---

### Option B: Fix `scalar_finish` with Manual Proof

For line 8997, replace `ring` with manual `calc` chain showing the algebraic steps explicitly.

**Pros**: Deterministic, avoids `ring` failure
**Cons**: Labor-intensive, may miss the underlying issue

---

### Option C: Pack→Lemma (If Applicable)

If Paul has identified a lemma that these proofs should use (like `payload_cancel_all_flipped` for 9688/9702), we could:
1. Pack the relevant sums
2. Apply the lemma

**Pros**: Clean, reusable pattern
**Cons**: Not clear what lemma to use or how to pack

---

## Questions for Paul

1. **Are these pack→lemma issues?** If so:
   - What lemma should be applied after packing?
   - What expressions need to be packed?

2. **Or are these tactic replacement issues?** If so:
   - Should we replace `simpa` with `rw`/`calc` to avoid `HasDistribNeg` recursion?
   - Should we replace `ring` with manual proofs in `scalar_finish`?

3. **Are the errors at 9018, 9232 cascading failures?** Will they be auto-fixed if 8982, 8997 are resolved?

4. **What is the "similar shape" you mentioned?** I don't see the same four-sum pattern as 9688/9702.

---

## Current Status

**Step 6**: ✅ Complete (9688/9702 eliminated with pack→lemma pattern)
**Step 7**: ⏸ Blocked pending clarification on fix strategy for 8982-9232

**Error Count**: 18 (same as baseline)
**Next Targets**: Lines 8982, 8997, 9014, 9018, 9232

---

**REQUEST**: Please advise on fix strategy for these errors. Should I proceed with Option A (replace `simpa`), Option B (fix `ring`), Option C (pack→lemma), or a different approach?
