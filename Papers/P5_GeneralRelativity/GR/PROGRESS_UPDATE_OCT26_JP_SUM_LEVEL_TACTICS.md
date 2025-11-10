# Progress Update: JP's Sum-Level Tactics Implementation - October 26, 2025

**Status**: ⚠️ **PARTIALLY IMPLEMENTED** - Core structure works, h_collect step needs additional tactical guidance

**Date**: October 26, 2025
**Agent**: Claude Code (Sonnet 4.5)
**For**: JP (Tactic Professor)

---

## Executive Summary

### What Works ✅

1. **payload_cancel proofs** (both hb and ha)
   - Fixed by using `simp only [h]; exact sumIdx_zero` instead of `simp only [h, sumIdx]; ring`
   - Pattern: Prove pointwise equality to 0, then apply `sumIdx_zero`

2. **h₁, h₂, h₃, h₄ proofs** (both branches)
   - Fixed by using explicit steps: `apply sumIdx_congr; intro ρ; simp only [mul_sumIdx]; apply sumIdx_congr; intro e; ring`
   - Avoids `simpa` which tried to do too much at once

3. **h_lin proofs** (both branches)
   - Fixed by using `rw [← sumIdx_map_sub, ← sumIdx_map_sub, ← sumIdx_add_distrib]` to linearize outer sums first
   - Then `apply sumIdx_congr` at each level with `ring` on scalars

### What's Blocked ❌

4. **h_collect_to_grb / h_collect_to_gar proofs**
   - **Location**: Lines 7289-7303 (hb), Lines 7451-7464 (ha)
   - **Issue**: Metric index manipulation too complex for automated tactics

---

## The h_collect Blocking Issue

### Current Approach (Doesn't Complete)

```lean
have h_collect_to_grb :
  sumIdx (fun ρ => sumIdx (fun e =>
    ((Γρμa * Γeνρ) - (Γρνa * Γeμρ)) * g_eb +
    ((Γρμa * Γeνb) - (Γρνa * Γeμb)) * g_ρe))
  =
  sumIdx (fun ρ =>
    g_ρb * (sumIdx (Γρμe * Γeνa) - sumIdx (Γρνe * Γeμa))) := by
  classical
  apply sumIdx_congr; intro ρ
  rw [← sumIdx_map_sub]
  simp only [g_symm_JP, sumIdx_contract_g_right, sumIdx_contract_g_left, sumIdx_reduce_by_diagonality]
  ring
```

### What Happens

After `simp only [...]`, the goal becomes:

```lean
⊢ (sumIdx fun e =>
      Γρμa * Γeνρ * g_be + Γρμa * Γeνb * g_ρe +
        (-(Γρνa * Γeμρ * g_be) - Γρνa * Γeμb * g_ρe)) =
    g_bρ * sumIdx fun k => Γρμk * Γkνa - Γρνk * Γkμa
```

**Problem**: `ring` cannot complete because:
1. Terms with `g_be` and `g_ρe` need metric contraction
2. The contraction lemmas (`sumIdx_contract_g_right`, etc.) work on sums like `sumIdx (F e * g_de)`, but the expression has multiple terms summed together
3. Need to split the sum using linearity before applying contractions
4. After contractions, need to use diagonality to get `g_bb` and `g_ρρ`, then somehow combine to `g_bρ`

### Available Lemmas

- `sumIdx_contract_g_right`: `sumIdx (fun e => F e * g M d e r θ) = F d * g M d d r θ`
- `sumIdx_contract_g_left`: `sumIdx (fun d => g M d e r θ * F d) = g M e e r θ * F e`
- `sumIdx_reduce_by_diagonality`: `sumIdx (fun e => g M ρ e r θ * K e) = g M ρ ρ r θ * K ρ`
- `g_symm_JP`: `g M μ ν r θ = g M ν μ r θ`

### What's Needed

The proof requires:
1. Splitting `sumIdx (A + B + (-C) + (-D))` into `sumIdx A + sumIdx B - sumIdx C - sumIdx D`
2. Applying contraction lemmas to each piece
3. Using diagonality to reduce `g_bb` and `g_ρρ`
4. Somehow showing that the result equals `g_bρ * (...)` on the RHS

**This is beyond the scope of `ring` and `simp`** - it requires explicit tactical manipulation of metric indices.

---

## Specific Questions for JP

### Q1: h_collect Proof Strategy

How should we prove h_collect_to_grb? Options:

**A)** Manual calc chain?
```lean
calc
  sumIdx (fun e => (A - B) * g_eb + (C - D) * g_ρe)
    = sumIdx (A * g_eb) - sumIdx (B * g_eb) + sumIdx (C * g_ρe) - sumIdx (D * g_ρe) := by <?>
  _ = g_bb * A_ρ - g_bb * B_ρ + g_ρρ * C_b - g_ρρ * D_b := by <?>
  _ = g_bρ * (sumIdx ...) := by <?>
```

**B)** Auxiliary lemmas?
```lean
lemma metric_collect_to_diagonal :
  sumIdx (fun e => F₁ e * g M e b r θ + F₂ e * g M ρ e r θ) =
  g M b b r θ * F₁ b + g M ρ ρ r θ * F₂ ρ := by <?>
```

**C)** Different approach entirely?

### Q2: Are Collector Lemmas Sufficient?

Are the existing collector lemmas (`sumIdx_contract_g_right`, etc.) sufficient for this proof, or do we need additional lemmas for the specific pattern in h_collect?

### Q3: Expected Proof Length

JP's original comment said "compact version with sumIdx_congr; intro; ring", but this doesn't work. What's the expected proof length? Should it be:
- 1-2 lines (unlikely given complexity)
- 5-10 lines (calc chain)
- 10-20 lines (explicit lemma applications)

### Q4: Diagonality Pattern

How do we show that `g_bb * (stuff with ρ) + g_ρρ * (stuff with b)` equals `g_bρ * (combined stuff)`?

This seems to require:
- Using diagonality to convert `g_bb` and `g_ρρ` to something
- Using symmetry `g_bρ = g_ρb`
- Some index manipulation in the Christoffel terms

---

## What We've Learned

### Pattern 1: Sum of Zeros
```lean
have h : ∀ ρ, [expr] = 0 := by intro ρ; ring
simp only [h]
exact sumIdx_zero
```

### Pattern 2: Pushing Scalars into Sums
```lean
apply sumIdx_congr; intro ρ
simp only [mul_sumIdx]
apply sumIdx_congr; intro e
ring
```

### Pattern 3: Linearizing Nested Sums
```lean
rw [← sumIdx_map_sub, ← sumIdx_map_sub, ← sumIdx_add_distrib]
apply sumIdx_congr; intro ρ
rw [← sumIdx_map_sub, ← sumIdx_map_sub, ← sumIdx_add_distrib]
apply sumIdx_congr; intro e
ring
```

### Pattern 4: What Doesn't Work
```lean
-- ❌ simpa [lemmas] using rfl  -- tries to do too much
-- ❌ simp [h, sumIdx]; ring     -- sumIdx isn't a simp lemma, need sumIdx_zero
-- ❌ simp only [collectors]; ring  -- collectors need explicit structure match
```

---

## Build Status

**File**: `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean`

**Errors Remaining**: 13 total
- 2 in hb h_collect_to_grb (line 7297)
- 2 in ha h_collect_to_gar (line 7459)
- Rest are cascading errors from these

**Build Logs**:
- `/tmp/build_jp_simplified.txt` - Latest build with all fixes except h_collect

**Lines of Interest**:
- 7201-7343: hb proof (payload_cancel ✅, h₁-h₄ ✅, h_lin ✅, h_collect ❌)
- 7365-7497: ha proof (same pattern)

---

## Next Steps

⏳ **AWAITING JP GUIDANCE** on h_collect tactical approach

Once we get past h_collect:
1. Verify `scalar_finish` works (should be straightforward `intro ρ; ring`)
2. Verify assembly step works
3. Test full algebraic_identity compilation
4. Verify cascade to ricci_identity_on_g_general and Riemann_swap_a_b_ext

---

## Impact Assessment

### If h_collect Works
- hb and ha proofs complete
- algebraic_identity compiles (estimated)
- ricci_identity_on_g_general compiles (estimated)
- Riemann_swap_a_b_ext compiles (estimated)
- **Estimated time to completion**: 1-2 hours

### If h_collect Needs Major Rework
- May need to redesign the proof strategy
- Potentially break h_collect into multiple sub-lemmas
- **Estimated time to completion**: 3-6 hours

---

## Technical Context

### Key Insight

JP's sum-level approach is **fundamentally sound**:
- payload_cancel works (sum of zeros pattern)
- h₁-h₄ work (mul_sumIdx pattern)
- h_lin works (linearity pattern)

The blocker is **metric index manipulation** in h_collect, which requires explicit tactical guidance for:
1. Splitting sums with multiple terms
2. Applying contraction lemmas to each piece
3. Using diagonality to reduce diagonal components
4. Combining results to match target form

---

**Prepared By**: Claude Code (Sonnet 4.5)
**Date**: October 26, 2025
**For**: JP (Tactic Professor)

---
