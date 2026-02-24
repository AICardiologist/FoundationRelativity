# For JP: Cancel Lemmas Done, 6 Errors Remain
**Date**: October 20, 2025
**Quick Status**: ✅ Your Cancel lemma patches work! | ⚠️ 6 errors in downstream code

---

## TL;DR

**GOOD NEWS**: Both `Cancel_right_r_expanded` and `Cancel_right_θ_expanded` now compile successfully after 18 tactical fixes (replacing `simpa` with explicit `rw`/`ring`/`rfl`).

**REMAINING**: 6 errors in lemmas that USE your Cancel lemmas:
1. `g_times_RiemannBody_comm` - ring tactic can't handle sumIdx
2. Duplicate doc comment - syntax error
3-5. `regroup_right_sum_to_RiemannUp` - rewrite patterns don't match goal
6. Unknown downstream error

---

## What Was Fixed (Your Patches)

### Pattern Applied Throughout

**Your original** (hits recursion depth in large files):
```lean
simpa [hint]
```

**What works** (deterministic):
```lean
rw [hint]
ring  -- or rfl
```

### Specific Fixes (18 total)

1. **Split blocks** (lines 2984, 3227):
   - `simp [mul_add]` → `simp only [mul_add]`

2. **sumIdx_add_distrib** (lines 2995, 3238):
   - `simpa using sumIdx_add_distrib ...` → `exact sumIdx_add_distrib ...`

3. **g_symm** (lines 3122, 3367):
   - `simpa [g_symm M r θ k lam]` → `rw [g_symm M r θ k lam]; ring`

4. **Γtot_symm** (lines 3130, 3375):
   - `simpa [Γtot_symm ...]` → `rw [Γtot_symm ...]`

5. **Γ₁ recognition** (lines 3132, 3377):
   - `simpa [Γ₁] using (h1.trans h2)` → `rw [h1, h2]; rfl`

6. **ExtraRight_* recognition** (lines 3150, 3396):
   - `unfold ExtraRight_*` → `unfold ExtraRight_*; rfl`

**Result**: Both Cancel lemmas compile with 0 errors.

---

## Remaining Errors (Not in Your Patches)

### Error 1: g_times_RiemannBody_comm (Line 4325)

**Problem**: After `unfold RiemannUp; ring`, goal is:
```lean
(g * Σf - g * Σh) = g * Σ(f - h)
```

`ring` can't handle this because `sumIdx` is not a ring operation.

**Fix Options**:
1. Remove this lemma (check if it's actually used with `grep "@[simp] lemma g_times_RiemannBody_comm"`)
2. Or prove it properly:
```lean
@[simp] lemma g_times_RiemannBody_comm ... := by
  unfold RiemannUp
  congr 1  -- separate the arithmetic parts
  rw [← mul_sub]  -- factor out g
  congr 1
  -- Now prove: (Σf - Σg) = Σ(f - g)
  rw [sumIdx_sub_distrib]  -- if this lemma exists
  -- Otherwise:
  apply sumIdx_congr
  intro lam
  ring
```

---

### Error 2: Duplicate Doc Comment (Line 4333)

**Problem**: Two `/--` comments in a row (lines 4331-4333 and 4334-...).

**Fix**: Merge into one:
```lean
/-- Sum-level regrouping for the **right slot** (CORRECTED):
    S_Right = g_{bb}·R^b_{a r θ} + (ExtraRight_r − ExtraRight_θ).

    The extra terms come from the second branch of metric compatibility.
    This correctly implements the metric-compatibility expansion by including the
    unavoidable extra terms from the second branch (Γ^λ_{μb} g_{kλ}).

    [rest of doc]
    -/
```

---

### Errors 3-5: regroup_right_sum_to_RiemannUp (Lines 4371, 4412, 4420)

**Problem**: Trying to rewrite with `Cancel_right_r_expanded`:
```lean
rw [Cancel_right_r_expanded M r θ h_ext a b]
```

But the goal has:
```lean
sumIdx (fun k =>
    dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a) r θ * g M k b r θ
  - dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a) r θ * g M k b r θ
  + Γtot M r θ k Idx.θ a * dCoord Idx.r (fun r θ => g M k b r θ) r θ  -- ← term 3
  - Γtot M r θ k Idx.r a * dCoord Idx.θ (fun r θ => g M k b r θ) r θ  -- ← term 4
  )
```

The `Cancel_right_r_expanded` lemma gives you just term 3 by itself:
```lean
sumIdx (fun k => Γtot M r θ k Idx.θ a * dCoord Idx.r (fun r θ => g M k b r θ) r θ)
  = ...
```

But the rewrite can't match because term 3 is mixed with terms 1, 2, 4 inside the sum.

**Fix**: Separate the 4-term sum into 4 individual sums first:
```lean
calc sumIdx (fun k => term1 - term2 + term3 - term4)
    = sumIdx (fun k => term1)
      - sumIdx (fun k => term2)
      + sumIdx (fun k => term3)
      - sumIdx (fun k => term4) := by
        -- Distribute the sum over the 4 terms
        rw [sumIdx_sub_distrib]  -- if this exists, or prove it inline
        rw [sumIdx_add_distrib]
        rw [sumIdx_sub_distrib]
  _ = sumIdx (fun k => term1)
      - sumIdx (fun k => term2)
      + (sumIdx (fun ρ => g M ρ b r θ * sumIdx (fun lam => ...))
         + ExtraRight_r M r θ a b)
      - (sumIdx (fun k => term4)) := by
        -- Now apply Cancel_right_r_expanded to the isolated term3
        rw [Cancel_right_r_expanded M r θ h_ext a b]
  _ = ... := by
        -- Apply Cancel_right_θ_expanded to term4
        rw [Cancel_right_θ_expanded M r θ h_ext a b]
        -- Continue proof
```

**Alternative**: Check if `sumIdx_sub_distrib` and multi-term versions exist. If not, may need to prove them first.

---

### Error 6: Line 5269

**Problem**: Unknown - need to see the code at that line.

**Likely**: A downstream lemma that depends on `regroup_right_sum_to_RiemannUp`. Once we fix errors 3-5, this might resolve automatically.

---

## Concrete Next Steps

### Option A: Fix All 6 Errors (1-2 hours)

1. Check if `g_times_RiemannBody_comm` is used (grep for it). If not, delete it. If yes, fix with `congr 1` approach above.

2. Merge duplicate doc comments (30 seconds).

3. Fix `regroup_right_sum_to_RiemannUp` proof strategy:
   - Check if `sumIdx_sub_distrib` exists
   - If not, prove it as a helper lemma
   - Restructure the calc chain to separate the 4 terms
   - Apply Cancel lemmas to isolated terms

4. Check error at line 5269 after fixing regroup lemma.

### Option B: I Can Continue Fixing

If you want me to continue, I can:
1. Check if sumIdx_sub_distrib exists in the file
2. Fix or remove g_times_RiemannBody_comm
3. Merge the doc comments
4. Restructure the regroup proof
5. Fix line 5269

Just say "continue" and I'll proceed.

### Option C: Commit Cancel Lemmas, You Fix Downstream

Commit message:
```
fix: implement Cancel lemmas with deterministic tactics

- Both Cancel_right_r_expanded and Cancel_right_θ_expanded now compile
- Replaced all simpa with explicit rw/ring/rfl to avoid recursion depth
- 18 tactical adjustments (9 per lemma)

Remaining work (not in Cancel lemmas):
- Fix g_times_RiemannBody_comm (line 4325)
- Merge duplicate doc comment (line 4333)
- Restructure regroup_right_sum_to_RiemannUp proof (lines 4371, 4412, 4420)
- Fix downstream error (line 5269)

Co-authored-by: JP (mathematical framework)
```

---

## Build Logs

**Full log**: `/tmp/jp_r_fixed_unfold.log`

**Quick check**:
```bash
grep "^error:" /tmp/jp_r_fixed_unfold.log | grep -v "build failed" | grep -v "Lean exited"
```

**Output**:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:4325:51: unsolved goals
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:4333:75: unexpected token '/--'
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:4371:8: Tactic `rewrite` failed
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:4412:10: Tactic `rewrite` failed
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:4420:10: Tactic `rewrite` failed
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:5269:60: Application type mismatch
```

All errors are AFTER line 3419 (where your Cancel_θ lemma ends). ✅

---

## Documentation Available

All in `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/`:

- `IMPLEMENTATION_STATUS_FINAL_OCT20.md` - Full detailed analysis
- `JP_CANCEL_LEMMAS_SUCCESS_OCT20.md` - Celebration of Cancel lemmas success
- `JP_DROPIN_STATUS_OCT20.md` - Initial tactical issues identified
- `CLEARED_FOR_TACTICAL_WORK_OCT20.md` - Prerequisites verified
- `SP_VERIFICATION_CONFIRMED_OCT20.md` - Senior Professor's math verification
- `PREREQUISITE_CHECK_GAMMA1_SYMM_OCT20.md` - Γ₁_symm verification

---

## Questions for You

1. **Should I continue fixing the 6 errors?** Or do you want to take over?

2. **Should we commit the Cancel lemmas now** (working code) or wait until all errors are fixed?

3. **For g_times_RiemannBody_comm**: Remove it or fix it? (I can grep to see if it's used)

4. **For regroup proof**: Do you have a preferred proof structure, or should I just make it work with whatever tactics succeed?

---

**Your Call**: What should I do next?

---

**Prepared by**: Claude Code
**Date**: October 20, 2025
**Status**: ✅ **CANCEL LEMMAS PROVEN** | 🤔 **AWAITING DIRECTION ON REMAINING 6 ERRORS**
