# Section B Complete: Infrastructure and Right-Slot Refolds
**Date:** October 11, 2025
**Status:** ✅ All Section B lemmas implemented and tested
**Build:** 0 errors, 6 sorries (unchanged)

---

## Executive Summary

Successfully implemented all infrastructure improvements from JP's Section B guidance:
1. **Denominator form shims** - Reusable helpers for field_simp pattern matching
2. **Fold helpers** - Quick folding without invoking ring in binders
3. **Right-slot compat_refold lemmas** - Mirrors of left-slot with same pure-rewrite discipline

**Key Achievement:** All new lemmas compile with 0 errors using pure-rewrite tactics (no search).

---

## A. Denominator Form Shims (Lines 39-60)

### Problem Solved
field_simp pattern-matches **syntactically**, not semantically. When the goal contains `(r - M * 2)⁻¹`, providing `r - 2 * M ≠ 0` fails even though they're mathematically equal by commutativity.

### Solution: Exact Form Matching
```lean
/-- Convert r - 2*M ≠ 0 to the commuted form r - M*2 ≠ 0 for field_simp. -/
lemma denom_form_of_comm {M r : ℝ} (hD₀ : r - 2 * M ≠ 0) : r - M * 2 ≠ 0 := by
  simpa [mul_comm] using hD₀

/-- Derive r - M*2 ≠ 0 directly from Exterior (exact form for field_simp). -/
lemma denom_form_of_exterior {M r θ : ℝ} (h_ext : Exterior M r θ) : r - M * 2 ≠ 0 := by
  have : r - 2 * M ≠ 0 := by linarith [h_ext.hr_ex]
  simpa [mul_comm] using this
```

### Bundled Nonzeros
```lean
/-- Package all common nonzero hypotheses from Exterior for field_simp. -/
lemma nonzeros_of_exterior {M r θ : ℝ} (h_ext : Exterior M r θ) :
  r ≠ 0 ∧ f M r ≠ 0 ∧ r - M * 2 ≠ 0 := by
  refine ⟨r_ne_zero h_ext, f_ne_zero h_ext, ?_⟩
  have : r - 2 * M ≠ 0 := by linarith [h_ext.hr_ex]
  simpa [mul_comm] using this
```

**Usage Pattern:**
```lean
-- Instead of:
have hr : r ≠ 0 := Exterior.r_ne_zero h_ext
have hf : f M r ≠ 0 := Exterior.f_ne_zero h_ext
have hD : r - M * 2 ≠ 0 := by linarith [h_ext.hr_ex]

-- Use:
have ⟨hr, hf, hD⟩ := Exterior.nonzeros_of_exterior h_ext
```

---

## B. Fold Helpers (Lines 115-123)

### Problem Solved
Using `ring` inside binder contexts (like `funext k`) creates search overhead and can cause timeouts. Need quick folding lemmas.

### Solution: Simp-Friendly Folds
```lean
/-- Fold subtraction on right: a * c - b * c = (a - b) * c -/
@[simp] lemma fold_sub_right {a b c : ℝ} : a * c - b * c = (a - b) * c := by
  simpa using (sub_mul a b c).symm

/-- Fold addition on left: a * b + a * c = a * (b + c) -/
@[simp] lemma fold_add_left {a b c : ℝ} : a * b + a * c = a * (b + c) := by
  simpa using (mul_add a b c).symm
```

**Why These Work:**
- Marked `@[simp]` so simp can automatically apply them
- Based on mathlib's `sub_mul` and `mul_add` (backward direction)
- No search - just direct simplification

**Usage Pattern:**
```lean
-- Inside funext k, instead of:
ring  -- ← Expensive search in binder context!

-- Use:
simp [fold_sub_right, fold_add_left]  -- ← Quick pattern match
```

---

## C. Right-Slot compat_refold Lemmas (Lines 1787-1821)

### Design: Mirrors of Left-Slot

**Left-slot lemmas** (existing):
- `compat_refold_r_kb`: For fixed `(k, b)`, isolate `Σλ Γ^λ_{rb} g_{kλ}` (left slot `b`)
- `compat_refold_θ_kb`: θ-branch version

**Right-slot lemmas** (new):
- `compat_refold_r_ak`: For fixed `(a, k)`, isolate `Σλ Γ^λ_{rk} g_{aλ}` (right slot `k`)
- `compat_refold_θ_ak`: θ-branch version

### Implementation: Pure Rewrite

Both use identical tactical pattern:
1. Start from `dCoord_g_via_compat_ext` with indices ordered correctly
2. Use `congrArg` to subtract unwanted sum
3. Use `simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]` to rearrange

**Example (compat_refold_r_ak):**
```lean
lemma compat_refold_r_ak
    (M r θ : ℝ) (h_ext : Exterior M r θ) (a k : Idx) :
  sumIdx (fun lam => Γtot M r θ lam Idx.r k * g M a lam r θ)
    =
  dCoord Idx.r (fun r θ => g M a k r θ) r θ
  - sumIdx (fun lam => Γtot M r θ lam Idx.r a * g M lam k r θ) := by
  classical
  -- ∂_r g_{a k} = Σλ Γ^λ_{r a} g_{λ k} + Σλ Γ^λ_{r k} g_{a λ}
  have H := dCoord_g_via_compat_ext M r θ h_ext Idx.r a k
  -- Move Σλ Γ^λ_{r a} g_{λ k} to the RHS; keep Σλ Γ^λ_{r k} g_{a λ} on LHS
  have := congrArg (fun x =>
    x - sumIdx (fun lam => Γtot M r θ lam Idx.r a * g M lam k r θ)) H
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this.symm
```

**Why This Compiles Fast:**
- No `simp` search beyond definitional unfolding
- Only `congrArg` (pure rewrite) + `simpa` with explicit reassociation
- Same discipline that made E3 integration compile in ~20 seconds

---

## Design Principles (From JP)

### 1. Match What's There, Don't Normalize
> "In high-algebraic proofs the kernel is syntactic, so the shortest path is often
> 'match what's there,' not 'normalize to what you think should be there.'"

**Application:** The `denom_form_of_exterior` lemma proves `r - M * 2 ≠ 0` (matching the goal) instead of trying to normalize with `[two_mul, mul_comm]`.

### 2. Fold, Don't Expand
> "When rearranging linear terms: use ← add_mul and ← mul_add to fold quickly
> into the shape your next lemma expects."

**Application:** The fold helpers use backward direction of distributivity lemmas:
- `← add_mul`: Folds `a*c + b*c` into `(a+b)*c`
- `← mul_add`: Folds `a*b + a*c` into `a*(b+c)`

### 3. Avoid Global AC Normalization
> "Resist simp [mul_comm, mul_assoc, two_mul] in large goals; prefer small
> local simpa […] using … on helper facts."

**Application:** The Section A fix used `simpa [mul_comm] using hD₀` on a single hypothesis, not global normalization of the entire goal.

### 4. One field_simp Per Lemma
> "Expand with simp only […] to the minimal form you need, then call
> field_simp […] once with the exact non-zero hyps. Finish with ring."

**Application:** The successful line 3786 fix:
```lean
simp only [Γ_r_rr, Γ_r_θθ, Γ_θ_rθ, div_eq_mul_inv, f, pow_two]
have hD : r - M * 2 ≠ 0 := by linarith [h_ext.hr_ex]  -- Exact form!
field_simp [hr, hD]  -- One call with exact hyps
ring
```

---

## Build Verification

**Command:** `lake build Papers.P5_GeneralRelativity.GR.Riemann`

**Results:**
```
Build completed successfully (3078 jobs).
Errors: 0 ✅
Sorries: 6 (unchanged)
Build Time: ~22 seconds
```

**Added Lemmas:**
- 3 denominator shims (lines 39-60)
- 2 fold helpers (lines 115-123)
- 2 right-slot compat_refold lemmas (lines 1787-1821)
- Total: 69 lines added

**No Regressions:** All existing proofs still compile. No new errors introduced.

---

## What Section B Unlocks

### For Section C (Sorry Elimination):

1. **Denominator shims** remove the temptation to over-normalize
   - Just call `Exterior.denom_form_of_exterior h_ext` when field_simp needs `r - M * 2 ≠ 0`

2. **Fold helpers** speed up sum manipulations
   - Inside `funext k`, use `simp [fold_sub_right]` instead of `ring`

3. **Right-slot refolds** enable symmetric sum manipulations
   - Apply same calc chain patterns to both left and right slots
   - Wire into apply_H chains where right-slot sums appear

### For Future Proofs:

These lemmas are reusable patterns:
- **Any lemma needing field_simp** can use `nonzeros_of_exterior` to bundle hypotheses
- **Any sum manipulation** can use the fold helpers to avoid search
- **Any compat equation** can use the refold mirrors to isolate specific sums

---

## Next Steps (Section C: Sorry Elimination)

**Current 6 Sorries (after Section B additions):**

1. **Line 2635:** `regroup_right_sum_to_RiemannUp` - Right-slot mirror (uses right-slot refolds)
2. **Line 3142:** `regroup_left_sum_to_RiemannUp` - Uses sumIdx_congr_then_fold
3. **Line 3215:** `ricci_identity_on_g_rθ_ext` - Ricci off-diagonal identity
4. **Line 3252:** `ricci_identity_on_g` - General Ricci identity
5. **Line 3261:** `Riemann_swap_a_b_ext` - Riemann symmetry on Exterior
6. **Line 3276:** `Riemann_swap_a_b` - General Riemann symmetry

**Note:** Line numbers shifted by ~69 lines due to Section B infrastructure additions.

**Strategy:**
- Work in order (increasing difficulty)
- Use pure-rewrite discipline throughout
- Apply Section B infrastructure where appropriate
- Test each sorry fix independently

---

## Commit History

1. **00b533e** - Complete Section A (6/6 tactical errors resolved)
2. **46b9629** - Add Section B infrastructure (this commit)

---

## Technical Debt Removed

### Before Section B:
- Had to manually prove `r - M * 2 ≠ 0` each time (risk of normalization mistakes)
- Used `ring` in binder contexts (slow builds, potential timeouts)
- No right-slot refold lemmas (would need to derive each time)

### After Section B:
- One-liner shims for all denominator forms
- Quick fold helpers marked `@[simp]`
- Symmetric left/right slot refold lemmas
- All patterns reusable across future proofs

---

**Prepared by:** Claude Code (AI Agent)
**Date:** October 11, 2025
**Status:** ✅ Section B Complete - Ready for Section C

**Quote from JP:**
> "The 'match what's there' discipline + 'fold, don't expand' is exactly
> what keeps the kernel happy and your builds fast."
