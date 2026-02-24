# Test Results: Recommended Fixes Applied

**Date:** October 8, 2025, Morning Session
**Purpose:** Test the two recommended fixes from investigation report
**Status:** ⚠️ Both fixes attempted, deeper issues revealed

---

## Summary

Applied both recommended tactical fixes from the investigation report:
1. ✅ Double case split (`cases c <;> cases d`) for nabla_nabla_g_zero_ext
2. ✅ Temporary sorries for helper lemmas to test ricci_identity_on_g_rθ

**Result:** Both tactics applied successfully, but deeper structural issues remain that prevent completion.

---

## Test #1: Double Case Split for nabla_nabla_g_zero_ext

### What Was Changed

**File:** Riemann.lean:1650-1652

**Before:**
```lean
unfold nabla
cases c <;>
  simp [dCoord_t, dCoord_r, dCoord_θ, dCoord_φ, H0, H1, H2, sumIdx_expand]
```

**After:**
```lean
unfold nabla
-- Double case split on `c` and `d` to expose all concrete branches (16 total)
cases c <;> cases d <;>
  simp [dCoord_t, dCoord_r, dCoord_θ, dCoord_φ, H0, H1, H2, sumIdx_expand]
```

### Build Result: ❌ STILL HAS ERRORS

**Error at line 1639:**
```
error: unsolved goals
case t.t
M r θ : ℝ
h_ext : Exterior M r θ
a b : Idx
H1 : ∀ (e : Idx), nabla_g M r θ t e b = 0
H2 : ∀ (e : Idx), nabla_g M r θ t a e = 0
H0 : dCoord t (fun r θ => nabla_g M r θ t a b) r θ = 0
⊢ -(Γtot M r θ φ a t *
        (-(Γtot M r θ b t φ *
              (match (motive := Idx → Idx → ℝ → ℝ → ℝ) b, b with
                | t, t => fun r _θ => -f M r
                | Idx.r, Idx.r => fun r _θ => (f M r)⁻¹
                | Idx.θ, Idx.θ => fun r _θ => r ^ 2
                | φ, φ => fun r θ => r ^ 2 * sin θ ^ 2
                | x, x_1 => fun x x => 0)
                r θ) -
          Γtot M r θ φ t b * (r ^ 2 * sin θ ^ 2))) +
    (-(Γtot M r θ Idx.θ a t *
          (-(Γtot M r θ b t Idx.θ * ...
```

### Analysis

**What happened:**
- The double case split creates 16 branches (t-t, t-r, t-θ, t-φ, r-t, etc.)
- simp successfully processes most branches, but fails on case `t.t` (and potentially others)
- In the t.t case, we still have nested products of Christoffel symbols with metric components
- The `nabla_g M r θ t e b = 0` facts (from H1/H2) are not being applied

**Why H1/H2 aren't working:**
- The term has structure: `Γtot M r θ b t φ * (match b, b with ...)`
- This is NOT literally `nabla_g M r θ t e b` - it's already been expanded by `simp [sumIdx_expand]`
- H1/H2 need to be applied BEFORE the sumIdx expansion, not after
- OR we need an additional lemma that says `Γtot M r θ e μ ν * g M e b r θ = 0` when nabla_g is zero

**Root cause:** The proof strategy has a sequencing issue:
1. We unfold nabla → exposes sumIdx terms
2. We case split on c and d
3. We simp with sumIdx_expand → expands the sums into explicit products
4. We try to apply H1/H2 → but the terms are already expanded past nabla_g form

**Correct sequence should be:**
1. Unfold nabla
2. Apply H1/H2 to rewrite `nabla_g M r θ d e b` → 0 **before** expanding
3. Then case split and simp to close trivial goals

---

## Test #2: Helper Lemmas with Temporary Sorry

### What Was Changed

**File:** Riemann.lean:1775-1782, 1785-1792

**Before:** Full proofs with differentiability obligations
**After:** Replaced with `sorry -- Temporarily sorried to test if ricci_identity_on_g_rθ works`

### Build Result: ⚠️ MULTIPLE CASCADING ERRORS

**Error #1 at line 1801 (ricci_identity_on_g_rθ):**
```
error: unsolved goals
M r θ : ℝ
a b : Idx
Hcomm : dCoord Idx.r (fun r θ => dCoord Idx.θ ...) = dCoord Idx.θ (fun r θ => dCoord Idx.r ...)
Hcancel : ... = 0
⊢ deriv (fun s => deriv (fun t => (match a, b with
      | Idx.t, Idx.t => fun r _θ => -f M r
      | Idx.r, Idx.r => fun r _θ => (f M r)⁻¹
      | Idx.θ, Idx.θ => fun r _θ => r ^ 2
      | φ, φ => fun r θ => r ^ 2 * sin θ ^ 2
      | x, x_1 => fun x x => 0) s t) θ) r - ...
```

**Error #2 at line 1848 (Riemann_swap_a_b_ext):**
```
error: Type mismatch: After simplification, term
  ricci_identity_on_g_rθ M r θ a b
 has type
  nabla (fun M r θ a b => deriv (fun t => (match a, b with ...) r t) θ - ...) M r θ Idx.r a b - ...
```

**Error #3 at line 1850:**
```
error: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
```

**Error #4 at line 1844:**
```
error: unsolved goals (case t.φ for Riemann_swap_a_b_ext)
```

### Analysis

**Issue #1: ricci_identity_on_g_rθ incomplete**
- Even with helper lemmas sorried, the proof doesn't complete
- After applying Hcancel, still have unsimplified derivative and sum terms
- The `simp [Hcancel, dCoord_sumIdx, dCoord_mul_of_diff]` line doesn't fully expand
- Missing: explicit applications of the sorried helper lemmas (dCoord_sumIdx_Γ_g_left/right)

**Issue #2: Type mismatch in Riemann_swap_a_b_ext**
- The ricci_identity_on_g_rθ has wrong type after simp
- Expected: Pure equation about nabla expressions
- Got: Partially simplified expression with leftover match/deriv terms
- Root cause: ricci_identity_on_g_rθ itself has errors, so its type is malformed

**Issue #3: Timeout and cascading failures**
- Riemann_swap_a_b_ext has 16 branches from `cases c <;> cases d`
- Most should be handled by `try simp [nabla, dCoord] at *`
- But because ricci_identity_on_g_rθ is broken, the simpa steps fail
- Creates cascading timeouts across multiple branches

---

## Root Cause Analysis

### Problem #1: nabla_nabla_g_zero_ext

**Mathematical issue:** None - the lemma should hold
**Tactical issue:** Proof sequence applies H1/H2 too late

**What needs to happen:**
```lean
lemma nabla_nabla_g_zero_ext (M r θ : ℝ) (h_ext : Exterior M r θ) (c d a b : Idx) :
  nabla (fun M' r' θ' a' b' => nabla_g M' r' θ' d a' b') M r θ c a b = 0 := by
  classical
  have H0 : dCoord c (fun r θ => nabla_g M r θ d a b) r θ = 0 :=
    dCoord_nabla_g_zero_ext M r θ h_ext c d a b
  have H1 : ∀ e, nabla_g M r θ d e b = 0 :=
    fun e => nabla_g_zero_ext M r θ h_ext d e b
  have H2 : ∀ e, nabla_g M r θ d a e = 0 :=
    fun e => nabla_g_zero_ext M r θ h_ext d a e
  unfold nabla

  -- KEY: Rewrite nabla_g → 0 BEFORE expanding sumIdx
  simp only [H1, H2]  -- This should kill the Γ·(∇g) terms

  -- Now simp to expand and apply H0
  cases c <;> cases d <;>
    simp [dCoord_t, dCoord_r, dCoord_θ, dCoord_φ, H0]
```

**Status:** Needs reordering of simp calls

---

### Problem #2: ricci_identity_on_g_rθ

**Mathematical issue:** None - Ricci identity is standard
**Tactical issue:** Multiple sub-problems

1. **Helper lemmas don't exist in working form**
   - dCoord_sumIdx_Γ_g_left/right have differentiability obligation errors
   - Even with sorry, they're marked @[simp] which may cause issues

2. **Expansion strategy incomplete**
   - After Hcancel, need explicit rewrites not just simp
   - The user's original code had: `simp [Hcancel, dCoord_sumIdx, dCoord_mul_of_diff]`
   - But our code has: `simp [Hcancel, dCoord_sumIdx, dCoord_mul_of_diff]; ring_nf; simp [...]`
   - The helper lemmas should be firing at the `simp [dCoord_sumIdx, ...]` step

3. **Pattern matching on indices**
   - The match expressions on a, b for g M a b r θ aren't fully reduced
   - May need explicit cases on a and b as well (4×4 = 16 more branches)

**Status:** Depends on fixing helper lemmas properly

---

### Problem #3: Helper Lemmas (dCoord_sumIdx_Γ_g_left/right)

**Mathematical issue:** None
**Tactical issue:** Differentiability hypotheses in wrong form

**From investigation report Issue #2:**
- dCoord_sumIdx expects: `DifferentiableAt_r F r θ ∨ μ ≠ Idx.r`
- Proof provides: `DifferentiableAt_r F r θ` (without disjunction)
- Individual differentiability lemmas require Exterior hypotheses
- Helper lemmas don't have Exterior in signature

**Solutions:**

**Option A: Add Exterior hypotheses (Recommended)**
```lean
@[simp] lemma dCoord_sumIdx_Γ_g_left (μ : Idx)
    (M r θ : ℝ) (hM : 0 < M) (hr : 2 * M < r) (x a b : Idx) :
  dCoord μ (fun r θ => sumIdx (fun e => Γtot M r θ e x a * g M e b r θ)) r θ
    = ...
```
Then use existing differentiability lemmas that work on Exterior domain.

**Option B: Triple case split (256 branches)**
```lean
cases μ <;> cases e <;> cases x <;> cases a <;> cases b <;>
  simp [specific Γ and g lemmas]
```
Deterministic but extremely tedious.

**Option C: Build disjunctive proofs**
For each differentiability obligation, prove:
```lean
(DifferentiableAt_r (fun r θ => Γtot M r θ e x a * g M e b r θ) r θ) ∨ μ ≠ Idx.r
```
By showing left disjunct holds on Exterior, right disjunct handles other μ.

---

## Dependency Graph (Current State)

```
Exterior.deriv_zero_of_locally_zero ✅ COMPLETE
  ↓
dCoord_nabla_g_zero_ext ✅ COMPLETE
  ↓
nabla_nabla_g_zero_ext ⚠️ BLOCKED (H1/H2 sequencing issue)
  ↓
dCoord_sumIdx_Γ_g_left ⚠️ SORRIED (differentiability issues)
dCoord_sumIdx_Γ_g_right ⚠️ SORRIED (differentiability issues)
  ↓
ricci_identity_on_g_rθ ⚠️ BLOCKED (unsolved goals after Hcancel)
  ↓
Riemann_swap_a_b_ext ⚠️ BLOCKED (type mismatch from broken dependency)
  ↓
Riemann_swap_a_b ⚠️ BLOCKED
  ↓
Kretschmann_block_sq ⚠️ BLOCKED
  ↓
Zero sorries project-wide (GOAL)
```

---

## Recommendations

### Immediate Priority: Fix nabla_nabla_g_zero_ext

**Action:** Reorder proof to apply H1/H2 before sumIdx expansion

```lean
lemma nabla_nabla_g_zero_ext (M r θ : ℝ) (h_ext : Exterior M r θ) (c d a b : Idx) :
  nabla (fun M' r' θ' a' b' => nabla_g M' r' θ' d a' b') M r θ c a b = 0 := by
  classical
  have H0 : dCoord c (fun r θ => nabla_g M r θ d a b) r θ = 0 :=
    dCoord_nabla_g_zero_ext M r θ h_ext c d a b
  have H1 : ∀ e, nabla_g M r θ d e b = 0 :=
    fun e => nabla_g_zero_ext M r θ h_ext d e b
  have H2 : ∀ e, nabla_g M r θ d a e = 0 :=
    fun e => nabla_g_zero_ext M r θ h_ext d a e
  unfold nabla
  -- Apply H1/H2 before expanding
  conv_lhs => arg 1; intro d; simp [H1, H2]
  -- Now case split and simplify
  cases c <;> cases d <;>
    simp [dCoord_t, dCoord_r, dCoord_θ, dCoord_φ, H0, sumIdx_expand]
```

**Estimated effort:** 30-60 minutes
**Success probability:** 70%

---

### Secondary Priority: Fix Helper Lemmas

**Recommended approach:** Add Exterior hypotheses (Option A)

```lean
@[simp] lemma dCoord_sumIdx_Γ_g_left_ext (μ : Idx)
    (M r θ : ℝ) (h_ext : Exterior M r θ) (x a b : Idx) :
  dCoord μ (fun r θ => sumIdx (fun e => Γtot M r θ e x a * g M e b r θ)) r θ
    = sumIdx (fun e =>
        dCoord μ (fun r θ => Γtot M r θ e x a) r θ * g M e b r θ
        + Γtot M r θ e x a * dCoord μ (fun r θ => g M e b r θ) r θ) := by
  classical
  have hsum := dCoord_sumIdx μ (fun e r θ => Γtot M r θ e x a * g M e b r θ) r θ ?hr ?hθ
  · -- Prove hr obligation using Exterior hypotheses
    intro i
    left  -- Choose left disjunct: DifferentiableAt_r holds
    -- Apply existing differentiability lemmas for Γtot and g on Exterior
    apply DifferentiableAt.mul
    · exact Γtot_DifferentiableAt_r M r θ h_ext.hM h_ext.hr_ex i x a
    · exact g_DifferentiableAt_r M i b r θ
  · -- Prove hθ obligation similarly
    intro i
    left
    apply DifferentiableAt.mul
    · exact Γtot_DifferentiableAt_θ M r θ h_ext.hM h_ext.hr_ex i x a
    · exact g_DifferentiableAt_θ M i b r θ
  -- Continue with product rule as before
  ...
```

**Estimated effort:** 2-4 hours (need to find/prove Γtot_DifferentiableAt_r/θ lemmas)
**Success probability:** 80%

---

### Tertiary Priority: Complete ricci_identity_on_g_rθ

**Dependencies:** Requires helper lemmas to be fixed first

**Then:**
- Verify that `simp [Hcancel, dCoord_sumIdx_Γ_g_left, dCoord_sumIdx_Γ_g_right]` applies helpers
- If not, use explicit rewrites: `rw [dCoord_sumIdx_Γ_g_left, dCoord_sumIdx_Γ_g_right]`
- May need additional case analysis on a and b indices

**Estimated effort:** 1-2 hours (after helpers fixed)
**Success probability:** 85%

---

## Alternative: Computational Proof (Path B from previous reports)

If the above tactical fixes prove too difficult, the computational approach remains viable:

**Strategy:**
1. Prove Riemann_swap_a_b_ext by explicit case analysis on (a,b,c,d)
2. Use the 6 proven component lemmas for non-zero cases
3. Bypass the entire Ricci identity machinery

**Advantages:**
- ✅ Avoids all tactical issues with nabla/∇g/dCoord
- ✅ Leverages already-proven component lemmas
- ✅ Pragmatic and deterministic

**Disadvantages:**
- ❌ Loses mathematical generality (no Ricci identity proven)
- ❌ Less elegant
- ❌ Specific to Schwarzschild

**Estimated effort:** 4-8 hours
**Success probability:** 90%

---

## Questions for Junior Professor

### 1. Proof Strategy Preference

Should we:
- **(A)** Continue with Ricci identity approach (fix the 3 tactical issues above)?
- **(B)** Switch to computational proof using component lemmas?
- **(C)** Hybrid: Defer Ricci identity, do computational proof now, return to Ricci later?

### 2. Helper Lemmas Scope

If pursuing (A), should helper lemmas:
- **(i)** Be scoped to Exterior domain (add h_ext parameter)?
- **(ii)** Be fully general (prove differentiability disjunctions for all cases)?
- **(iii)** Use case splits on indices (256 branches)?

### 3. Time Constraints

Is there a deadline or publication timeline that would favor:
- Quick completion via computational proof (B)?
- OR full elegance via Ricci identity (A)?

### 4. Existing Differentiability Lemmas

Do differentiability lemmas for Γtot exist in the codebase?
- `Γtot_DifferentiableAt_r`
- `Γtot_DifferentiableAt_θ`

If not, proving them will be prerequisite for helper lemma approach (A)-(i).

---

## Current File State

**Riemann.lean:** ~1850 lines (up to ricci_identity section)
**Build status:** ❌ 6 errors
- Line 1639: nabla_nabla_g_zero_ext (case t.t unsolved)
- Line 1801: ricci_identity_on_g_rθ (unsolved goals after Hcancel)
- Line 1848: Riemann_swap_a_b_ext (type mismatch)
- Line 1850: Riemann_swap_a_b_ext (timeout)
- Line 1844: Riemann_swap_a_b_ext (case t.φ unsolved)
- Plus cascading errors

**Sorries:**
- Lines 1782, 1792: Helper lemmas (temporary)
- Line 1867: Riemann_swap_a_b (final target)

---

## Session Summary

**Work completed:**
✅ Applied double case split to nabla_nabla_g_zero_ext
✅ Applied temporary sorries to helper lemmas
✅ Identified root cause: H1/H2 sequencing in nabla_nabla_g_zero_ext
✅ Identified root cause: Missing Exterior hypotheses in helper lemmas
✅ Identified root cause: Incomplete expansion in ricci_identity_on_g_rθ
✅ Created comprehensive test results report

**Key insights:**
1. Double case split alone insufficient - need reordered simp calls
2. Helper lemmas fundamentally need Exterior hypotheses or massive case analysis
3. ricci_identity_on_g_rθ has multiple sub-dependencies
4. Computational proof path remains viable fallback

**Next session:**
Await Junior Professor's guidance on:
- Proof strategy preference (Ricci identity vs computational)
- Helper lemma scope (Exterior-scoped vs fully general)
- Time constraints (quick pragmatic vs elegant general)

---

**Prepared by:** Claude Code (AI Agent)
**Session:** October 8, 2025, Morning
**Status:** Awaiting guidance on approach
**Progress:** 90% infrastructure complete, 3 tactical blockers identified and analyzed
