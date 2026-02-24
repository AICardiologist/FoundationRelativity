# JP Patch Implementation - Iteration Report (October 14, 2025)

**Status:** Partial success - PATCH 1 works, PATCH 2 has tactical timeouts

**Summary:** Applied JP's three patches with minor modifications. Schwarzschild.lean builds cleanly. Riemann.lean has timeouts in the diagonal case helper lemmas. Need JP's guidance on simpler diagonal metric collapse approach.

---

## PATCH 1: Schwarzschild.lean - ✅ SUCCESS

### What Was Applied (Lines 1578-1603)

```lean
/-!  JP's commutator-collapse helpers for h_fiber diagonal case (Oct 14, 2025)  -/

-- One-shot diagonal/off-diagonal fact for the Schwarzschild metric.
-- Avoids 16 subgoals each time we just need "g_{kb} = 0 when k ≠ b".
@[simp] lemma g_offdiag (M r θ : ℝ) {i j : Idx} (hij : i ≠ j) :
  g M i j r θ = 0 := by
  cases i <;> cases j <;> (first | exfalso; exact hij rfl | simp [g])

/-- In Schwarzschild, for the `r`-branch commutator
    ∑_λ Γ^k_{rλ} Γ^λ_{θa} collapses to the single λ = k term. -/
@[simp] lemma comm_r_sum_collapse (M r θ : ℝ) (k a : Idx) :
  sumIdx (fun lam =>
    Γtot M r θ k Idx.r lam * Γtot M r θ lam Idx.θ a)
  =
  Γtot M r θ k Idx.r k * Γtot M r θ k Idx.θ a := by
  classical
  cases k <;> cases a <;> simp [sumIdx_expand, Γtot, mul_zero, zero_mul, add_zero, zero_add]

/-- **Correct θ-branch collapse.**
    In Schwarzschild, for the `θ`-branch commutator
    ∑_λ Γ^k_{θλ} Γ^λ_{ra} collapses to the single λ = a term (not λ = k). -/
@[simp] lemma comm_θ_sum_collapse (M r θ : ℝ) (k a : Idx) :
  sumIdx (fun lam =>
    Γtot M r θ k Idx.θ lam * Γtot M r θ lam Idx.r a)
  =
  Γtot M r θ k Idx.θ a * Γtot M r θ a Idx.r a := by
  classical
  cases k <;> cases a <;> simp [sumIdx_expand, Γtot, mul_zero, zero_mul, add_zero, zero_add]
```

### Modifications from JP's Original

1. **g_offdiag**: Changed from `cases i <;> cases j <;> simp [g, hij]` to use `(first | exfalso; exact hij rfl | simp [g])`
   - **Why**: The diagonal cases (i=i) have `hij : i ≠ i`, which is `(i = i) → False`. Needed `exfalso; exact hij rfl` to derive contradiction.
   - **Result**: ✅ Compiles cleanly

2. **comm_r_sum_collapse**: Added explicit simp lemmas `Γtot, mul_zero, zero_mul, add_zero, zero_add`
   - **Why**: JP's `simp [sumIdx_expand]` alone didn't reduce the Γtot zeros after expansion
   - **Result**: ✅ Closes in one line

3. **comm_θ_sum_collapse**: Same modification as comm_r
   - **Why**: Same reason
   - **Result**: ✅ Closes in one line, **correct index** (λ=a not λ=k)

### Build Status

```
✅ Schwarzschild.lean builds successfully
✅ All 3 lemmas proven
✅ No sorries remaining in this section
```

---

## PATCH 2: Riemann.lean - ⏳ PARTIAL (Timeouts)

### Off-Diagonal Case - ✅ WORKS (Lines 6337-6356)

Applied JP's O(1) approach exactly as specified:

```lean
· ------------------------------------------------------------------
  -- Case k ≠ b: OFF-DIAGONAL
  ------------------------------------------------------------------
  classical
  -- (1) Manufacture the global "g_kb is identically 0" as a *function*,
  --     not just at (r, θ). This lets us kill both dCoord-terms cheaply.
  have hg_fun : (fun r θ => g M k b r θ) = (fun _ _ => 0) := by
    funext r' θ'
    simpa [g] using (g_offdiag M r' θ' (i := k) (j := b) hkb)

  -- (2) Pointwise and derivative zeros follow immediately.
  have hg0  : g M k b r θ = 0 := by simpa using congrArg (fun F => F r θ) hg_fun
  have hgr  : dCoord Idx.r (fun r θ => g M k b r θ) r θ = 0 := by
    simpa [hg_fun, dCoord_r, deriv_const]
  have hθg  : dCoord Idx.θ (fun r θ => g M k b r θ) r θ = 0 := by
    simpa [hg_fun, dCoord_θ, deriv_const]

  -- (3) Now the whole goal is 0 = 0:
  --     LHS terms all carry g_kb or ∂g_kb; RHS is kernel * g_kb.
  simp [hg0, hgr, hθg]
```

**Status**: Compiles if diagonal case is commented out (timeout at line 6357 is from diagonal case failing earlier)

---

### Diagonal Case - ❌ TIMEOUT (Lines 6276-6335)

#### What Was Applied

```lean
· ------------------------------------------------------------------
  -- Case k = b: DIAGONAL
  ------------------------------------------------------------------
  subst hkb
  classical
  -- Expand ∂g_kk by the *small* compat shape, then fold with the diagonal g.
  -- (We avoid any AC: two precise rewrites + local simp.)
  have Hr := dCoord_g_via_compat_ext M r θ h_ext Idx.r k k
  have Hθ := dCoord_g_via_compat_ext M r θ h_ext Idx.θ k k
  -- Fold each sum against the diagonal metric using the two collapse lemmas you already have.
  have Hr' :
    dCoord Idx.r (fun r θ => g M k k r θ) r θ
      = Γtot M r θ k Idx.r k * g M k k r θ
      + Γtot M r θ k Idx.r k * g M k k r θ := by
    -- ∂_r g_kk = Σ_e Γ^e_{rk} g_ek + Σ_e Γ^e_{rk} g_ke
    -- Each sum collapses to Γ^k_{rk} g_kk by diagonality.
    rw [Hr]
    -- Both sums collapse because g is diagonal
    have sum1 : sumIdx (fun e => Γtot M r θ e Idx.r k * g M e k r θ) = Γtot M r θ k Idx.r k * g M k k r θ := by
      cases k <;> simp [sumIdx_expand, g, Γtot, mul_zero, zero_mul, add_zero, zero_add]
    have sum2 : sumIdx (fun e => Γtot M r θ e Idx.r k * g M k e r θ) = Γtot M r θ k Idx.r k * g M k k r θ := by
      cases k <;> simp [sumIdx_expand, g, Γtot, mul_zero, zero_mul, add_zero, zero_add]
    rw [sum1, sum2]
  have Hθ' :
    dCoord Idx.θ (fun r θ => g M k k r θ) r θ
      = Γtot M r θ k Idx.θ k * g M k k r θ
      + Γtot M r θ k Idx.θ k * g M k k r θ := by
    -- ∂_θ g_kk, same story.
    rw [Hθ]
    have sum1 : sumIdx (fun e => Γtot M r θ e Idx.θ k * g M e k r θ) = Γtot M r θ k Idx.θ k * g M k k r θ := by
      cases k <;> simp [sumIdx_expand, g, Γtot, mul_zero, zero_mul, add_zero, zero_add]
    have sum2 : sumIdx (fun e => Γtot M r θ e Idx.θ k * g M k e r θ) = Γtot M r θ k Idx.θ k * g M k k r θ := by
      cases k <;> simp [sumIdx_expand, g, Γtot, mul_zero, zero_mul, add_zero, zero_add]
    rw [sum1, sum2]

  -- Now rewrite the *goal state* produced by prod_r/prod_θ using these
  -- two pointwise equalities (no AC, only fold lemmas).
  -- After these rewrites, what remains is exactly the RiemannUp kernel * g_kk,
  -- once we drop in the commutator collapses (r-branch → λ=k, θ-branch → λ=a).
  have :
    ( dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a) r θ * g M k k r θ
      + Γtot M r θ k Idx.θ a * dCoord Idx.r (fun r θ => g M k k r θ) r θ )
    - ( dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a) r θ * g M k k r θ
        + Γtot M r θ k Idx.r a * dCoord Idx.θ (fun r θ => g M k k r θ) r θ )
    =
    ( dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a) r θ
      - dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a) r θ
      + sumIdx (fun lam => Γtot M r θ k Idx.r lam * Γtot M r θ lam Idx.θ a)
      - sumIdx (fun lam => Γtot M r θ k Idx.θ lam * Γtot M r θ lam Idx.r a) )
      * g M k k r θ := by
    -- Rewrite ∂g by Hr'/Hθ', fold, and then collapse the commutator sums.
    -- Everything is pointwise and local; no associative-commutative search.
    simp [Hr', Hθ', fold_add_left, fold_sub_right, sub_eq_add_neg,
          -- r-branch: λ = k
          comm_r_sum_collapse,
          -- θ-branch: λ = a  (the *fixed* index on the kernel)
          comm_θ_sum_collapse]

  -- Done: the equality above *is* the target after prod_r/prod_θ at k=b.
  exact this
```

#### Timeout Errors

```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:6297:22:
  Tactic `simp` failed with a nested error:
  (deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000) has been reached

error: Papers/P5_GeneralRelativity/GR/Riemann.lean:6289:50:
  (deterministic) timeout at `«tactic execution»`, maximum number of heartbeats (200000) has been reached

error: Papers/P5_GeneralRelativity/GR/Riemann.lean:6315:6:
  (deterministic) timeout at `«tactic execution»`, maximum number of heartbeats (200000) has been reached
```

**Line 6297**: `sum2` helper in Hr' (with cases k)
**Line 6289**: The `Hr'` have statement itself
**Line 6315**: The big simp with commutator collapses

#### Root Cause

JP's patch referenced `sumIdx_Γ_g_left` and `sumIdx_Γ_g_right` which don't exist in the codebase. I tried to prove the diagonal metric collapse inline with:

```lean
cases k <;> simp [sumIdx_expand, g, Γtot, mul_zero, zero_mul, add_zero, zero_add]
```

This expands to 4 cases × 2 sums = 8 simps, each with complex Γtot pattern matching → timeout.

#### What JP Probably Meant

JP likely intended for `sumIdx_Γ_g_left/right` to be **simple helper lemmas** like:

```lean
lemma sumIdx_Γ_g_diag_left (M r θ : ℝ) (x k : Idx) :
  sumIdx (fun e => Γtot M r θ e x k * g M e k r θ) = Γtot M r θ k x k * g M k k r θ := by
  sorry  -- How to prove this efficiently?

lemma sumIdx_Γ_g_diag_right (M r θ : ℝ) (x k : Idx) :
  sumIdx (fun e => Γtot M r θ e x k * g M k e r θ) = Γtot M r θ k x k * g M k k r θ := by
  sorry  -- How to prove this efficiently?
```

Then use:
```lean
have Hr' : ... := by
  rw [Hr]
  simp [sumIdx_Γ_g_diag_left, sumIdx_Γ_g_diag_right]
```

---

## PATCH 3: Final Sum-Level Lift - ✅ APPLIED (Lines 6359-6375)

```lean
-- Lift the pointwise identity to a sum and recognize the kernel
classical
have h_pt : (fun k =>
    dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a * g M k b r θ) r θ
  - dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a * g M k b r θ) r θ)
  =
  (fun k =>
    ( dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a) r θ
    - dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a) r θ
    + sumIdx (fun lam => Γtot M r θ k Idx.r lam * Γtot M r θ lam Idx.θ a)
    - sumIdx (fun lam => Γtot M r θ k Idx.θ lam * Γtot M r θ lam Idx.r a) )
    * g M k b r θ) := by
  funext k; exact h_fiber k

-- Now sum both sides over k and recognize RiemannUp kernel * g via the kernel lemma.
have h_sum := congrArg (fun F : Idx → ℝ => sumIdx F) h_pt
simpa [RiemannUp_kernel_mul_g] using h_sum
```

**Status**: Applied exactly as JP specified. Will compile once h_fiber closes.

---

## Current Build Status

**Schwarzschild.lean**: ✅ Clean (0 errors, warnings only)

**Riemann.lean**: ❌ Build fails with timeouts:
- Line 6289: Hr' have statement
- Line 6297: sum2 in Hr' proof
- Line 6315: Main diagonal case simp

---

## Questions for JP

### Q1: sumIdx_Γ_g Helper Lemmas

You referenced `sumIdx_Γ_g_left` and `sumIdx_Γ_g_right` in your patch comments. These don't exist in the codebase.

**Did you mean:**
- A) These should be new lemmas I add to Schwarzschild.lean before the commutator collapses?
- B) Something else that already exists under a different name?
- C) These were just conceptual labels, and the simp should work without them?

**If (A), what's the efficient proof pattern?**

The naive approach (cases k + full simp) times out. Should I:
- Use a more targeted simp set?
- Prove for each specific k value manually?
- Use a different lemma that relates ∑_e Γ^e_{xk} g_ek to the diagonal?

### Q2: Diagonal Metric Collapse Strategy

After `rw [Hr]`, I have:
```
∂_r g_kk = Σ_e Γ^e_{rk} g_ek + Σ_e Γ^e_{rk} g_ke
```

I need to show both sums collapse to `Γ^k_{rk} g_kk`.

**Current approach (times out):**
```lean
cases k <;> simp [sumIdx_expand, g, Γtot, mul_zero, zero_mul, add_zero, zero_add]
```

**What's the fast pattern?** Should I:
- Add @[simp] lemmas for specific index patterns?
- Use conv to rewrite inside the sum before expanding?
- Apply diagonality of g before sumIdx_expand?

### Q3: Is There a Shortcut?

Looking at the goal structure, after `subst hkb` we're trying to show:

```
[∂_r Γ · g + Γ · ∂_r g] - [∂_θ Γ · g + Γ · ∂_θ g] = [∂_r Γ - ∂_θ Γ + commutators] · g
```

**Is there a lemma that directly relates compat sums to commutator sums in the diagonal case?**

Or do we really need to go through the full Hr'/Hθ' construction?

---

## What Works So Far

1. ✅ Product rule (prod_r, prod_θ) - Lines 6242-6268
2. ✅ by_cases k=b split - Line 6275
3. ✅ Off-diagonal case closes - Lines 6337-6356
4. ✅ g_offdiag lemma (with exfalso fix) - Schwarzschild.lean:1580
5. ✅ Both commutator collapses (with explicit zeros) - Schwarzschild.lean:1586, 1597
6. ✅ Final sum-level lift structure - Lines 6359-6375

---

## What Needs Fix

1. ❌ Diagonal case Hr' proof - timeout in sum collapse helpers
2. ❌ Diagonal case Hθ' proof - same issue
3. ❌ Diagonal case main simp - likely will work once Hr'/Hθ' close

---

## Minimal Reproducer for Timeout

```lean
-- This times out:
have sum1 : sumIdx (fun e => Γtot M r θ e Idx.r k * g M e k r θ) = Γtot M r θ k Idx.r k * g M k k r θ := by
  cases k <;> simp [sumIdx_expand, g, Γtot, mul_zero, zero_mul, add_zero, zero_add]
```

**After `cases k`**, we get 4 goals (t, r, θ, φ). Each `simp` expands:
- `sumIdx_expand`: 4-term sum
- `g`: Diagonal definition with catch-all
- `Γtot`: Sparse definition with catch-all

Even though most terms should reduce to zero, the simp search space is too large.

---

## Suggested Next Step

**Option A**: JP provides the efficient proof for the two `sumIdx_Γ_g_*` helper lemmas.

**Option B**: JP provides a different tactical approach for the diagonal case that avoids inline sum collapse proofs.

**Option C**: Add `set_option maxHeartbeats 400000` locally and retry (may just be slow, not stuck).

---

## Code Locations for JP

**Schwarzschild.lean**:
- Lines 1578-1603: PATCH 1 (working)

**Riemann.lean**:
- Lines 6242-6268: Product rule (working)
- Lines 6276-6335: Diagonal case (timeouts at 6289, 6297, 6315)
- Lines 6337-6356: Off-diagonal case (working if diagonal fixed)
- Lines 6359-6375: Sum-level lift (will work once h_fiber closes)

---

## Summary

**Mathematical structure**: ✅ Correct (JP's case-split approach is sound)
**Off-diagonal branch**: ✅ Working (O(1) approach perfect)
**Commutator lemmas**: ✅ Working (with explicit zero handling)
**Diagonal branch**: ⏳ Needs tactical optimization for sum collapses

**Next**: Awaiting JP's guidance on efficient diagonal metric collapse pattern.

---

## Build Command Used

```bash
lake build Papers.P5_GeneralRelativity.GR.Riemann
```

**Last error location**: Line 6297 in sum2 proof within Hr'

**Timeout threshold**: 200000 heartbeats (default)

**Estimated completion**: Once diagonal case tactical fix applied, expect all sorries to close (5 total reduction: 2 in Schwarzschild + 3 in Riemann).
