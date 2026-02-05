# Final Report - Sum-Level Approach Investigation (October 13, 2025)

**TO:** JP (Junior Professor)
**FROM:** Claude Code (AI Agent)
**DATE:** October 13, 2025 (End of Session)
**RE:** Results of Sum-Level Step 5 Implementation Attempt
**BUILD STATUS:** ✅ Clean (with sorry at line 6187)
**SORRY COUNT:** 11 total (baseline, no regression)

---

## EXECUTIVE SUMMARY

Per your October 13 request, I implemented your sum-level approach for Step 5 of `regroup_right_sum_to_RiemannUp_NEW`. The implementation reveals that **the same fundamental AC explosion issue affects both fiberwise and sum-level approaches**.

**Key finding:** The blocker is not fiberwise vs sum-level structure, but rather the **RiemannUp recognition step** which hits AC timeout regardless of proof strategy.

---

## WHAT WAS IMPLEMENTED

### 1. Helper Lemmas (Lines 125-129) ✅ SUCCESS

```lean
/-- Group as `(X + Y) - Z = (X - Z) + Y`. No AC, stable shape. -/
@[simp] lemma group_add_sub (X Y Z : ℝ) : X + Y - Z = (X - Z) + Y := by ring

/-- Group as `X - (Y + Z) = (X - Y) - Z`. No AC, stable shape. -/
@[simp] lemma group_sub_add (X Y Z : ℝ) : X - (Y + Z) = (X - Y) - Z := by ring
```

**Status:** ✅ Compile cleanly and are available for use.

---

### 2. Right-Slot Refold Helpers (Lines 6100-6124) ✅ SUCCESS

```lean
have refold_r_right (k : Idx) :
    Γtot M r θ k Idx.θ a
      * sumIdx (fun lam => Γtot M r θ lam Idx.r b * g M k lam r θ)
  =
    Γtot M r θ k Idx.θ a
      * dCoord Idx.r (fun r θ => g M k b r θ) r θ
  - Γtot M r θ k Idx.θ a
      * sumIdx (fun lam => Γtot M r θ lam Idx.r k * g M lam b r θ) := by
  have base := compat_refold_r_kb M r θ h_ext k b
  simpa [mul_sub, sumIdx_pull_const_left] using
    congrArg (fun x => Γtot M r θ k Idx.θ a * x) base

have refold_θ_right (k : Idx) :
    Γtot M r θ k Idx.r a
      * sumIdx (fun lam => Γtot M r θ lam Idx.θ b * g M k lam r θ)
  =
    Γtot M r θ k Idx.r a
      * dCoord Idx.θ (fun r θ => g M k b r θ) r θ
  - Γtot M r θ k Idx.r a
      * sumIdx (fun lam => Γtot M r θ lam Idx.θ k * g M lam b r θ) := by
  have base := compat_refold_θ_kb M r θ h_ext k b
  simpa [mul_sub, sumIdx_pull_const_left] using
    congrArg (fun x => Γtot M r θ k Idx.r a * x) base
```

**Status:** ✅ Compile cleanly. Successfully use existing `compat_refold_r_kb` and `compat_refold_θ_kb` lemmas with correct slot order.

---

### 3. Weighted Lift and Compat Expansion (Lines 6127-6129) ✅ SUCCESS

```lean
-- Start from the weighted identity (lift h_fold_fiber to sum level)
have h_weighted := congrArg (fun F : Idx → ℝ => sumIdx F) h_fold_fiber

-- Expand compat under the outer sum
simp_rw [dCoord_g_via_compat_ext M r θ h_ext] at h_weighted
```

**Status:** ✅ Works perfectly. The weighted-first lift and compat expansion compile without issues.

---

### 4. Refold Application (Line 6145) ✅ SUCCESS

```lean
-- 5.3 Apply the two right-slot refolds under the outer sum
have Hr := refold_r_right
have Hθ := refold_θ_right
simp_rw [Hr, Hθ] at h_weighted
```

**Status:** ✅ Successfully applies the refold helpers under the outer sum using `simp_rw`.

---

## WHAT DIDN'T WORK

### Issue 1: Distribution Step (Line 6132) ❌ FAILED

**Your code:**
```lean
simp_rw [mul_add, add_mul, sub_eq_add_neg] at h_weighted
```

**Error:** `'simp' made no progress`

**Diagnosis:** After compat expansion, the expression is already in a form that doesn't match `mul_add` or `add_mul` patterns.

**Workaround applied:**
```lean
try simp_rw [mul_add] at h_weighted
try simp_rw [add_mul] at h_weighted
simp_rw [sub_eq_add_neg] at h_weighted
```

---

### Issue 2: Pulling Constants Through Sums (Line 6138) ❌ FAILED

**Your code:**
```lean
simp_rw [sumIdx_pull_const_right] at h_weighted
```

**Error:** `'simp' made no progress`

**Diagnosis:** The Γ factors may already be in the correct position relative to inner sums, or the pattern doesn't match the actual expression structure.

**Workaround applied:**
```lean
try simp_rw [sumIdx_pull_const_right] at h_weighted
try simp_rw [sumIdx_pull_const_left] at h_weighted
```

---

### Issue 3: Grouping Lemmas (Line 6148) ❌ FAILED

**Your code:**
```lean
simp only [group_add_sub, group_sub_add] at h_weighted
```

**Error:** `'simp' made no progress`

**Diagnosis:** The expression form after refold application doesn't have the specific patterns `(X + Y) - Z` or `X - (Y + Z)` that these lemmas target.

**Workaround applied:**
```lean
try simp only [group_add_sub, group_sub_add] at h_weighted
```

---

### Issue 4: Fold Lemmas (Line 6151) ❌ FAILED

**Your code:**
```lean
simp only [fold_add_left, fold_sub_right] at h_weighted
```

**Error:** `'simp' made no progress`

**Diagnosis:** Similar to grouping lemmas - the expression form doesn't match the expected patterns.

**Workaround applied:**
```lean
try simp only [fold_add_left, fold_sub_right] at h_weighted
```

---

### Issue 5: RiemannUp Recognition (Line 6170) ❌ TIMEOUT

**Your code:**
```lean
have h_R_sum :
  sumIdx (fun k =>
    ( dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a) r θ
    - dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a) r θ
    + sumIdx (fun lam => Γtot M r θ k Idx.r lam * Γtot M r θ lam Idx.θ a)
    - sumIdx (fun lam => Γtot M r θ k Idx.θ lam * Γtot M r θ lam Idx.r a) )
    * g M k b r θ)
  =
  sumIdx (fun k => RiemannUp M r θ k a Idx.r Idx.θ * g M k b r θ) := by
  classical
  simp [RiemannUp, sub_eq_add_neg, sumIdx]
```

**Error:**
```
(deterministic) timeout at `simp`, maximum number of heartbeats (200000) has been reached
```

**Diagnosis:** This is the **same AC explosion** that affected the fiberwise approach. Even with `sumIdx` expansion, `simp` explores a huge search space when trying to match the LHS to the RHS.

**Critical insight:** The problem is **not** fiberwise vs sum-level structure. The problem is that **recognizing RiemannUp triggers AC explosion** regardless of how we structure the proof.

---

## ROOT CAUSE ANALYSIS

### The Core Problem

After all the tactical manipulations (compat expansion, refold application, grouping, folding), the `h_weighted` hypothesis contains an expression of the form:

```
sumIdx (fun k => [complex expression involving dCoord, Γ, g, and nested sums])
= sumIdx (fun k => [another complex expression])
```

The goal is to show this equals:

```
sumIdx (fun k => RiemannUp M r θ k a Idx.r Idx.θ * g M k b r θ)
```

The issue is that `simp [RiemannUp, sub_eq_add_neg, sumIdx]` attempts to:
1. Unfold `RiemannUp` definition
2. Unfold `sumIdx` to `Finset.sum`
3. Match the LHS to the RHS using AC-normalization

This search space is **exponentially large** in the number of terms, leading to timeout.

### Why Generic Tactics Fail

1. **`simp [RiemannUp, ...]`**: Hits AC explosion (timeout)
2. **`ring`**: Can't handle `dCoord` and `sumIdx` structure
3. **`abel`**: Can't handle non-additive operations
4. **Pattern matching with `rw`**: Requires exact syntactic form

### Comparison to Fiberwise Approach

**Fiberwise approach (failed):**
- Prove `∀ k, [LHS k] = RiemannUp M r θ k a Idx.r Idx.θ * g M k b r θ`
- Failed because cleanup with AC lemmas hit timeout

**Sum-level approach (failed):**
- Work at sum level: `sumIdx [LHS] = sumIdx [RHS]`
- Failed because RiemannUp recognition with AC lemmas hit timeout

**Lesson:** Both approaches fail at the **same step** - recognizing the RiemannUp pattern requires AC lemmas that cause timeout.

---

## COMPARISON TO LEFT REGROUP (Which Works)

The LEFT regroup lemma `regroup_left_sum_to_RiemannUp_OLD` (lines 2678-2850) **successfully completes** using:

1. **Fiberwise compat expansion** (not sum-level)
2. **Manual Fubini swaps** with helper lemmas (H₁, H₂)
3. **Targeted `rw` for kk_refold** (not `simp`)
4. **Final `ring`** to close (works because expression is pure algebraic)

**Key difference:** The OLD approach uses **expression-specific tactical lemmas** that match the exact syntactic form produced by the codebase, rather than generic patterns.

---

## TECHNICAL LESSONS LEARNED

### Lesson 1: Drop-In Generic Code Requires Expression Alignment

Your sum-level approach is mathematically sound and elegant. The issue is that generic tactical code (written without seeing our specific codebase) makes assumptions about syntactic forms that don't match our reality.

**Your assumptions:**
1. After compat expansion, terms need distribution with `mul_add`, `add_mul`
2. Γ factors need to be pulled through inner sums
3. Expression needs grouping with `group_add_sub`, `group_sub_add`
4. Products need folding with `fold_add_left`, `fold_sub_right`
5. RiemannUp recognition is deterministic with `simp [RiemannUp, sumIdx]`

**Our reality:**
1. Expression is already distributed (or in different form)
2. Γ factors are already in correct position (or different pattern)
3. Grouping patterns don't match actual form
4. Folding patterns don't match actual form
5. RiemannUp recognition hits AC explosion

### Lesson 2: AC Explosion is Not Structure-Dependent

Both fiberwise and sum-level approaches fail at RiemannUp recognition. This suggests the problem is **independent of proof structure** and is instead about:
- The complexity of the expressions involved
- The number of AC-equivalent orderings
- Lean's simp search strategy

### Lesson 3: Working Code Uses Expression-Specific Tactics

The OLD LEFT regroup works because it uses:
- **Custom helper lemmas** (H₁, H₂ for Fubini swaps)
- **Targeted `rw`** that match specific patterns
- **Minimal use of AC lemmas**

This suggests we need to **write custom tactics that match our specific expression forms**, not generic patterns.

---

## THREE PATHS FORWARD

### Path A: Expression Dump (Recommended)

**What to do:**

1. Add trace after line 6145 (after refold application):
```lean
simp_rw [Hr, Hθ] at h_weighted
trace "{h_weighted}"
sorry
```

2. Read the trace output to see **exact syntactic form** of `h_weighted`

3. Write **expression-specific tactical lemmas** that:
   - Match the actual LHS form exactly
   - Transform it step-by-step to RiemannUp form
   - Avoid AC lemmas that cause explosion

**Pros:**
- Addresses root cause directly
- Will definitely work (we control both LHS and RHS)
- Maintains weighted-first elegance

**Cons:**
- Requires one more debugging iteration
- May reveal expression is too complex to fold simply
- Requires writing custom tactical lemmas

**Estimated effort:** 2-4 hours after seeing trace

---

### Path B: Revert to OLD Working Pattern (Fastest)

**What to do:**

Replace lines 6100-6187 with OLD regroup approach from lines 2678-2850:

```lean
-- OLD fiberwise approach (known working)
have h_kk : ∀ k,
  dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a * g M k b r θ) r θ
  - dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a * g M k b r θ) r θ
  = RiemannUp M r θ k a Idx.r Idx.θ * g M k b r θ := by
    intro k
    -- Use OLD tactics: pointwise compat, Fubini H₁/H₂, kk_refold, ring
    [Copy OLD tactical sequence with index adaptations]

have := congrArg (fun F => sumIdx F) (funext h_kk)
simpa using this
```

**Pros:**
- Guaranteed to work (OLD code compiles)
- No dependency on expression form matching
- Can be implemented immediately
- Proven approach

**Cons:**
- More verbose than weighted-first
- Requires Fubini swap lemmas
- Doesn't use your elegant fold pattern
- Not as mathematically clean

**Estimated effort:** 1-2 hours (mostly adaptation)

---

### Path C: Constraint-Based RiemannUp Recognition

**What to do:**

Instead of using `simp [RiemannUp, sumIdx]` (which hits AC explosion), write a **constraint-based matcher** that:

1. Manually unfolds RiemannUp once
2. Uses `conv` to isolate each term
3. Matches each term individually with `rfl` or `ring`
4. Combines with targeted lemmas

**Example:**
```lean
have h_R_sum : [LHS] = [RHS] := by
  classical
  ext k
  unfold RiemannUp sumIdx
  conv_lhs => [navigate to each term]
  conv_rhs => [navigate to corresponding term]
  rfl <;> ring
```

**Pros:**
- Avoids AC explosion by controlling search space
- More deterministic than `simp`
- Can be made robust to expression form

**Cons:**
- Requires detailed knowledge of expression structure
- More tedious to write
- May not generalize well

**Estimated effort:** 3-5 hours (experimental)

---

## RECOMMENDATION

**For immediate progress:** Implement **Path B** (OLD regroup pattern)

**Rationale:**
1. We've now tested **both** your fiberwise and sum-level approaches
2. Both hit the **same AC explosion** at RiemannUp recognition
3. Path A requires expression dump and custom tactical development
4. Path B is proven, self-contained, and can be done immediately
5. We can always refactor to weighted-first later if Path A succeeds

**For long-term elegance:** Eventually pursue **Path A** (after expression dump)

**For research interest:** Consider **Path C** as investigation into Lean's AC handling

---

## CURRENT CODE STATE

**File:** `GR/Riemann.lean`

**Working sections:**
- Lines 125-129: ✅ group_add_sub, group_sub_add helpers
- Lines 6060-6091: ✅ pair_θ_fold_comm successfully implemented
- Lines 6100-6124: ✅ refold_r_right, refold_θ_right compile cleanly
- Lines 6127-6129: ✅ Weighted lift and compat expansion
- Lines 6145: ✅ Refold application with simp_rw

**Blocked section:**
- Lines 6131-6187: ⏳ Distribution, grouping, folding, and RiemannUp recognition all fail

**Build:** ✅ Clean (0 compilation errors)
**Sorry count:** 11 (same as baseline, no regression)

---

## QUESTIONS FOR JP

1. **AC Explosion:** Do you have insights into why RiemannUp recognition hits AC explosion in both fiberwise and sum-level approaches? Is there a known Lean 4 pattern for avoiding this?

2. **Expression Dump:** Would you like me to provide an expression dump of `h_weighted` after line 6145? This would show the exact syntactic form and might reveal why generic patterns don't match.

3. **OLD vs NEW:** The OLD regroup uses Fubini swaps + targeted rw + ring. Do you see a path to adapt this proven approach to RIGHT regroup (with index swaps a ↔ b)?

4. **Alternative Strategy:** Should we consider a completely different approach, such as:
   - Using `conv` tactics to navigate expression structure?
   - Writing custom RiemannUp recognizer that doesn't use AC lemmas?
   - Proving a meta-lemma about sum-level pattern matching?

5. **Acceptance Criteria:** If Path B (OLD pattern) successfully completes the proof, would that be acceptable for the paper? Or do you consider the weighted-first approach essential?

---

## GRATITUDE

Thank you for the detailed sum-level approach. The investigation was valuable because it revealed that:
1. ✅ Your refold helpers work perfectly
2. ✅ Weighted-first lift is elegant and compiles
3. ✅ simp_rw under binders works as expected
4. ❌ The blocker is **RiemannUp recognition**, not proof structure

This narrows the problem significantly and clarifies the path forward.

---

## FILES CREATED THIS SESSION

1. **FINAL_REPORT_JP_SUM_LEVEL_OCT13.md** (this file)
   - Complete investigation of sum-level approach
   - Detailed error analysis
   - Three clear paths forward

2. **DIAGNOSTIC_REPORT_JP_OCT13.md** (earlier)
   - Investigation of fiberwise approach
   - Same AC explosion discovered

3. **FINAL_SUMMARY_OCT13.md** (earlier)
   - Session summary before sum-level attempt

4. **STATUS_OPTION_C_ATTEMPT_OCT13.md** (earlier)
   - Investigation of slot-swapped lemmas

5. **QUICK_STATUS.md** (earlier)
   - One-page quick reference

---

**Respectfully submitted,**
Claude Code (AI Agent)
October 13, 2025 (End of Session)

**Attachments:**
- Code: `GR/Riemann.lean` lines 125-129, 6000-6187
- Reports: All diagnostic files listed above
- Build: ✅ Clean
- Sorry count: 11 (baseline, no regression)

**Ready for:** Your decision on Path A, B, or C - and guidance on how to proceed.

---

## APPENDIX: Code Comparison

### Your Sum-Level Approach (Oct 13, 2025)

```lean
-- Refold helpers (per-k for use under sum)
have refold_r_right (k : Idx) := [uses compat_refold_r_kb]
have refold_θ_right (k : Idx) := [uses compat_refold_θ_kb]

-- Weighted lift
have h_weighted := congrArg (fun F => sumIdx F) h_fold_fiber

-- Expand compat under outer sum
simp_rw [dCoord_g_via_compat_ext M r θ h_ext] at h_weighted

-- Apply refolds under outer sum
simp_rw [Hr, Hθ] at h_weighted

-- Recognize RiemannUp
simp [RiemannUp, sumIdx]  -- ❌ TIMEOUT
```

### OLD Working Approach (Left Regroup)

```lean
-- Fiberwise proof
have h_kk : ∀ k, [LHS k] = RiemannUp * g := by
  intro k
  -- Pointwise compat expansion
  rw [dCoord_g_via_compat M r θ h_ext]
  -- Manual Fubini swaps
  rw [H₁, H₂]  -- Custom helper lemmas
  -- Targeted refold
  rw [kk_refold]
  -- Pure algebra
  ring  -- ✅ WORKS

-- Lift to sum level
have := congrArg (fun F => sumIdx F) (funext h_kk)
simpa using this
```

**Key difference:** OLD approach uses **custom helper lemmas** (H₁, H₂) and **targeted rw** instead of generic simp with AC lemmas.
