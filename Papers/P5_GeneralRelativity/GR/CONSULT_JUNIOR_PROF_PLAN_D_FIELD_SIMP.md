# Consult Memo: Junior Professor - Plan D field_simp Investigation

**To:** Junior Professor (Lean 4 Tactics Expert)
**From:** Claude Code (Implementation Team)
**Date:** October 6, 2025
**Re:** Plan D - Can field_simp handle complex denominators directly?
**Priority:** HIGH
**Context:** Following Senior Professor's Plan D after Plans A-C failed

---

## Quick Summary of Request

After exhaustive attempts to apply the rmf/rinv normalization pattern (including Senior Professor's Plans A and C), all approaches have failed with "simp made no progress". The Senior Professor's Plan D recommends questioning the original premise: **Can `field_simp` be made to handle complex denominators like `(r - M*2)⁻¹` directly, avoiding the rmf/rinv complexity entirely?**

**Specific Question:** Given that we can prove `r - M*2 ≠ 0`, is there a way to configure or use `field_simp` (or an alternative tactic) to clear denominators like `(r - M*2)⁻¹` without first rewriting them to simpler forms?

---

## Context: The Full Story

### Where We Started (Initial Blocking Issue)

**Date:** October 5, 2025 (morning)
**Problem:** Implementing Schwarzschild Riemann component lemmas following your recommended structure:

```lean
lemma Riemann_tθtθ_eq (M r θ : ℝ) (hM : 0 < M) (hr_ex : 2 * M < r) :
    Riemann M r θ Idx.t Idx.θ Idx.t Idx.θ = M * f M r / r := by
  classical
  have hr_nz : r ≠ 0 := r_ne_zero_of_exterior M r hM hr_ex
  have hf_nz : f M r ≠ 0 := ne_of_gt (f_pos_of_hr M r hM hr_ex)

  rw [Riemann_contract_first M r θ Idx.t Idx.θ Idx.t Idx.θ]
  unfold RiemannUp
  simp only [dCoord_t, dCoord_θ, sumIdx_expand, Γtot, g]
  simp only [deriv_const', Γ_t_tr, Γ_r_θθ]

  field_simp [hr_nz]  -- ❌ BLOCKED HERE
  ring
```

**The Issue:** After expanding Christoffel symbols, `field_simp [hr_nz]` **did not clear denominators**. The goal contained reciprocal terms like `(r - M*2)⁻¹` which remained after `field_simp`, causing `ring` to fail.

**Example goal (after field_simp failed):**
```lean
⊢ -(r * M^2 * (r - M*2)⁻¹ * 4) + r^2 * M * (r - M*2)⁻¹ + M^3 * (r - M*2)⁻¹ * 4
  = r * M - M^2 * 2
```

**My Initial Attempted Fix (Failed):**
```lean
have hsub_nz : r - M * 2 ≠ 0 := by linarith [hr_ex]
field_simp [hr_nz, hsub_nz]  -- Still didn't clear denominators
ring
```

**Result:** ❌ Same failure - `field_simp` left `(r - M*2)⁻¹` terms in the goal.

**Documented in:** `PHASE2_FIELD_SIMP_NOT_CLEARING_DENOMINATORS.md`

---

### Expert Guidance: The rmf/rinv Normalization Technique

**Date:** October 5, 2025 (afternoon)
**Source:** User provided expert tactical guidance

**Expert's Analysis:**

> "`field_simp` only clears denominators it can see as atomic 'inv/÷ by X' factors. The issue is that `(r - M*2)⁻¹` is a complex expression that field_simp doesn't recognize as an atomic denominator.
>
> **The fix:** Rewrite all occurrences of `r - 2*M` to `r * f M r` BEFORE calling field_simp. Then field_simp only needs to clear base denominators `r` and `f M r`, which it knows how to handle."

**Recommended rmf/rinv Pattern:**
```lean
-- Set up normalization identities
have rmf : r - 2 * M = r * f M r := by
  simpa [mul_comm] using r_mul_f M r hr_nz
have rinv : (r - 2 * M)⁻¹ = (r * f M r)⁻¹ := by
  simpa [rmf]

-- Rewrite patterns in goal
simp_rw [rmf, rinv]

-- NOW field_simp can clear atomic denominators
field_simp [hr_nz, hf_nz]  -- Do NOT pass hsub_nz
ring
```

**Theoretical Soundness:** This technique is mathematically correct. If `(r - 2*M)⁻¹` is rewritten to `(r * f M r)⁻¹`, then field_simp sees two atomic denominators (`r⁻¹` and `(f M r)⁻¹`) which it can clear.

---

### Multiple Implementation Attempts (All Failed)

**Attempts:** 4 different approaches over October 5-6, 2025

#### Attempt 1: Direct rmf/rinv after simp expansion
```lean
simp only [deriv_const', Γ_t_tr, Γ_r_θθ]

have rmf : r - 2 * M = r * f M r := (r_mul_f M r hr_nz).symm
have rinv : (r - 2 * M)⁻¹ = (r * f M r)⁻¹ := by rw [rmf]
simp_rw [rmf, rinv]  -- ❌ ERROR: `simp` made no progress
```

#### Attempt 2: Handle commutativity (both 2*M and M*2)
```lean
have rmf : r - 2 * M = r * f M r := (r_mul_f M r hr_nz).symm
have rmf' : r - M * 2 = r * f M r := by rw [mul_comm M 2]; exact rmf
simp_rw [rmf, rmf']  -- ❌ ERROR: `simp` made no progress
```

#### Attempt 3: Include inverse patterns explicitly
```lean
have rmf : r - 2 * M = r * f M r := (r_mul_f M r hr_nz).symm
have rinv : (r - 2 * M)⁻¹ = (r * f M r)⁻¹ := by rw [rmf]
have rmf' : r - M * 2 = r * f M r := by rw [mul_comm M 2]; exact rmf
have rinv' : (r - M * 2)⁻¹ = (r * f M r)⁻¹ := by rw [rmf']
simp_rw [rmf, rmf', rinv, rinv']  -- ❌ ERROR: `simp` made no progress
```

#### Attempt 4: Rewrite before Γ expansion
```lean
-- Try normalizing BEFORE expanding Γ symbols
simp_rw [rmf, rinv]  -- ❌ ERROR: `simp` made no progress
simp only [deriv_const', Γ_t_tr, Γ_r_θθ]
```

**Conclusion from Attempts 1-4:** The pattern `r - 2*M` (in any form) does not exist in the goal for `simp_rw` to match, despite Γ_r_θθ being defined as `-(r - 2*M)`.

**Documented in:** `PHASE2_RMF_RINV_PATTERN_MISMATCH_REPORT.md`

---

### Senior Professor's Strategic Guidance (October 6, 2025)

**Source:** Response to consult memo `CONSULT_SENIOR_PROF_COMPONENT_LEMMAS_BLOCKED.md`

**Strategic Decision:** Continue with component lemma approach (mathematically sound, tactical issue only)

**Root Cause Analysis (Senior Professor):**

1. **Premature Normalization:** Using `simp only` to expand Γ symbols causes Lean to immediately apply normalization rules, destroying the literal pattern `r - 2*M` before `simp_rw` can act.

2. **Incomplete Rewrite Set:** Previous attempts didn't provide all necessary pattern variants simultaneously.

---

### Plan A: Gentle Unfolding + Complete Rewrite Set (Senior Professor)

**Recommendation:** Use `unfold` instead of `simp only` for Γ symbols (preserves literal patterns) and provide the COMPLETE rmf/rinv lemma set.

**Implementation (October 6, 2025):**

```lean
-- Step 1: Structural Expansion
rw [Riemann_contract_first M r θ Idx.t Idx.θ Idx.t Idx.θ]
unfold RiemannUp
simp only [dCoord_t, dCoord_θ, sumIdx_expand, Γtot, g]

-- Step 2: Handle derivatives
simp only [deriv_const']

-- Step 3: GENTLE UNFOLDING (critical change)
unfold Γ_t_tr Γ_r_θθ  -- ← Use 'unfold' instead of 'simp only'

-- Step 4: Complete normalization set
have rmf : r - 2 * M = r * f M r := (r_mul_f M r hr_nz).symm
have rinv : (r - 2 * M)⁻¹ = (r * f M r)⁻¹ := by rw [rmf]
have rmf' : r - M * 2 = r * f M r := by rw [mul_comm M 2]; exact rmf
have rinv' : (r - M * 2)⁻¹ = (r * f M r)⁻¹ := by rw [rmf']

simp_rw [rmf, rmf', rinv, rinv']

-- Step 5: Final algebra
field_simp [hr_nz, hf_nz, pow_two, sq]
ring
```

**Test Result (October 6, 2025):**
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:4971:16: `simp` made no progress
```

❌ **Plan A FAILED** - Even with `unfold` instead of `simp only`, the pattern still isn't found.

---

### Plan C: Add Negated Variants (Senior Professor's Contingency)

**Rationale:** The `-(r - 2*M)` from Γ_r_θθ might be normalized to `2*M - r`, requiring additional lemmas.

**Implementation (October 6, 2025):**

```lean
-- Complete set including negated forms
have rmf : r - 2 * M = r * f M r := (r_mul_f M r hr_nz).symm
have rinv : (r - 2 * M)⁻¹ = (r * f M r)⁻¹ := by rw [rmf]
have rmf' : r - M * 2 = r * f M r := by rw [mul_comm M 2]; exact rmf
have rinv' : (r - M * 2)⁻¹ = (r * f M r)⁻¹ := by rw [rmf']
have rmf_neg : 2 * M - r = -(r * f M r) := by rw [←neg_sub, rmf]
have rmf_neg' : M * 2 - r = -(r * f M r) := by rw [mul_comm M 2]; exact rmf_neg

simp_rw [rmf, rmf', rinv, rinv', rmf_neg, rmf_neg']
```

**Test Result (October 6, 2025):**
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:4974:16: `simp` made no progress
```

❌ **Plan C FAILED** - Even with negated variants, the pattern still isn't found.

---

## Current Situation Analysis

### What We Know

1. **Γ Definitions:** The Christoffel symbols ARE defined with the literal pattern:
   ```lean
   noncomputable def Γ_r_θθ (M r : ℝ) : ℝ := -(r - 2*M)  -- Pattern exists here
   ```

2. **After Expansion:** Neither `simp only` nor `unfold` exposes this pattern in a form that `simp_rw` can match.

3. **All Pattern Variants Tried:**
   - `r - 2*M` and `r - M*2` (direct and commutative)
   - `(r - 2*M)⁻¹` and `(r - M*2)⁻¹` (inverses)
   - `2*M - r` and `M*2 - r` (negated forms)
   - All simultaneously provided to `simp_rw`
   - **Result:** "simp made no progress" in every case

4. **Systematic Failure:** The pattern matching failure is not due to missing variants or wrong ordering - the patterns simply don't exist in the goal in ANY recognizable form after Γ expansion.

---

## Senior Professor's Plan D Recommendation

**From Senior Professor's memo, Section "Plan D: Revisit the field_simp Premise":**

> "In parallel, it is worth questioning the premise that necessitated rmf/rinv. The report PHASE2_FIELD_SIMP_NOT_CLEARING_DENOMINATORS.md showed field_simp failing to clear `(r - M*2)⁻¹` even with the required non-zero hypothesis.
>
> **Action:** Consult the Junior Professor (Lean Expert) specifically about this behavior. If field_simp can be made to handle complex denominators directly, the rmf/rinv complexity can be avoided entirely."

---

## Questions for Junior Professor

### Q1: Can field_simp Handle Complex Denominators?

**Background:** Our initial approach was:
```lean
have hsub_nz : r - M * 2 ≠ 0 := by linarith [hr_ex]
field_simp [hr_nz, hsub_nz]
ring
```

This failed - `field_simp` did not clear the `(r - M*2)⁻¹` denominators even with `hsub_nz` explicitly provided.

**Questions:**
1. Is there a configuration or option to make `field_simp` handle complex denominators like `(r - M*2)⁻¹`?
2. Does `field_simp` require denominators to be in a specific canonical form?
3. Is there a way to "teach" `field_simp` about the nonzero constraint for composite expressions?

---

### Q2: Alternative Tactics for Clearing Complex Denominators?

If `field_simp` fundamentally cannot handle `(r - M*2)⁻¹`, is there an alternative tactic that can?

**Options to consider:**
1. **field_simp variants:** Is there `field_simp!` or other aggressive versions?
2. **Specialized tactics:** Are there tactics specifically for clearing denominators in field expressions?
3. **Normalization first:** Should we use `ring_nf` to normalize the goal to canonical form before attempting to clear denominators?
4. **Manual clearing:** Can we use `rw` with specific field lemmas to manually multiply through by denominators?

---

### Q3: Why Did rmf/rinv Pattern Matching Fail?

Even though this is a secondary question (since Plan D focuses on avoiding rmf/rinv), understanding why the pattern matching failed might provide insights.

**The Mystery:** After `unfold Γ_r_θθ`, which should substitute `-(r - 2*M)` directly into the goal, `simp_rw` still cannot find the pattern.

**Possible explanations:**
1. Does `unfold` trigger some normalization despite being "gentler" than `simp`?
2. Are there earlier simplification steps (from expanding RiemannUp, Γtot, etc.) that pre-normalize the expressions?
3. Is the pattern buried inside a more complex structure that `simp_rw` doesn't traverse?

**If you have diagnostic suggestions:** The Senior Professor recommended using the IDE (VS Code Lean extension) to inspect the exact goal state. However, I'm working in a non-interactive environment. Are there tactics or options to print the full goal state to build logs?

---

### Q4: Working Example Request

**Most Helpful Response:** A complete, compilable proof of just the R_tθtθ component lemma showing the exact tactical sequence that works.

Even if it uses tactics or approaches I haven't tried, seeing a working example would immediately clarify the correct path forward and serve as a template for the other 5 component lemmas.

**Current non-working code (GR/Riemann.lean:4944-4978):**
```lean
/-- Component: R_tθtθ = M·f(r)/r -/
lemma Riemann_tθtθ_eq (M r θ : ℝ) (hM : 0 < M) (hr_ex : 2 * M < r) :
    Riemann M r θ Idx.t Idx.θ Idx.t Idx.θ = M * f M r / r := by
  classical
  have hr_nz : r ≠ 0 := r_ne_zero_of_exterior M r hM hr_ex
  have hf_nz : f M r ≠ 0 := ne_of_gt (f_pos_of_hr M r hM hr_ex)

  -- Step 1: Structural Expansion
  rw [Riemann_contract_first M r θ Idx.t Idx.θ Idx.t Idx.θ]
  unfold RiemannUp
  simp only [dCoord_t, dCoord_θ, sumIdx_expand, Γtot, g]

  -- Step 2: Handle derivatives
  simp only [deriv_const']

  -- Step 3: GENTLE UNFOLDING
  unfold Γ_t_tr Γ_r_θθ

  -- Step 4: Normalization (complete set including negated forms)
  have rmf : r - 2 * M = r * f M r := (r_mul_f M r hr_nz).symm
  have rinv : (r - 2 * M)⁻¹ = (r * f M r)⁻¹ := by rw [rmf]
  have rmf' : r - M * 2 = r * f M r := by rw [mul_comm M 2]; exact rmf
  have rinv' : (r - M * 2)⁻¹ = (r * f M r)⁻¹ := by rw [rmf']
  have rmf_neg : 2 * M - r = -(r * f M r) := by rw [←neg_sub, rmf]
  have rmf_neg' : M * 2 - r = -(r * f M r) := by rw [mul_comm M 2]; exact rmf_neg

  simp_rw [rmf, rmf', rinv, rinv', rmf_neg, rmf_neg']  -- ❌ FAILS HERE

  -- Step 5: Final Algebra
  field_simp [hr_nz, hf_nz, pow_two, sq]
  ring
```

**What would help:**
- Either a fix to make this approach work
- OR a completely different tactical sequence that achieves the same goal

---

## Available Context and Resources

### Helper Lemmas (Available, Proven)

**Location:** GR/Riemann.lean:4899-4905

```lean
lemma r_mul_f (M r : ℝ) (hr_nz : r ≠ 0) : r * f M r = r - 2 * M := by
  unfold f
  field_simp [hr_nz]
  ring

lemma one_minus_f (M r : ℝ) : 1 - f M r = 2 * M / r := by
  unfold f
  ring

lemma f_derivative (M r : ℝ) (hr_nz : r ≠ 0) :
    deriv (fun s => f M s) r = 2 * M / r ^ 2 := by
  unfold f
  simp [deriv_sub_const, deriv_const', deriv_div_const]
  rw [deriv_mul_const, deriv_inv' hr_nz]
  field_simp [hr_nz]
  ring
```

These compile successfully and can be used in the component lemma proofs.

---

### Christoffel Symbol Definitions

**Location:** GR/Schwarzschild.lean:1112-1116

```lean
noncomputable def Γ_t_tr (M r : ℝ) : ℝ := M / (r^2 * f M r)
noncomputable def Γ_r_θθ (M r : ℝ) : ℝ := -(r - 2*M)  -- ← Contains the pattern
```

---

### Related Documentation

1. **`PHASE2_FIELD_SIMP_NOT_CLEARING_DENOMINATORS.md`** - Original field_simp blocking issue
2. **`PHASE2_RMF_RINV_PATTERN_MISMATCH_REPORT.md`** - Detailed analysis of pattern matching failures
3. **`CONSULT_SENIOR_PROF_COMPONENT_LEMMAS_BLOCKED.md`** - Strategic consult that led to Plans A-D
4. **`JUNIOR_PROF_REQUEST_COMPONENT_LEMMAS.md`** - Your original component lemma recommendation

---

## Summary of Request

**Primary Goal:** Determine if `field_simp` can be made to work directly with complex denominators like `(r - M*2)⁻¹`, avoiding the rmf/rinv pattern matching complexity entirely.

**What We've Tried:**
1. ❌ Initial `field_simp [hr_nz, hsub_nz]` - denominators not cleared
2. ❌ rmf/rinv pattern with `simp only` expansion - pattern not found
3. ❌ Senior Prof Plan A: Gentle unfolding + complete set - pattern not found
4. ❌ Senior Prof Plan C: Add negated variants - pattern not found

**What We Need:**
- Either a way to make `field_simp` handle complex denominators directly
- OR an alternative tactic/approach that can clear these denominators
- OR a complete working example showing the correct tactical sequence

**Urgency:** HIGH - All 6 component lemmas (and thus 4 diagonal Ricci cases) are blocked pending resolution.

**Next Steps:**
- If field_simp can be enhanced: Apply that solution
- If not: Senior Professor suggested considering infrastructure changes or alternative proof strategies
- Your expertise on Lean 4 tactics is critical for determining the best path forward

---

Thank you for your time and tactical expertise. Looking forward to your guidance on whether Plan D (direct field_simp approach) is viable, or if we need to pivot to a fundamentally different strategy.

**— Claude Code**

---

**Attachments:**
- Senior Professor Memo Response (in previous communications)
- Technical Report: `GR/PHASE2_RMF_RINV_PATTERN_MISMATCH_REPORT.md`
- Previous Reports: Multiple .md files documenting the journey
- Current Code: `GR/Riemann.lean:4944-4978`

**Current Build Status:** ~15 errors (baseline 9 + 6 from component lemma work)
**Recommendation:** Do not commit current state - awaiting tactical guidance
