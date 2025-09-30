# Revised Consultation: Implementation Issues with Recommended Patterns

**Date:** September 30, 2025
**Re:** Challenges implementing the Robust Exterior Proof Pattern and tactical guidance
**To:** Senior Professor
**From:** Implementation Team
**Current Status:** 31 errors (increased from 23), budget compliant

## Executive Summary

We attempted to implement your strategic guidance from September 30, but encountered significant issues that increased our error count from 23 to 31. After careful analysis, we've identified several problems with the recommended patterns that need clarification.

## What We Tried to Implement

### 1. Phase A: nabla_g_zero with Case Exhaustion
**Your recommendation:**
```lean
theorem nabla_g_zero (M r θ : ℝ) (c a b : Idx) : nabla_g M r θ c a b = 0 := by
  cases c <;> cases a <;> cases b
  all_goals { simp [nabla_g, dCoord_g_via_compat] }
```

**What happened:**
- This approach caused timeouts (as noted in the original comment)
- The proof requires `dCoord_g_via_compat` to be proven first, but that lemma depends on `nabla_g_zero`
- This creates a circular dependency

**Current state:** Left as `sorry` to avoid timeout

### 2. Phase B: Metric Compatibility Lemmas
**Issue encountered:**
- The lemmas at lines 257-330 already have the correct structure
- They use `exact h` as terminal tactic (not `simp`)
- The errors persist because they depend on the unproven `nabla_g_zero`

### 3. Phase C: Exterior Domain Proofs (lines 338-434)
**Your Robust Exterior Proof Pattern (REPP):**
The pattern assumes we can extract non-zero hypotheses and apply field_simp, but we're getting "unsolved goals" errors even with the pattern applied.

## Current Error Breakdown (31 total)

### Category 1: Exterior Domain Proofs (9 errors)
- Lines 345-430: All "unsolved goals" in ExteriorDomainProofs section
- These should be mechanical according to your guidance

### Category 2: Infrastructure Dependencies (13 errors)
- Lines 449-985: Mix of "Type mismatch", "simp failed", and "unsolved goals"
- Many cascade from the `nabla_g_zero` sorry

### Category 3: Duplicate Declaration (1 error)
- Line 573: `sumIdx_mul_left` already declared (from our patches)

### Category 4: Phase 3 Identity (1 error)
- Line 938: "simp made no progress" in alternation_phase3_identity_tt

### Other Issues (7 errors)
- Various simp failures in Stage-1 lemmas

## Only 1 Sorry in the File

```lean
line 239: sorry -- TODO: cases c <;> cases a <;> cases b <;> simp [nabla_g, dCoord, sumIdx, g, Γtot] (timeout)
```

## Key Problems We Need Help With

### Problem 1: Circular Dependency
`nabla_g_zero` needs `dCoord_g_via_compat`, but `dCoord_g_via_compat` uses `nabla_g_zero`. How should we break this cycle?

### Problem 2: REPP Not Working as Expected
Even when we apply your pattern exactly in the ExteriorDomainProofs section, we still get unsolved goals. Example at line 345:
```lean
lemma compat_r_tt_ext (h_ext : Exterior M r θ) :
  dCoord Idx.r (fun r θ => g M Idx.t Idx.t r θ) r θ
    = 2 * Γtot M r θ Idx.t Idx.r Idx.t * g M Idx.t Idx.t r θ := by
  classical
  have hr : r ≠ 0 := r_pos_of_Exterior h_ext |>.ne'
  have hf : f M r ≠ 0 := f_pos_of_Exterior h_ext |>.ne'
  simp only [dCoord_r, g_tt, Γtot_t_tr, Γ_t_tr]
  -- ... pattern continues but still fails
```

### Problem 3: Incorrect Tactical Advice?
Your memo suggested using `linarith` to replace `simpa [add_comm] using h.symm`, but:
- `simpa` was actually working in most places
- The issue at line 252 was that `nabla_g_zero` returns `sorry`
- We had to use `linarith` there as a workaround

## What's Actually Working

1. **Phase 3 infrastructure** (from previous patches) is complete
2. **Budget compliance** maintained (31 < 50)
3. **Baseline check** passes
4. Most of the codebase structure is sound

## Specific Questions

1. **How do we resolve the circular dependency** between `nabla_g_zero` and `dCoord_g_via_compat`?

2. **Is there a different proof strategy for `nabla_g_zero`** that avoids the 64-case exhaustion?

3. **Why might REPP fail** even when we follow the pattern exactly?

4. **Should we try a different approach entirely**, perhaps:
   - Axiomatizing some base lemmas temporarily?
   - Using a different proof architecture?
   - Focusing on a subset of the lemmas first?

## Request

We need either:
1. **Corrected tactical guidance** that addresses the circular dependencies
2. **A different architectural approach** that avoids these issues
3. **Confirmation that we should leave certain lemmas as axioms** for now

The increase from 23 to 31 errors suggests there may be a fundamental issue with the recommended approach, or we're misunderstanding the implementation details.

## Attachment
Current Riemann.lean with all attempted fixes is available for review.