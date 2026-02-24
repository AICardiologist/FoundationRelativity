# Summary for JP - Left Regrouping Blocker
## Date: October 18, 2025 (Evening)

---

## TL;DR

Attempted to implement `regroup_left_sum_to_RiemannUp` following your guidance, but hit a fundamental pattern matching issue:

**After compatibility expansion + distribution, the goal is ONE big `sumIdx` containing 6 terms lumped together. H₁/H₂/Identify lemmas can't match their patterns because they expect separate top-level sums.**

---

## What's Working ✅

- Compatibility expansion: `compat_r_a_e` and `compat_θ_a_e` applied successfully
- Distribution: All products distributed over sums
- H₁ and H₂: Both compile and are mathematically correct (lines 4070-4093)
- Identify lemmas: Both exist and are available (lines 1770-1820)
- Build: Clean (0 errors, sorry at line 4114)

---

## The Blocker

After `simp_rw [compat_r_a_e, compat_θ_a_e]` and `simp only [mul_add, add_mul, ...]`, the goal has shape:

```lean
sumIdx (fun k =>
    ∂_r Γ_{kθb} * g_{ak} +                                -- term 1
    -(∂_θ Γ_{krb} * g_{ak}) +                             -- term 2
    ((Γ_{kθb} * Σ_{k₁} Γ_{k₁ra} * g_{k₁k}) +             -- term 3 (diagonal - needs Identify_r)
     Γ_{kθb} * Σ_{k₁} Γ_{k₁rk} * g_{ak₁}) +              -- term 4 (off-diagonal - needs H₁)
    -((Γ_{krb} * Σ_{k₁} Γ_{k₁θa} * g_{k₁k}) +            -- term 5 (diagonal - needs Identify_θ)
      Γ_{krb} * Σ_{k₁} Γ_{k₁θk} * g_{ak₁}))              -- term 6 (off-diagonal - needs H₂)
  = g_{aa} * RiemannUp ...
```

**Problem**: H₁ expects to match `sumIdx (fun k => Γ_{kθb} * sumIdx ...)` at the TOP LEVEL, but term 4 is buried inside this bigger sum with 5 other terms.

Same issue for H₂, Identify_r, and Identify_θ.

---

## What I Tried

1. **Direct application**: `rw [H₁, H₂]` → "Did not find an occurrence of the pattern"

2. **Identify first**: `rw [I₁, I₂]; rw [H₁, H₂]` → Same failure

3. **Manual split**: Defined f1...f6 functions and tried to prove `sumIdx (fun k => ...) = Σf1 - Σf2 + Σf3 + ...` → proof won't close with `ring`

4. **Conv mode targeting**: Too unwieldy, leads to massive proof states

**See `LEFT_REGROUPING_STATUS_OCT18_V2.md` for full details of all attempts.**

---

## The Question

**How do I extract/separate the 6 terms so H₁/H₂/Identify can match their patterns?**

Possible approaches:
- **A**: Use `sumIdx_add_distrib` repeatedly to split into `Σf1 - Σf2 + Σf3 + Σf4 - Σf5 - Σf6`
  - **Blocker**: Can't close the proof that shows the split is valid

- **B**: Rewrite H₁/H₂ to work pointwise via `sumIdx_congr`
  - **Question**: Would this even help, or just defer the problem?

- **C**: Use a different compatibility expansion strategy to avoid lumping terms
  - **Question**: Is there a selective way to apply compat lemmas?

- **D**: Something else I'm not seeing?

---

## Specific Help Needed

1. **Which approach is correct?**

2. **If approach A**: How do I close the `split_goal` proof? What's the exact tactic sequence?

3. **If approach B**: Should I create pointwise versions of H₁/H₂/Identify?

4. **Concrete code**: Can you provide the working tactical sequence from after distribution to first rewrite application?

---

## Current Code State

```lean
lemma regroup_left_sum_to_RiemannUp ... := by
  classical
  have compat_r_a_e : ... := by exact dCoord_g_via_compat_ext ... ✅
  have compat_θ_a_e : ... := by exact dCoord_g_via_compat_ext ... ✅
  simp_rw [compat_r_a_e, compat_θ_a_e]  ✅
  simp only [mul_add, add_mul, sub_eq_add_neg, ...]  ✅

  have H₁ : ... := by ... ✅
  have H₂ : ... := by ... ✅

  /- ③ Put everything together: ... -/
  -- ❌ BLOCKER: Goal has 6 terms lumped in ONE sumIdx
  -- H₁/H₂/Identify can't match their patterns
  sorry  -- line 4114
```

**File**: `Riemann.lean`, lines 4036-4114
**Build**: Clean ✅
**Detailed analysis**: `LEFT_REGROUPING_STATUS_OCT18_V2.md`

---

## What I'm Blocked On

I understand the MATHEMATICS:
- Terms 3 and 5 need Identify lemmas to convert diagonal Γ·Γ → Γ₁·Γ
- Terms 4 and 6 need H₁/H₂ to contract off-diagonal Γ·Γ
- Then collect with mixed-left collector
- Then pointwise kernel recognition

But I'm stuck on the TACTICS:
- How to extract terms 3, 4, 5, 6 from the nested sum so the lemmas can match
- What's the exact rewrite sequence after distribution

---

**Next Steps**: Awaiting your tactical guidance on how to proceed from the distributed goal.

**Prepared by**: Claude Code
**Date**: October 18, 2025 (Evening)
**Status**: Blocked at step ③ of left regrouping implementation
