# Left Regrouping Implementation - Tactical Blocker
## Date: October 18, 2025 (Evening Session)
## Status: Pattern Matching Issues

---

## Summary

Attempted to implement `regroup_left_sum_to_RiemannUp` following JP's guidance, but hit fundamental pattern matching issues with how H₁/H₂ and Identify lemmas interact with the nested sum structure after compatibility expansion.

---

## What Works ✅

1. **Compatibility expansion**: Successfully applied `compat_r_a_e` and `compat_θ_a_e`
2. **Distribution**: Successfully distributed products over sums
3. **H₁ and H₂ definitions**: Both lemmas compile and are mathematically correct
4. **Identify lemmas exist**: `Riemann_via_Γ₁_Identify_r` and `_θ` are available

---

## The Core Problem

After `simp_rw [compat_r_a_e, compat_θ_a_e]` and distribution, the goal has shape:

```lean
sumIdx (fun k =>
    dCoord Idx.r (Γ_{kθb}) * g_{ak} +                              -- term 1 (∂Γ)
    -(dCoord Idx.θ (Γ_{krb}) * g_{ak}) +                            -- term 2 (∂Γ)
    ((Γ_{kθb} * Σ_{k₁} Γ_{k₁ra} * g_{k₁k}) +                       -- term 3 (diagonal Γ·Γ)
     Γ_{kθb} * Σ_{k₁} Γ_{k₁rk} * g_{ak₁}) +                        -- term 4 (off-diagonal Γ·Γ)
    -((Γ_{krb} * Σ_{k₁} Γ_{k₁θa} * g_{k₁k}) +                      -- term 5 (diagonal Γ·Γ)
      Γ_{krb} * Σ_{k₁} Γ_{k₁θk} * g_{ak₁}))                        -- term 6 (off-diagonal Γ·Γ)
  = g_{aa} * RiemannUp ...
```

---

## Pattern Matching Issues

###  H₁ and H₂

**H₁ expects**:
```lean
sumIdx (fun k => Γ_{kθb} * sumIdx (fun lam => Γ_{lam,r,k} * g_{a,lam}))
```

**But the goal has BOTH**:
```lean
sumIdx (fun k => ... +
    ((Γ_{kθb} * Σ_{k₁} Γ_{k₁ra} * g_{k₁k}) +        -- diagonal (NOT what H₁ handles)
     Γ_{kθb} * Σ_{k₁} Γ_{k₁rk} * g_{ak₁}) + ...)    -- off-diagonal (IS what H₁ handles)
```

**Problem**: H₁ cannot match its pattern because:
1. The off-diagonal term (term 4) is lumped together with 5 other terms inside ONE outer `sumIdx`
2. Even if we could extract term 4, it has wrong index structure: `Γ_{k₁rk}` vs `Γ_{lam,r,k}`

**Same issue for H₂** with terms 5 and 6.

### Identify Lemmas

**`Riemann_via_Γ₁_Identify_r` expects**:
```lean
sumIdx (fun ρ => sumIdx (fun σ => Γ_{σ,r,a} * g_{σρ}) * Γ_{ρ,θ,b})
```

**But term 3 in the goal is**:
```lean
Γ_{kθb} * sumIdx (fun k₁ => Γ_{k₁ra} * g_{k₁k})  -- inside the outer sumIdx over k
```

**Problem**: The Identify lemma expects the pattern to be at the TOP LEVEL as a separate sumIdx, not nested inside another sumIdx with other terms.

---

## Approaches Tried

### Attempt 1: Direct Application of H₁/H₂
```lean
rw [H₁, H₂]
```
**Result**: `Did not find an occurrence of the pattern` - H₁/H₂ can't match because their patterns are buried inside a bigger sum

### Attempt 2: Apply Identify First, Then H₁/H₂
```lean
have I₁ := (Riemann_via_Γ₁_Identify_r M r θ (β := a) (a := b))
have I₂ := (Riemann_via_Γ₁_Identify_θ M r θ (β := a) (a := b))
rw [H₁, H₂]  -- Still fails
rw [← I₁, ← I₂]
```
**Result**: Same pattern matching failure

### Attempt 3: Split Sum Into Components
```lean
let f1 : Idx → ℝ := fun k => dCoord Idx.r (Γ_{kθb}) * g_{ak}
let f2 : Idx → ℝ := fun k => dCoord Idx.θ (Γ_{krb}) * g_{ak}
let f3 : Idx → ℝ := fun k => Γ_{kθb} * Σ_{k₁} Γ_{k₁ra} * g_{k₁k}   -- diagonal
let f4 : Idx → ℝ := fun k => Γ_{kθb} * Σ_{k₁} Γ_{k₁rk} * g_{ak₁}   -- off-diagonal
let f5 : Idx → ℝ := fun k => Γ_{krb} * Σ_{k₁} Γ_{k₁θa} * g_{k₁k}   -- diagonal
let f6 : Idx → ℝ := fun k => Γ_{krb} * Σ_{k₁} Γ_{k₁θk} * g_{ak₁}   -- off-diagonal

have split_goal : sumIdx (fun k => f1 k - f2 k + ((f3 k + f4 k) + -(f5 k + f6 k)))
                = sumIdx f1 - sumIdx f2 + ((sumIdx f3 + sumIdx f4) + -(sumIdx f5 + sumIdx f6))
```
**Result**: The `split_goal` proof itself gets stuck because `ring` can't normalize the negation distribution properly

### Attempt 4: Use `conv` Mode for Targeted Rewriting
```lean
conv_lhs =>
  arg 1
  ext k
  rw [show ... = ... by rfl]  -- Try to expose structure
```
**Result**: Too unwieldy, leads to massive proof state

---

## Key Insight

The fundamental tactical challenge is:

**After compatibility expansion, we have ONE big `sumIdx` with 6 terms mixed together.**

But our rewrite lemmas (H₁, H₂, Identify_r, Identify_θ) expect:
- **Separate top-level sums** for each pattern
- **Specific index structures** that may not match what the goal has

**Question**: How do we bridge this gap?

---

## Possible Solutions (Need JP's Guidance)

### Option A: Manual Extraction + Separate Rewrites

1. Use `sumIdx_add_distrib` (in reverse) repeatedly to split the goal into 6 separate sums:
   ```lean
   Σf1 - Σf2 + Σf3 + Σf4 - Σf5 - Σf6 = ...
   ```

2. Apply H₁ to `Σf4` (off-diagonal θ-branch)
3. Apply H₂ to `Σf6` (off-diagonal r-branch)
4. Apply Identify_r to `Σf3` (diagonal θ-branch)
5. Apply Identify_θ to `Σf5` (diagonal r-branch)
6. Collect with mixed-left

**Blocker**: The `split_goal` proof won't close with just `simp` and `ring`

### Option B: Index Relabeling

Maybe the index mismatch (e.g., `k₁` vs `lam`) is the real issue?

Try explicit variable renaming:
```lean
conv_lhs =>
  arg 1
  ext k
  arg 2; arg 2  -- Navigate to the Γ·Γ term
  ext k_1
  rw [show k_1 = lam by sorry]  -- Relabel index
```

**Question**: Is this even possible in Lean? Can we rename bound variables mid-proof?

### Option C: Rewrite H₁/H₂ to Handle Embedded Patterns

Modify H₁/H₂ to accept the nested pattern directly:
```lean
have H₁_embedded :
  ∀ k, Γ_{kθb} * sumIdx (fun k_1 => Γ_{k_1rk} * g_{ak_1})
     = g_{ak} * sumIdx (fun lam => Γ_{k r lam} * Γ_{lam θ b})
```

Then apply `sumIdx_congr` and use `H₁_embedded` pointwise?

**Question**: Would this work, or does it just defer the problem?

### Option D: Different Compatibility Expansion Strategy

Maybe the issue is HOW we expand compatibility?

Instead of:
```lean
simp_rw [compat_r_a_e, compat_θ_a_e]
simp only [mul_add, add_mul, ...]
```

Could we expand more selectively to avoid lumping all 6 terms together?

**Question**: Is there a targeted way to apply compatibility that preserves structure?

---

## What I Need From JP

1. **Which option (A/B/C/D/other) is the right approach?**

2. **For Option A (manual extraction)**:
   - How do I close the `split_goal` proof?
   - What's the exact sequence of `sumIdx_add_distrib` applications?

3. **For the index relabeling issue**:
   - Is `k_1` vs `lam` a real blocker, or should pattern matching handle this?
   - Do I need to explicitly rename bound variables?

4. **Concrete code**:
   - Can you provide a working proof of `split_goal`?
   - Or an alternative tactical sequence that avoids needing `split_goal`?

---

## Current State

```lean
lemma regroup_left_sum_to_RiemannUp ... := by
  classical
  have compat_r_a_e : ... := by ... ✅
  have compat_θ_a_e : ... := by ... ✅
  simp_rw [compat_r_a_e, compat_θ_a_e]  ✅
  simp only [mul_add, add_mul, ...]  ✅

  have H₁ : ... := by ... ✅
  have H₂ : ... := by ... ✅

  -- ❌ STUCK HERE
  -- Goal has 6 terms lumped in one sumIdx
  -- Can't apply H₁/H₂/Identify lemmas directly

  sorry
```

**Build Status**: Clean (with sorry at line 4124)
**File**: `Riemann.lean`, lines 4036-4124

---

## Documentation References

- **Blocker V1**: `LEFT_REGROUPING_BLOCKER_OCT18.md` (original blocker from this morning)
- **JP's guidance**: Embedded in previous conversation (f₁...f₈ definitions, step-by-step sequence)
- **Identify lemmas**: Lines 1770-1820 in Riemann.lean
- **H₁/H₂**: Lines 4070-4093 in Riemann.lean

---

**Prepared by**: Claude Code
**Date**: October 18, 2025 (Evening)
**Status**: Blocked on pattern matching strategy
**Need**: Tactical guidance for applying H₁/H₂/Identify to nested sum structure
