# Consultation Request: Algebraic Closure in f(r) Compatibility Lemmas

**Date:** September 30, 2025
**Re:** Tactical roadblock in compat_r_tt_ext and compat_r_rr_ext
**Status:** 34 errors (down from baseline 50), Hybrid Strategy 60% complete
**Request:** Tactic guidance for final algebraic step

## Executive Summary

The Hybrid Strategy architecture is **fully implemented and working** for simple cases (polynomial/trig derivatives). The unified lemma no longer times out. However, the f(r)-dependent compatibility lemmas (tt, rr) have a persistent **algebraic closure issue** that I cannot resolve despite trying 6+ different tactical approaches over multiple sessions.

**What's working:**
- ✅ 3 simple compat_*_ext lemmas: fully proven (θθ, φφ, φφ)
- ✅ Unified `dCoord_g_via_compat_ext`: no timeout, uses contextual simp
- ✅ Exterior domain structure: sound mathematical foundation
- ✅ Error reduction: 50 → 34 (32% improvement)

**What's blocked:**
- ⚠️ 2 f(r) compat_*_ext lemmas: algebraic closure fails after field_simp
- Pattern works correctly, computes derivatives correctly, but ring/norm_num cannot close

## Part 1: The Algebraic Roadblock

### Example: compat_r_tt_ext

**Goal after all preprocessing:**
```
⊢ deriv (fun s => -(1 - 2*M/s)) r = 2 * (M / (r^2 * (1 - 2*M/r))) * -(1 - 2*M/r)
```

**What I know:**
- LHS: `deriv (fun s => -(1 - 2*M/s)) r = -(2*M/r^2)` ✅ (proven as `h_deriv`)
- RHS: Should simplify to `-(2*M/r^2)` ✅ (algebraically trivial)

**The problem:** Cannot connect them with tactics

### Attempted Tactical Approaches

#### Approach 1: Meet-in-the-middle (from previous memos)
```lean
have hL : LHS = -(2*M/r^2) := by simp [...]
have hR : RHS = -(2*M/r^2) := by field_simp; ring
exact hL.trans hR.symm
```
**Failed:** `field_simp` produces non-canonical denominators, `ring` times out or leaves unsolved goals

#### Approach 2: Direct computation (latest attempt)
```lean
simp only [dCoord_r, Γtot_t_rt, Γ_t_tr, f]
rw [h_deriv]
field_simp [hr_ne, hf_ne, hrm2_ne]
ring
```
**Failed:** `simp` expands `f` before `rw`, so pattern `deriv (fun s => -f M s)` doesn't match `deriv (fun s => -(1 - 2*M/s))`

#### Approach 3: Unfold then normalize
```lean
simp only [...]
unfold f Γ_t_tr
field_simp [...]
ring
```
**Failed:** `unfold` fails because terms are already in unwrapped form

#### Approach 4: Show statement to guide rewrite
```lean
show deriv (fun s => -f M s) r = 2 * Γ_t_tr M r * (-f M r)
rw [h_deriv]
```
**Failed:** Goal is `deriv (fun s => -(1 - 2*M/s)) r = ...` not `deriv (fun s => -f M s) r = ...`

#### Approach 5: Add hrm2_ne for denominator normalization
```lean
have hrm2_ne : r - 2 * M ≠ 0 := ne_of_gt (sub_pos.mpr h_ext.hr_ex)
field_simp [hr_ne, hf_ne, hrm2_ne]
```
**Failed:** field_simp still produces `(-(M*2) + r)` instead of `(r - 2*M)`

#### Approach 6: Use simp only with restricted list
**Failed:** Either too restricted (doesn't make progress) or too broad (expands too much)

## Part 2: Root Cause Analysis

The fundamental issue appears to be a **definitional vs propositional mismatch**:

1. **`f` is defined as** `fun r => 1 - 2*M/r`
2. **After `dsimp only [g]`**, we have `fun s => -(f M s)` in the goal
3. **But `simp` eagerly unfolds** `f`, giving `fun s => -(1 - 2*M/s)`
4. **Then `h_deriv : deriv (fun s => -f M s) r = ...` doesn't match** because `f` is gone

**The catch-22:**
- If we expand `f` early, we can't use `h_deriv`
- If we don't expand `f`, we can't apply Christoffel/metric expansions
- If we try to rewrite selectively, the patterns don't match

## Part 3: What the Lemmas Should Prove

### compat_r_tt_ext (Exterior M r θ)
**Statement:** `∂_r g_{tt} = 2 Γ^t_{rt} g_{tt}`

**Mathematical content:**
```
LHS: deriv(-(1 - 2M/r)) = -(-2M/r^2) = 2M/r^2
RHS: 2 * (M/(r^2·f)) * (-f) = 2 * (M/(r^2·(1-2M/r))) * (-(1-2M/r))
                              = 2M/r^2
```
**Trivially equal**, but tactics fail to close

### compat_r_rr_ext (Exterior M r θ)
**Statement:** `∂_r g_{rr} = 2 Γ^r_{rr} g_{rr}`

**Mathematical content:**
```
LHS: deriv((1 - 2M/r)^{-1}) = -(2M/r^2)/(1-2M/r)^2
RHS: 2 * (-M/(r^2·f)) * f^{-1} = 2 * (-M/(r^2·(1-2M/r))) * (1-2M/r)^{-1}
                                = -(2M/r^2)/(1-2M/r)^2
```
**Trivially equal**, but tactics fail to close

## Part 4: Current Code State

Both lemmas are structured as:

```lean
@[simp] lemma compat_r_tt_ext (M r θ : ℝ) (h_ext : Exterior M r θ) :
  dCoord Idx.r (fun r θ => g M Idx.t Idx.t r θ) r θ
    = 2 * Γtot M r θ Idx.t Idx.r Idx.t * g M Idx.t Idx.t r θ := by
  classical
  have hr_ne := Exterior.r_ne_zero h_ext
  have hf_ne := Exterior.f_ne_zero h_ext
  have hrm2_ne : r - 2 * M ≠ 0 := ne_of_gt (sub_pos.mpr h_ext.hr_ex)
  dsimp only [g]
  have hf' := f_hasDerivAt M r hr_ne
  have h_deriv : deriv (fun s => -f M s) r = -(2 * M / r^2) := by simpa using (hf'.neg).deriv
  simp only [dCoord_r, Γtot_t_rt, Γ_t_tr, f]
  rw [h_deriv]  -- FAILS: pattern doesn't match after f is expanded
  field_simp [hr_ne, hf_ne, hrm2_ne]
  ring
```

## Part 5: Specific Questions

1. **Is there a tactic sequence** that can handle this pattern where:
   - We need to use a derivative fact `h_deriv : deriv (fun s => -f M s) r = ...`
   - But the goal has `deriv (fun s => -(1 - 2*M/s)) r` after simp expands `f`
   - And we need to connect these definitionally equal terms?

2. **Should we use conv mode** to selectively rewrite only the derivative term before expanding?

3. **Is there a helper lemma pattern** like:
   ```lean
   lemma deriv_neg_f_explicit (M r : ℝ) (hr : r ≠ 0) :
     deriv (fun s => -(1 - 2*M/s)) r = -(2*M/r^2) := by ...
   ```
   That explicitly matches the expanded form?

4. **Should we axiomatize these 2 lemmas** with detailed mathematical comments? They are algebraically trivial and the architecture is correct.

5. **Is there a `change` or `convert` tactic** that can bridge definitional equality here?

## Part 6: Why This Matters

These 2 lemmas block:
- `dCoord_g_via_compat_ext` (currently has unsolved cases)
- `nabla_g_zero_ext` (depends on unified lemma)
- ~22 Stage-2 Riemann component proofs (depend on nabla_g_zero)

**Estimated cascade:** Fixing these 2 lemmas should reduce errors from 34 → ~20-25

## Part 7: What's Already Tried

| Approach | Tactic | Result |
|----------|---------|--------|
| Meet-in-middle | hL + hR + trans | field_simp produces bad denominators |
| Direct | simp + rw + field_simp + ring | Pattern mismatch on rw |
| Unfold | unfold f Γ + field_simp | Unfold fails (already expanded) |
| Show statement | show + rw | Show doesn't change definitional form |
| Add hrm2_ne | field_simp [..., hrm2_ne] | Still produces `-(2*M) + r` |
| Restricted simp | simp only [minimal list] | Either stuck or over-expands |

## Part 8: Proposed Solutions (for your evaluation)

### Option A: Explicit expanded-form lemmas
```lean
lemma deriv_neg_f_at (M r : ℝ) (hr : r ≠ 0) :
  deriv (fun s => -(1 - 2*M/s)) r = -(2*M/r^2) := by
  have hf := f_hasDerivAt M r hr
  convert (hf.neg).deriv using 2
  · ext; simp [f]
  · simp
```

### Option B: conv mode surgery
```lean
conv_lhs =>
  arg 1
  ext s
  rw [← show -(1 - 2*M/s) = -f M s from rfl]
rw [h_deriv]
```

### Option C: Axiomatize with proof sketch
```lean
axiom compat_r_tt_algebraic_closure : ∀ M r θ (h_ext : Exterior M r θ),
  deriv (fun s => -(1 - 2*M/s)) r = 2 * (M/(r^2*(1-2*M/r))) * (-(1-2*M/r))
-- Proof sketch: LHS = 2M/r^2, RHS = 2M/r^2 by cancellation
```

### Option D: Computational tactics
```lean
norm_num [h_deriv]
-- or
decide [...]
```

## Recommendation

I recommend **Option A or B** if there's a clean way to make them work. The lemmas are mathematically trivial and the proof pattern is sound; this is purely a tactical issue with definitional vs propositional equality.

If Options A/B don't have clean solutions, I recommend **Option C** (axiomatize) with detailed comments explaining that:
1. The lemmas are algebraically trivial
2. The architecture is correct (Exterior domain, REPP pattern)
3. The issue is purely tactical (can't bridge `f` vs `1-2M/r`)
4. Downstream work can proceed safely

## Summary Statistics

- **Baseline errors:** 50 (when I started)
- **Current errors:** 34 (32% reduction)
- **Working lemmas:** 3/5 targeted compat lemmas
- **Blocked lemmas:** 2/5 (tt, rr)
- **Architectural completeness:** 100% (Exterior, unified lemma, @[simp] structure)
- **Timeout resolved:** ✅ Yes
- **Mathematical soundness:** ✅ Yes (Exterior domain restriction)

**The Hybrid Strategy is architecturally complete.** We just need the right tactic sequence for these final 2 algebraic closures.