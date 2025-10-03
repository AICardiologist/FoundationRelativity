# Response to Junior Professor: Patch H Analysis and Status Report

**Date:** October 2, 2025
**Re:** Patch H (deriv_mul argument reordering) and remaining work

---

## Executive Summary

**Patch H is NOT needed and would break the working code.**

The derivative calculators have been successfully fixed using the correct API for mathlib snapshot 24dd4cac. Build status: ✅ **0 compilation errors**, 14 documented sorries.

---

## Part 1: Why Patch H is Incorrect

### Your Claim
> "In mathlib 24dd4cac, the signature is:
> ```lean
> deriv_mul (x : ℝ) (f g : ℝ → ℝ) :
>   deriv (fun y => f y * g y) x = ...
> ```"

### Actual Signature in Our Mathlib
```bash
$ grep -A 2 "^theorem deriv_mul " .lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean

theorem deriv_mul (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
    deriv (c * d) x = deriv c x * d x + c x * deriv d x :=
  (hc.hasDerivAt.mul hd.hasDerivAt).deriv
```

**Key difference:** The lemma expects **differentiability proofs** (`hc` and `hd`), not `(x, f, g)`.

### What Patch H Would Do
Your proposed change:
```lean
have h_mul := deriv_mul r (fun s => s^2) (fun s => f M s)
```

This passes `r : ℝ` where `DifferentiableAt ℝ c x` is expected, causing:
```
error: Application type mismatch: The argument r has type ℝ
but is expected to have type DifferentiableAt ℝ ?c ?x
```

**Conclusion:** Patch H would reintroduce the exact type error we just fixed.

---

## Part 2: The Correct Fix (Already Applied)

### What We Did

**Lines 969-988 (deriv_Γ_t_tr_at):**
```lean
-- Component differentiability for the product rule
have hd1 : DifferentiableAt ℝ (fun s => s^2) r :=
  (differentiable_pow 2).differentiableAt
have hd2 : DifferentiableAt ℝ (fun s => f M s) r :=
  (contDiffAt_f M r hr).differentiableAt le_top
have hHdiff : DifferentiableAt ℝ (fun s => s^2 * f M s) r := hd1.mul hd2

-- Product rule: pass differentiability proofs
have h_mul := deriv_mul hd1 hd2
show deriv ((fun s => s^2) * (fun s => f M s)) r = 2 * r * f M r + r^2 * (2 * M / r^2)
rw [h_mul, h1, h2]
ring
```

**Lines 1045-1054 (deriv_Γ_φ_θφ_at):**
```lean
have hd_cos : DifferentiableAt ℝ (fun t => Real.cos t) θ :=
  Real.differentiable_cos.differentiableAt
have hd_csc : DifferentiableAt ℝ (fun t => (Real.sin t)⁻¹) θ :=
  (Real.differentiable_sin.differentiableAt).inv hθ

have hm := deriv_mul hd_cos hd_csc  -- Pass proofs, not functions
```

**Lines 1085-1089 (deriv_Γ_θ_φφ_at):**
```lean
have hd_sin : DifferentiableAt ℝ (fun t => Real.sin t) θ :=
  Real.differentiable_sin.differentiableAt
have hd_cos : DifferentiableAt ℝ (fun t => Real.cos t) θ :=
  Real.differentiable_cos.differentiableAt

have hprod := deriv_mul hd_sin hd_cos  -- Pass proofs
```

### Similar Fix for deriv_const_mul

**Lines 998-1003 (deriv_Γ_t_tr_at):**
```lean
have hd_inv : DifferentiableAt ℝ (fun s => (s^2 * f M s)⁻¹) r := hHdiff.inv hden
have hΓ :
    deriv (fun s => Γ_t_tr M s) r
      = M * deriv (fun s => (s^2 * f M s)⁻¹) r := by
  rw [hΓfun]
  exact deriv_const_mul M hd_inv  -- Pass differentiability proof
```

**Lines 1029-1036 (deriv_Γ_r_rr_at):**
```lean
have hd_Γttr : DifferentiableAt ℝ (fun s => Γ_t_tr M s) r :=
  DifferentiableAt.const_mul hd_inv M
have hderiv :
    deriv (fun s => Γ_r_rr M s) r
      = (-1) * deriv (fun s => Γ_t_tr M s) r := by
  rw [hΓfun]
  exact deriv_const_mul (-1) hd_Γttr  -- Pass proof
```

---

## Part 3: Build Verification

```bash
$ lake build Papers.P5_GeneralRelativity.GR.Riemann 2>&1 | grep "^error:" | grep -v "Lean exited" | grep -v "build failed" | wc -l
0
```

✅ **Zero compilation errors**

```bash
$ grep -n "^\s*sorry\s*$" Papers/P5_GeneralRelativity/GR/Riemann.lean | wc -l
14
```

✅ **14 sorries** (down from 18 after removing C³ shim)

All four derivative calculator lemmas compile successfully:
- `deriv_Γ_t_tr_at` ✅
- `deriv_Γ_r_rr_at` ✅
- `deriv_Γ_φ_θφ_at` ✅
- `deriv_Γ_θ_φφ_at` ✅

---

## Part 4: Remaining Work for TRUE LEVEL 3 (Zero Sorries)

From CONSULT_MEMO_9.md analysis, we have **15 sorries** blocking TRUE LEVEL 3:

### Critical Path (2 sorries - BOTTLENECK)

**Γtot_differentiable_r/θ (Lines 1561-1569)** - 2 sorries
```lean
lemma Γtot_differentiable_r (M r θ : ℝ) (i j k : Idx) :
  DifferentiableAt_r (fun r θ => Γtot M r θ i j k) r θ := by
  sorry

lemma Γtot_differentiable_θ (M r θ : ℝ) (i j k : Idx) :
  DifferentiableAt_θ (fun r θ => Γtot M r θ i j k) r θ := by
  sorry
```

**Issue:** Case analysis after `simp only [Γtot]` breaks case tag alignment.

**Your guidance requested:**
- Should we use NonzeroChristoffel dependent type?
- Manual match for each component?
- Different tactical approach?
- Accept as axioms (mathematically obvious)?

The 13 nonzero Christoffel components have base lemmas proven (e.g., `differentiableAt_Γ_t_tr_r`), but exhaustive case analysis fails.

---

### Dependent Lemmas (5 sorries)

Once Γtot differentiability is proven, these should cascade:

1. **ContractionC_differentiable_r/θ** (2 sorries, lines 1516-1524)
   - Issue: `DifferentiableAt.sum` doesn't unify with `sumIdx` expansion
   - Question: Rewrite sumIdx to Finset.sum? Prove helper equivalence?

2. **dCoord_g_differentiable_r/θ** (2 sorries, lines TBD)
   - C³ smoothness (∂(∂g))
   - Question: Are these critical for TRUE LEVEL 3? Can we defer?

3. **dCoord_ContractionC_expanded** (1 sorry, lines 1195-1209)
   - Structural lemma for derivative distributivity
   - With Γtot_diff as @[simp], should work via `discharge_diff` tactic

---

### Main Theorem (6 sorries)

4. **alternation_dC_eq_Riem** (6 sorries, lines TBD)
   - Depends on dCoord_ContractionC_expanded
   - Question: Is remaining sorry just algebraic residual or significant work?

---

### Non-Critical (1 sorry discovered)

We now have **14 sorries** but CONSULT_MEMO_9 listed 15. The extra sorry may be from:
- Infrastructure (should be 0 after C³ shim removal)
- Scaffolding (18 commented-out sorries in allowlist, not counted)

---

## Part 5: Request for Tactical Guidance

### Question 1: Γtot Case Analysis Strategy
The case-by-case approach for Γtot_differentiable_r/θ fails after `simp only [Γtot]` because expansion changes goal structure:

```lean
lemma Γtot_differentiable_r (M r θ : ℝ) (i j k : Idx) :
  DifferentiableAt_r (fun r θ => Γtot M r θ i j k) r θ := by
  cases i <;> cases j <;> cases k
  -- After simp [Γtot], case tags don't align
  case t.t.r | t.r.t =>  -- Error: Case tag `t.t.r` not found
    sorry
```

**Proposed approaches:**
- A. Use your `NonzeroChristoffel` type with `differentiableAt_Γtot_nonzero_r/θ`
- B. Manual match without expanding Γtot
- C. Accept as axioms (defer to later paper)

**Which do you recommend for this stage?**

### Question 2: sumIdx vs Finset.sum
`DifferentiableAt.sum` expects standard `∑ i ∈ u, ...` but we use custom `sumIdx`. Should we:
- A. Prove `(fun r => sumIdx F) = (fun r => ∑ i ∈ univ, F i r)`
- B. Rewrite all sumIdx uses to Finset.sum
- C. Expand to 4 terms manually, use `DifferentiableAt.add`

### Question 3: Priority
Given time constraints, should we:
- Focus on Γtot (unblocks 90% of remaining work)
- Complete all C1 smoothness first
- Skip C2 lemmas (dCoord_g) and accept Level 2.5

---

## Part 6: Possible Source of Confusion

Your Patch H might be based on:
1. **Different mathlib version** - Earlier snapshots may have had `(x, f, g)` order
2. **Different module** - `HasDerivAt.mul` vs `deriv_mul` have different APIs
3. **Misreading the signature** - Implicit arguments `{c d : 𝕜 → F} {x : 𝕜}` before explicit ones

In mathlib 24dd4cac (`leanprover-community/mathlib4@24dd4cac`), the correct pattern is:
```lean
theorem deriv_mul (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) : ...
```

Not `(x, c, d)`.

---

## Conclusion

**Action Items:**
1. ✅ Derivative calculators fixed (DONE)
2. ⏸️ Awaiting your tactical guidance on Γtot case analysis
3. ⏸️ Awaiting decision on sumIdx vs Finset.sum
4. ⏸️ Awaiting priority guidance (Level 3 vs Level 2.5)

**Current Milestone:** Phase 3.2 complete - C1 infrastructure working, derivative calculators proven, build passing.

**Next Milestone:** Prove Γtot_differentiable_r/θ to unblock TRUE LEVEL 3.

---

**Attachment:** `Riemann.lean` (commit: fix(P5/GR): Fix deriv_mul API for Lean 4.23.0-rc2)

Please advise on Questions 1-3 above.
