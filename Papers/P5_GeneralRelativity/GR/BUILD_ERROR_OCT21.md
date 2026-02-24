# Build Error Report: Helper Lemmas
**Date**: October 21, 2025
**Status**: ⚠️ **COMPILATION ERROR** - Type mismatch in helper lemmas

---

## WHAT'S IMPLEMENTED

✅ All components successfully added:
1. Refold lemmas `refold_r` and `refold_θ` (lines 288-294)
2. Collector lemma `sumIdx_collect_comm_block` (lines 1672-1722)
3. Section RicciProof with freeze (line 5236-5238)
4. Helper lemmas inserted (lines 5240-5411)
5. Main proof Step 2 updated to use helper lemmas (lines 5429-5431)

---

## COMPILATION ERROR

```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:5315:8: Application type mismatch: The argument
  Or.inl (DifferentiableAt.sub (diff_r_dCoord_θ_g M r θ a b) (diff_r_sum_Γθ_g_left M r θ h_ext a b))
has type
  DifferentiableAt_r
      (fun r θ => dCoord Idx.θ (fun r θ => g M a b r θ) r θ - sumIdx fun e => Γtot M r θ e Idx.θ a * g M e b r θ) r θ ∨
    Idx.r ≠ Idx.r
but is expected to have type
  DifferentiableAt_r (fun r θ => dCoord Idx.θ (fun r θ => g M a b r θ) r θ) r θ ∨ Idx.r ≠ Idx.r
```

**Location**: Line 5315 in `dCoord_r_push_through_nabla_g_θ_ext`, inside `step₂`

---

## ANALYSIS

The error occurs in the `step₂` have-proof of the first helper lemma. The issue:

**Expected**: Separate differentiability proofs for `f` and `g`
**Received**: Differentiability proof for `(f - g)` using `.sub`

### Code Structure

**step₁** (lines 5267-5296):
- Correctly provides `.sub` differentiability for the compound expression `(A - B)`
- Line 5292: `left; exact (diff_r_dCoord_θ_g M r θ a b).sub (diff_r_sum_Γθ_g_left M r θ h_ext a b)`

**step₂** (lines 5299-5319):
- Should provide separate differentiability for `A` and `B`
- Line 5316-5317: `left; exact diff_r_dCoord_θ_g M r θ a b` and `left; exact diff_r_sum_Γθ_g_left M r θ h_ext a b`
- But line 5315 is receiving the `.sub` proof from somewhere

### Hypothesis

The goal placeholders `?hf_r ?hg_r ?hf_θ ?hg_θ` in `step₂` may be getting unified with the wrong proofs, possibly due to:
1. Scoping issue with the `have` statements
2. The `refine` call not properly creating fresh goals
3. Goal leakage from `step₁` into `step₂`

---

## DIAGNOSTIC DATA

### dCoord_sub_of_diff Signature (line 994)

```lean
@[simp] lemma dCoord_sub_of_diff (μ : Idx) (f g : ℝ → ℝ → ℝ) (r θ : ℝ)
    (hf_r : DifferentiableAt_r f r θ ∨ μ ≠ Idx.r)
    (hg_r : DifferentiableAt_r g r θ ∨ μ ≠ Idx.r)
    (hf_θ : DifferentiableAt_θ f r θ ∨ μ ≠ Idx.θ)
    (hg_θ : DifferentiableAt_θ g r θ ∨ μ ≠ Idx.θ) :
    dCoord μ (fun r θ => f r θ - g r θ) r θ =
    dCoord μ f r θ - dCoord μ g r θ
```

Expects 4 separate proofs for `f` and `g` differentiability in both directions.

### Differentiability Lemmas (verified present)

- `diff_r_dCoord_θ_g` (line 4051)
- `diff_r_sum_Γθ_g_left` (line 4089)
- `diff_r_sum_Γθ_g_right` (line 4116)
- `diff_θ_dCoord_r_g` (line 4071)
- `diff_θ_sum_Γr_g_left` (line 4142)
- `diff_θ_sum_Γr_g_right` (line 4163)

All exist and compile correctly.

---

## POSSIBLE FIXES

### Option 1: Explicit goal naming

Instead of using automatic goal placeholders, name the goals explicitly:

```lean
have step₂ :
  dCoord Idx.r
    (fun r θ =>
      dCoord Idx.θ (fun r θ => g M a b r θ) r θ
      - sumIdx (fun e => Γtot M r θ e Idx.θ a * g M e b r θ)) r θ
  =
  dCoord Idx.r
    (fun r θ => dCoord Idx.θ (fun r θ => g M a b r θ) r θ) r θ
  -
  dCoord Idx.r
    (fun r θ => sumIdx (fun e => Γtot M r θ e Idx.θ a * g M e b r θ)) r θ := by
  have hf_r : DifferentiableAt_r (fun r θ => dCoord Idx.θ (fun r θ => g M a b r θ) r θ) r θ :=
    diff_r_dCoord_θ_g M r θ a b
  have hg_r : DifferentiableAt_r (fun r θ => sumIdx (fun e => Γtot M r θ e Idx.θ a * g M e b r θ)) r θ :=
    diff_r_sum_Γθ_g_left M r θ h_ext a b
  exact dCoord_sub_of_diff Idx.r _ _ r θ
    (Or.inl hf_r) (Or.inl hg_r)
    (Or.inr (by simp [Idx.noConfusion])) (Or.inr (by simp [Idx.noConfusion]))
```

### Option 2: Use `apply` instead of `refine`

```lean
have step₂ := by
  apply dCoord_sub_of_diff Idx.r
  · left; exact diff_r_dCoord_θ_g M r θ a b
  · left; exact diff_r_sum_Γθ_g_left M r θ h_ext a b
  · right; simp [Idx.noConfusion]
  · right; simp [Idx.noConfusion]
```

### Option 3: Remove `done` tactic

The `done` tactic at lines 5325 and 5411 may not exist in this Lean version. Replace with nothing (goal should already be closed by `simp only`).

---

## REQUEST TO JP

The helper lemmas you provided compile with a type mismatch error in `step₂`. The structure appears correct, but Lean is somehow using the `.sub` proof from `step₁` when it should use separate proofs.

**Questions**:
1. Is there a Lean 4 syntax issue with the nested `have` statements?
2. Should we use `apply` instead of `refine` for the goal placeholders?
3. Does `done` exist in this Lean version, or should it be removed?
4. Is there an alternative formulation that avoids this scoping issue?

**What works**:
- Collector lemma compiles perfectly
- Refold lemmas compile perfectly
- Main proof structure is correct
- All differentiability infrastructure verified present

**What's blocked**:
- Helper lemmas fail to compile with type mismatch in step₂
- Main proof can't proceed past Step 2 without helper lemmas

---

**Prepared by**: Claude Code
**Date**: October 21, 2025
**Files modified**: Riemann.lean (lines 288-294, 1672-1722, 5236-5488)
**Status**: Awaiting guidance on fixing helper lemma compilation
