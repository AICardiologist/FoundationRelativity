# Code Extracts for JP - Direct Patching (October 14, 2025)

**Purpose:** Provide exact code sections for JP to create drop-in diffs

**Requested Sections:**
1. Schwarzschild.lean lines 1531-1605 (Γ table + commutator lemmas)
2. Riemann.lean lines 6265-6310 (h_fiber case split)

---

## Section 1: Schwarzschild.lean (Lines 1531-1605)

**File:** `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Schwarzschild.lean`

**Lines 1531-1605:**

```lean
  | _, _, _ => 0

-- Simp lemmas for nonzero Christoffel symbols in Schwarzschild spacetime.
-- These 13 lemmas cover all nonzero components (out of 4³=64 possible).
@[simp] lemma Γtot_t_tr (M r θ : ℝ) : Γtot M r θ Idx.t Idx.t Idx.r = Γ_t_tr M r := rfl
@[simp] lemma Γtot_t_rt (M r θ : ℝ) : Γtot M r θ Idx.t Idx.r Idx.t = Γ_t_tr M r := rfl
@[simp] lemma Γtot_r_tt (M r θ : ℝ) : Γtot M r θ Idx.r Idx.t Idx.t = Γ_r_tt M r := rfl
@[simp] lemma Γtot_r_rr (M r θ : ℝ) : Γtot M r θ Idx.r Idx.r Idx.r = Γ_r_rr M r := rfl
@[simp] lemma Γtot_r_θθ (M r θ : ℝ) : Γtot M r θ Idx.r Idx.θ Idx.θ = Γ_r_θθ M r := rfl
@[simp] lemma Γtot_r_φφ (M r θ : ℝ) : Γtot M r θ Idx.r Idx.φ Idx.φ = Γ_r_φφ M r θ := rfl
@[simp] lemma Γtot_θ_rθ (M r θ : ℝ) : Γtot M r θ Idx.θ Idx.r Idx.θ = Γ_θ_rθ r := rfl
@[simp] lemma Γtot_θ_θr (M r θ : ℝ) : Γtot M r θ Idx.θ Idx.θ Idx.r = Γ_θ_rθ r := rfl
@[simp] lemma Γtot_θ_φφ (M r θ : ℝ) : Γtot M r θ Idx.θ Idx.φ Idx.φ = Γ_θ_φφ θ := rfl
@[simp] lemma Γtot_φ_rφ (M r θ : ℝ) : Γtot M r θ Idx.φ Idx.r Idx.φ = Γ_φ_rφ r := rfl
@[simp] lemma Γtot_φ_φr (M r θ : ℝ) : Γtot M r θ Idx.φ Idx.φ Idx.r = Γ_φ_rφ r := rfl
@[simp] lemma Γtot_φ_θφ (M r θ : ℝ) : Γtot M r θ Idx.φ Idx.θ Idx.φ = Γ_φ_θφ θ := rfl
@[simp] lemma Γtot_φ_φθ (M r θ : ℝ) : Γtot M r θ Idx.φ Idx.φ Idx.θ = Γ_φ_θφ θ := rfl

-- In the exterior region, Γtot_differential properties:
lemma Γtot_differentiable_r_ext (M r θ : ℝ) (h : Exterior M r θ) (k a b : Idx) :
    DifferentiableAt ℝ (fun r => Γtot M r θ k a b) r := by
  cases a <;> cases k <;> cases b <;>
    (simp [Γtot]; apply DifferentiableAt.const_mul <;> try apply DifferentiableAt.inv₀ <;> try norm_num <;> nlinarith [h.r_pos, h.r_gt_M])

@[simp] lemma Γtot_θ_θθ_zero (M r θ : ℝ) : Γtot M r θ Idx.θ Idx.θ Idx.θ = 0 := by simpa [Γtot]
@[simp] lemma Γtot_t_θt_zero (M r θ : ℝ) : Γtot M r θ Idx.t Idx.θ Idx.t = 0 := by simpa [Γtot]
@[simp] lemma Γtot_r_θr_zero (M r θ : ℝ) : Γtot M r θ Idx.r Idx.θ Idx.r = 0 := by simpa [Γtot]

lemma Γtot_differentiable_θ_ext (M r θ : ℝ) (h : Exterior M r θ) (k a b : Idx) :
    DifferentiableAt ℝ (fun θ => Γtot M r θ k a b) θ := by
  cases a <;> cases k <;> cases b <;>
    (simp [Γtot]; try norm_num; try fun_prop)

/-!  JP's commutator-collapse helpers for h_fiber diagonal case (Oct 14, 2025)  -/

/-- In Schwarzschild, only the λ = k term can survive in ∑_λ Γ^k_{rλ} Γ^λ_{θa}.
    JP's solution (Oct 14, 2025) for h_fiber diagonal case. -/
@[simp] lemma comm_r_sum_collapse (M r θ : ℝ) (k a : Idx) :
  sumIdx (fun lam =>
    Γtot M r θ k Idx.r lam * Γtot M r θ lam Idx.θ a)
  =
  Γtot M r θ k Idx.r k * Γtot M r θ k Idx.θ a := by
  classical
  cases k <;> cases a <;> (simp [sumIdx_expand]; sorry)

/-- Likewise for ∑_λ Γ^k_{θλ} Γ^λ_{ra}.
    JP's solution (Oct 14, 2025) for h_fiber diagonal case. -/
@[simp] lemma comm_θ_sum_collapse (M r θ : ℝ) (k a : Idx) :
  sumIdx (fun lam =>
    Γtot M r θ k Idx.θ lam * Γtot M r θ lam Idx.r a)
  =
  Γtot M r θ k Idx.θ k * Γtot M r θ k Idx.r a := by
  classical
  cases k <;> cases a <;> (simp [sumIdx_expand]; sorry)

/-!  Supporting infrastructure for the sumIdx‑based approach  -/

-- We need to work with the 4‑component sum over all indices.
```

---

## Section 2: Riemann.lean (Lines 6265-6310)

**File:** `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean`

**Lines 6265-6310:**

```lean
          (Or.inr (by decide : Idx.θ ≠ Idx.r))
          (Or.inr (by decide : Idx.θ ≠ Idx.r))
          (Or.inl (Γtot_differentiable_θ_ext_μr M r θ h_ext k a))
          (Or.inl (g_differentiable_θ_ext        M r θ h_ext k b)))

    -- JP's solution (Oct 14, 2025): Use by_cases k=b with diagonal metric
    -- Step 1: Apply product rule
    rw [prod_r, prod_θ]

    -- Step 2: Split on diagonal vs off-diagonal
    by_cases hkb : k = b
    · -- Case k = b: DIAGONAL
      subst hkb
      -- JP's approach: use nabla_g_shape + comm collapses
      -- TODO: simp times out - needs optimization or manual steps
      sorry
    · -- Case k ≠ b: OFF-DIAGONAL
      -- JP's approach: cases k; cases b; simp [g, hkb]
      -- TODO: times out - needs more efficient tactic
      sorry
  }

  -- Lift the pointwise identity to sum level
  have h_sum :=
    congrArg (fun F : Idx → ℝ => sumIdx F) (funext h_fiber)

  -- Recognize RiemannUp definitionally (no AC explosion)
  -- JP's fix (Oct 13, 2025): pointwise via kernel lemma, then lift with sumIdx
  -- TODO: Once RiemannUp_kernel_mul_g is proven, this will work with:
  --   classical
  --   have hpt := funext (fun k => simpa [RiemannUp_kernel_mul_g, ...])
  --   simpa using congrArg (fun F => sumIdx F) hpt
  --   exact h_sum.trans h_R_sum
  sorry

/-- Left-slot analogue of the regroup lemma: use `pack_left_slot_prod` and
    the left-slot compat refolds `compat_refold_*_kb`. -/
lemma regroup_left_sum_to_RiemannUp_NEW
    (M r θ : ℝ) (h_ext : Exterior M r θ) (hθ : Real.sin θ ≠ 0) (a b : Idx) :
  sumIdx (fun k =>
    dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ b * g M a k r θ) r θ
  - dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r b * g M a k r θ) r θ)
  =
  sumIdx (fun k =>
    RiemannUp M r θ k b Idx.r Idx.θ * g M a k r θ)
:= by
```

---

## Context for JP

### Current Issues (From Your Latest Message)

1. **θ-commutator lemma is WRONG** (Schwarzschild.lean lines 1588-1594)
   - `comm_θ_sum_collapse` is mathematically false
   - For k=θ, a=r: surviving term is at λ=r, not λ=k
   - Needs replacement with `comm_θ_sum_expand` (4-term tautology)

2. **Off-diagonal case times out** (Riemann.lean line 6284)
   - Current: `cases k; cases b; simp [g, hkb]` → 16 subgoals, 200k heartbeat timeout
   - Your fix: Manufacture 3 zeros first (hg0, hdr0, hdθ0), then single simp

3. **Diagonal case times out** (Riemann.lean line 6280)
   - Current: Big simp with nabla_g_shape + comm collapses + folds → timeout
   - Your fix: Sequential rewrites (RHS rewrite, h_r/h_θ step-by-step, local cases)

### Build Status

- ✅ Clean build (3078 jobs successful)
- Sorry count: 15 total
  - Schwarzschild.lean: 2 (comm_r_sum_collapse line 1583, comm_θ_sum_collapse line 1593)
  - Riemann.lean: 13 (baseline 11 + 2 new at lines 6280, 6284)

### Infrastructure Available

From ADDENDUM_SCHWARZSCHILD_INFRASTRUCTURE.md:
- ✅ Diagonal metric with catch-all `| _, _ => 0` (line 1010)
- ✅ Sparse Christoffel with catch-all `| _, _, _ => 0` (line 1531)
- ✅ Full @[simp] tables for nonzero components
- ✅ nabla_g_shape lemma (line 1531 in infrastructure doc)
- ✅ sumIdx_expand and sumIdx infrastructure

---

## What We Need from JP

**Exact diffs** for:

1. **Schwarzschild.lean lines 1576-1594** - Replace wrong θ-collapse with correct lemmas
   - Fix `comm_θ_sum_collapse` (replace with `comm_θ_sum_expand`)
   - Complete `comm_r_sum_collapse` proof if needed

2. **Riemann.lean lines 6275-6284** - Implement efficient tactics for both cases
   - Off-diagonal case (line 6282-6284): O(1) 3-zero manufacture approach
   - Diagonal case (line 6276-6280): Sequential rewrite approach

---

## Ready for Patching

Both code sections are extracted above. JP can provide exact diff blocks that we can apply directly to complete the h_fiber proof.

**Expected outcome**: Once patched, h_fiber proof should close completely, reducing sorry count by 4 (2 in Schwarzschild + 2 in Riemann).

This is the final 5% to complete the RiemannUp curvature formalization!
