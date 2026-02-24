/-
Papers/P7_PhysicalBidualGap/ReflexiveSubspace.lean
Module 2 (Lemma B): A closed subspace of a reflexive Banach space is reflexive.

This is the bottleneck module requiring Hahn-Banach separation and extension.

Proof outline:
  Given Y ⊆ X closed subspace and X reflexive, show Y is reflexive.
  For φ ∈ Y**:
    Step 1: Lift φ to Φ ∈ X** via restriction: Φ(f) = φ(f|_Y).
    Step 2: By reflexivity, get x ∈ X with J_X(x) = Φ.
    Step 3: Show x ∈ Y using Hahn-Banach separation (if x ∉ Y, get a
            functional separating x from Y; subspace scaling forces the
            functional to annihilate Y; but then f₀(x) = Φ(f₀) = φ(0) = 0,
            contradicting separation).
    Step 4: With y = ⟨x, _⟩ : Y, verify J_Y(y) = φ using Hahn-Banach extension.
-/
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Papers.P7_PhysicalBidualGap.Basic

noncomputable section
namespace Papers.P7

open NormedSpace

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
set_option linter.unusedSectionVars false

-- ========================================================================
-- Auxiliary: separating functional annihilates a subspace
-- ========================================================================

omit [CompleteSpace X] in
/-- If a continuous linear functional satisfies f(y) < u for all y in a subspace Y,
    then f annihilates Y (f(y) = 0 for all y ∈ Y).
    Proof: For any y ∈ Y and n ∈ ℕ, n • y ∈ Y, so n * f(y) < u, forcing f(y) ≤ 0.
    Similarly -y ∈ Y gives f(y) ≥ 0. -/
private lemma annihilates_of_bounded_on_subspace
    {Y : Submodule ℝ X} (f : StrongDual ℝ X) (u : ℝ)
    (hfu : ∀ a ∈ (Y : Set X), f a < u) :
    ∀ y ∈ (Y : Set X), f y = 0 := by
  intro y hy
  apply le_antisymm
  · -- Show f(y) ≤ 0: for any n > 0, n • y ∈ Y, so n * f(y) < u
    by_contra h
    push_neg at h
    -- f(y) > 0, so choose n large enough that n * f(y) ≥ u
    obtain ⟨n, hn⟩ := exists_nat_gt (u / f y)
    have hfy_pos : (0 : ℝ) < f y := h
    have hnu : (n : ℝ) * f y > u := by
      rwa [gt_iff_lt, ← div_lt_iff₀ hfy_pos]
    have hny : (n : ℝ) • y ∈ (Y : Set X) := Y.smul_mem (n : ℝ) hy
    have h_bound := hfu _ hny
    rw [map_smul, smul_eq_mul] at h_bound
    linarith
  · -- Show f(y) ≥ 0: -y ∈ Y, so f(-y) < u, i.e., -f(y) < u
    by_contra h
    push_neg at h
    -- f(y) < 0, i.e., -f(y) > 0
    have hfy_neg : f y < 0 := h
    have hfny_pos : (0 : ℝ) < - f y := neg_pos.mpr hfy_neg
    obtain ⟨n, hn⟩ := exists_nat_gt (u / (- f y))
    have hnu : (n : ℝ) * (- f y) > u := by
      rwa [gt_iff_lt, ← div_lt_iff₀ hfny_pos]
    have hny : (n : ℝ) • (-y) ∈ (Y : Set X) := Y.smul_mem (n : ℝ) (Y.neg_mem hy)
    have h_bound := hfu _ hny
    rw [map_smul, smul_eq_mul, map_neg] at h_bound
    linarith

-- ========================================================================
-- Main theorem
-- ========================================================================

/-- A closed subspace of a reflexive Banach space is reflexive.

    Note: No separability hypothesis needed — Mathlib's Hahn-Banach works
    for all NormedSpaces over ℝ. -/
theorem reflexive_closedSubspace_of_reflexive
    (Y : Submodule ℝ X) (hYc : IsClosed (Y : Set X))
    (hX : IsReflexive ℝ X) : IsReflexive ℝ Y := by
  intro φ  -- φ : Y**
  -- ================================================================
  -- Step 1: Lift φ to Φ ∈ X** via the restriction map
  -- ================================================================
  -- res : X* → Y* maps f ↦ f ∘ (inclusion Y ↪ X)
  let res : StrongDual ℝ X →L[ℝ] StrongDual ℝ Y :=
    ContinuousLinearMap.precomp ℝ Y.subtypeL
  -- Φ := φ ∘ res : X** (lifts φ from Y** to X**)
  let Φ : StrongDual ℝ (StrongDual ℝ X) := φ.comp res
  -- ================================================================
  -- Step 2: Represent Φ using reflexivity of X
  -- ================================================================
  obtain ⟨x, hx⟩ := hX Φ
  -- hx : inclusionInDoubleDual ℝ X x = Φ
  -- i.e., ∀ f : X*, f x = Φ f = φ (f ∘ subtypeL)
  -- ================================================================
  -- Steps 3+4: Show x ∈ Y, then verify J_Y(⟨x, _⟩) = φ
  -- ================================================================
  suffices hx_mem : x ∈ (Y : Set X) by
    -- Step 4: Verify J_Y(y) = φ using Hahn-Banach extension
    let y : Y := ⟨x, hx_mem⟩
    use y
    ext g  -- g : Y* ; need: J_Y(y)(g) = φ(g)
    -- Extend g to f : X* via Hahn-Banach (norm-preserving)
    obtain ⟨f, hf_ext, _⟩ := Real.exists_extension_norm_eq Y g
    -- hf_ext : ∀ z : Y, f z = g z
    -- Chain: g(y) = f(x) = Φ(f) = φ(res f) = φ(g)
    have h1 : (g : Y → ℝ) ⟨x, hx_mem⟩ = f x := by
      rw [← hf_ext ⟨x, hx_mem⟩]
    have h2 : f x = Φ f := by
      -- From hx: inclusionInDoubleDual ℝ X x = Φ
      have := congr_fun (congr_arg DFunLike.coe hx) f
      simp only [inclusionInDoubleDual, ContinuousLinearMap.apply_apply] at this
      exact this
    have h4 : res f = g := by
      ext ⟨z, hz⟩
      simp only [res, ContinuousLinearMap.precomp_apply, ContinuousLinearMap.comp_apply,
                  Submodule.subtypeL_apply]
      exact hf_ext ⟨z, hz⟩
    -- Assemble: J_Y(y)(g) = g(y) = f(x) = Φ(f) = φ(res f) = φ(g)
    simp only [inclusionInDoubleDual, ContinuousLinearMap.apply_apply]
    rw [h1, h2]
    -- Φ f = (φ.comp res) f = φ (res f) = φ g
    show Φ f = φ g
    simp only [Φ, ContinuousLinearMap.comp_apply, h4]
  -- ================================================================
  -- Step 3: Show x ∈ Y by contradiction using Hahn-Banach separation
  -- ================================================================
  by_contra hx_not_mem
  -- Separate x from the closed convex set Y
  -- geometric_hahn_banach_closed_point requires:
  --   Convex ℝ (Y : Set X) — from Submodule.convex
  --   IsClosed (Y : Set X) — from hYc
  --   x ∉ (Y : Set X) — from hx_not_mem
  --   LocallyConvexSpace ℝ X — automatic from NormedSpace ℝ X
  obtain ⟨f₀, u, hfu, hu_x⟩ :=
    geometric_hahn_banach_closed_point (Y.convex) hYc hx_not_mem
  -- hfu : ∀ a ∈ (Y : Set X), f₀ a < u
  -- hu_x : u < f₀ x
  -- Since Y is a subspace, f₀ annihilates Y
  have h_ann : ∀ y ∈ (Y : Set X), f₀ y = 0 :=
    annihilates_of_bounded_on_subspace f₀ u hfu
  -- 0 ∈ Y, so f₀(0) = 0 < u
  have h0_lt_u : (0 : ℝ) < u := by
    have := hfu 0 Y.zero_mem
    simp [map_zero] at this
    exact this
  -- f₀(x) = Φ(f₀) = φ(res f₀) (from J_X(x) = Φ)
  have hf0x : f₀ x = φ (res f₀) := by
    have := congr_fun (congr_arg DFunLike.coe hx) f₀
    simp only [inclusionInDoubleDual, ContinuousLinearMap.apply_apply] at this
    exact this
  -- res f₀ = 0 (since f₀ annihilates Y, restriction to Y is zero)
  have h_res_zero : res f₀ = 0 := by
    ext ⟨z, hz⟩
    simp only [res, ContinuousLinearMap.precomp_apply, ContinuousLinearMap.comp_apply,
               Submodule.subtypeL_apply, ContinuousLinearMap.zero_apply]
    exact h_ann z hz
  -- So f₀(x) = φ(0) = 0
  rw [h_res_zero, map_zero] at hf0x
  -- But u < f₀(x) = 0 and 0 < u — contradiction
  linarith

/-- Contrapositive: if a closed subspace is not reflexive,
    the ambient space is not reflexive. -/
theorem not_reflexive_of_closedSubspace_not_reflexive
    (Y : Submodule ℝ X) (hYc : IsClosed (Y : Set X))
    (hY : ¬ IsReflexive ℝ Y) : ¬ IsReflexive ℝ X :=
  fun hX => hY (reflexive_closedSubspace_of_reflexive Y hYc hX)

end Papers.P7
