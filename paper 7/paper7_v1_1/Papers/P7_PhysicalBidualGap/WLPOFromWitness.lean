/-
Papers/P7_PhysicalBidualGap/WLPOFromWitness.lean
Proof that a non-reflexivity witness in any Banach space implies WLPO.

Adapted from Paper 2 (Lee 2026a):
  Papers/P2_BidualGap/CRM_MetaClassical/Ishihara.lean

The proof follows the CRM (constructive reverse mathematics) methodology:
  1. Classical meta-extraction: given Ψ ∈ X** \ J(X), find h⋆ ∈ X* with
     (‖Ψ‖/2) < |Ψ(h⋆)|, and define g(α) := if (∀ n, α n = false) then 0 else h⋆.
     Set δ := |Ψ(h⋆)| / 2 > 0.
  2. Constructive consumption: the Ishihara kernel (Ψ, 0, g, δ) is fed to
     `WLPO_of_kernel`, which is purely intuitionistic.

This eliminates the `wlpo_of_nonreflexive_witness` axiom from Main.lean.
-/
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Tactic
import Papers.P7_PhysicalBidualGap.Basic

set_option linter.unnecessarySimpa false

namespace Papers.P7

open NormedSpace

-- ========================================================================
-- Ishihara kernel: constructive core
-- ========================================================================

/-- An Ishihara kernel packages the data needed for a constructive WLPO decision.
    Given a Banach space X, the kernel provides:
    - y ∈ X** (the bidual element)
    - f ∈ X* (base functional, typically 0)
    - g : (ℕ → Bool) → X* (the encoding map)
    - δ > 0 (the separation gap)
    such that |y(f + g(α))| is either 0 or ≥ δ, and the zero case
    characterizes "all false". -/
structure IshiharaKernel (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] where
  y     : (X →L[ℝ] ℝ) →L[ℝ] ℝ
  f     : X →L[ℝ] ℝ
  g     : (ℕ → Bool) → (X →L[ℝ] ℝ)
  δ     : ℝ
  δpos  : 0 < δ
  /-- Numeric separation: value is either 0 or at least δ in absolute value. -/
  sep   : ∀ α : ℕ → Bool, |y (f + g α)| = 0 ∨ δ ≤ |y (f + g α)|
  /-- Logical tie-in: "all false" iff the evaluation vanishes. -/
  zero_iff_allFalse :
    ∀ α : ℕ → Bool, (∀ n, α n = false) ↔ y (f + g α) = 0

/-- WLPO consumer: purely constructive (intuitionistic).
    No classical reasoning occurs here. -/
theorem WLPO_of_kernel
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (K : IshiharaKernel X) : WLPO := by
  intro α
  have h := K.sep α
  rcases h with h0 | hpos
  · -- |y(f + g α)| = 0 ⇒ y(f + g α) = 0 ⇒ all-false
    have yz0 : K.y (K.f + K.g α) = 0 := abs_eq_zero.mp h0
    exact Or.inl ((K.zero_iff_allFalse α).mpr yz0)
  · -- δ ≤ |y(f + g α)| with δ > 0 ⇒ y(f + g α) ≠ 0 ⇒ not all-false
    have pos : 0 < |K.y (K.f + K.g α)| := lt_of_lt_of_le K.δpos hpos
    have hne : K.y (K.f + K.g α) ≠ 0 := by
      intro yz0; simp [yz0] at pos
    exact Or.inr (fun hall => hne ((K.zero_iff_allFalse α).mp hall))

-- ========================================================================
-- Classical producer: builds the kernel from a non-reflexivity witness
-- ========================================================================

noncomputable section
open Classical

/-- Helper: for any nonzero continuous linear map T : E →L[ℝ] ℝ, there exists
    x with ‖x‖ ≤ 1 and (‖T‖/2) < ‖T x‖. This is a standard approximate
    supremum selection that avoids compactness.

    Adapted from Paper 2, Ishihara.lean:91-148. -/
private lemma exists_on_unitBall_gt_half_opNorm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →L[ℝ] ℝ) (hT : T ≠ 0) :
    ∃ x : E, ‖x‖ ≤ 1 ∧ (‖T‖ / 2) < ‖T x‖ := by
  by_contra h
  push_neg at h
  -- Global bound: ‖T x‖ ≤ (‖T‖/2) * ‖x‖ by scaling
  have bound_all : ∀ x : E, ‖T x‖ ≤ (‖T‖ / 2) * ‖x‖ := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      let u : E := (‖x‖)⁻¹ • x
      have hu_norm : ‖u‖ = 1 := by
        have h1 : ‖u‖ = ‖(‖x‖)⁻¹‖ * ‖x‖ := by simpa [u] using norm_smul ((‖x‖)⁻¹) x
        have h2 : ‖(‖x‖)⁻¹‖ = (‖x‖)⁻¹ :=
          by simpa [Real.norm_of_nonneg (le_of_lt (inv_pos.mpr hxpos))]
        have hxne : (‖x‖ : ℝ) ≠ 0 := ne_of_gt hxpos
        have : ‖u‖ = (‖x‖)⁻¹ * ‖x‖ := by simpa [h2] using h1
        simpa [hxne] using this
      have hu_le : ‖u‖ ≤ 1 := by simpa [hu_norm]
      have hu_ball : ‖T u‖ ≤ ‖T‖ / 2 := h u hu_le
      have hxu : (‖x‖ : ℝ) • u = x := by
        have hxne : (‖x‖ : ℝ) ≠ 0 := ne_of_gt hxpos
        simpa [u] using smul_inv_smul₀ hxne x
      have : T x = ‖x‖ * T u := by simpa [hxu] using T.map_smul (‖x‖ : ℝ) u
      calc
        ‖T x‖ = ‖‖x‖ * T u‖ := by simpa [this]
        _ = ‖x‖ * ‖T u‖     := by simpa using (norm_mul (‖x‖) (T u))
        _ ≤ (‖T‖ / 2) * ‖x‖ := by
          have := mul_le_mul_of_nonneg_left hu_ball (norm_nonneg x)
          simpa [mul_comm] using this
  -- Turn pointwise bound into op-norm bound
  have hnonneg : 0 ≤ ‖T‖ / 2 := div_nonneg (norm_nonneg _) (by norm_num)
  have hle : ‖T‖ ≤ ‖T‖ / 2 := by
    simpa using
      ContinuousLinearMap.opNorm_le_bound T hnonneg
        (by intro x; simpa [mul_comm] using bound_all x)
  -- Hence ‖T‖ = 0, hence T = 0, contradiction
  have hTnorm0 : ‖T‖ = 0 := by
    have : 0 ≤ ‖T‖ := norm_nonneg _
    nlinarith
  have T0 : T = 0 := by
    ext x
    have hx' : ‖T x‖ ≤ ‖T‖ * ‖x‖ := by simpa using T.le_opNorm x
    have : ‖T x‖ ≤ 0 := by simpa [hTnorm0] using hx'
    have : ‖T x‖ = 0 := le_antisymm this (norm_nonneg _)
    simpa using (norm_eq_zero.mp this)
  exact hT T0

/-- **Any Banach space with a non-reflexivity witness implies WLPO.**

    Given Ψ ∈ X** \ J(X), we construct an Ishihara kernel and apply
    the constructive consumer. This is the universal forward direction
    of the bidual gap equivalence.

    Adapted from Paper 2 (Lee 2026a), Ishihara.lean:188-271. -/
theorem wlpo_of_nonreflexive_witness_proof
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] :
    (∃ Ψ : StrongDual ℝ (StrongDual ℝ X),
       Ψ ∉ Set.range (inclusionInDoubleDual ℝ X)) → WLPO := by
  classical
  intro ⟨y, hy⟩
  -- y ∈ X** \ J(X); in particular y ≠ 0
  have hy0 : y ≠ 0 := by
    intro h0; subst h0
    exact hy ⟨0, by simp⟩
  -- Extract a half-norm witness h⋆ ∈ X* with (‖y‖/2) < ‖y h⋆‖
  -- Note: StrongDual ℝ (StrongDual ℝ X) = (X →L[ℝ] ℝ) →L[ℝ] ℝ
  obtain ⟨hstar, _, hstar_big⟩ :
      ∃ h : (X →L[ℝ] ℝ), ‖h‖ ≤ 1 ∧ (‖y‖ / 2) < ‖y h‖ := by
    simpa using
      exists_on_unitBall_gt_half_opNorm (E := (X →L[ℝ] ℝ)) y hy0
  -- Define the separation gap δ := |y(h⋆)| / 2 > 0
  let δ : ℝ := ‖y hstar‖ / 2
  have δpos : 0 < δ := by
    have zero_le_half_norm_y : 0 ≤ ‖y‖ / 2 :=
      div_nonneg (norm_nonneg y) (by norm_num)
    have pos_yh : 0 < ‖y hstar‖ :=
      lt_of_le_of_lt zero_le_half_norm_y hstar_big
    simpa [δ] using half_pos pos_yh
  -- Define kernel data: f = 0, g(α) = if all-false then 0 else h⋆
  let f : X →L[ℝ] ℝ := 0
  let g : (ℕ → Bool) → (X →L[ℝ] ℝ) := fun α =>
    if (∀ n, α n = false) then 0 else hstar
  -- Separation property
  have sep : ∀ α, |y (f + g α)| = 0 ∨ δ ≤ |y (f + g α)| := by
    intro α
    by_cases hall : ∀ n, α n = false
    · left; simp [f, g, hall]
    · right
      have : δ ≤ ‖y hstar‖ := by
        have hnn : 0 ≤ ‖y hstar‖ := norm_nonneg _
        simpa [δ] using half_le_self hnn
      simpa [f, g, hall, zero_add] using this
  -- Zero-characterization
  have zero_iff_allFalse : ∀ α, (∀ n, α n = false) ↔ y (f + g α) = 0 := by
    intro α; constructor
    · intro hall; simp [f, g, hall]
    · intro h0
      by_contra hnot
      have yh_eq : y (f + g α) = y hstar := by simpa [f, g, hnot, zero_add]
      have yhstar0 : y hstar = 0 := by simpa [yh_eq] using h0
      have pos : 0 < ‖y hstar‖ := by
        have zero_le_half_norm_y : 0 ≤ ‖y‖ / 2 :=
          div_nonneg (norm_nonneg y) (by norm_num)
        exact lt_of_le_of_lt zero_le_half_norm_y hstar_big
      have zero : ‖y hstar‖ = 0 := by simpa [yhstar0]
      linarith
  -- Conclude WLPO from the kernel
  exact WLPO_of_kernel (X := X)
    { y := y, f := f, g := g, δ := δ, δpos := δpos,
      sep := sep, zero_iff_allFalse := zero_iff_allFalse }

end -- noncomputable section

end Papers.P7
