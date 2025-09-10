/-
  Papers/P2_BidualGap/Constructive/Ishihara.lean
  Argument for BidualGapStrong -> WLPO, via the Ishihara kernel.

  CRM methodology split:
  • Classical meta-reasoning (fenced in `section ClassicalMeta`):
      extract y ∈ X** \ j(X), obtain a half-norm witness h⋆, define g(α) by
      case-splitting on an undecidable predicate.
  • Constructive consumption:
      the IshiharaKernel API and WLPO_of_kernel are intuitionistically valid.

  Implementation notes:
  - Avoid fragile patterns; expand normalization and op-norm steps explicitly.
-/
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Group.Completeness
import Papers.P2_BidualGap.Basic
import Papers.P2_BidualGap.Constructive.OpNormCore

namespace Papers.P2.Constructive
open Papers.P2
open scoped BigOperators

noncomputable section

-- ------------------------- Classical meta-reasoning -------------------------
section ClassicalMeta
open Classical

/-- Classical: find x on the unit ball with ‖T x‖ > ‖T‖/2 (no compactness needed). -/
lemma exists_on_unitBall_gt_half_opNorm
  {E} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (T : E →L[ℝ] ℝ) (hT : T ≠ 0) :
  ∃ x : E, ‖x‖ ≤ 1 ∧ (‖T‖ / 2) < ‖T x‖ := by
  by_contra h
  push_neg at h
  -- Global bound from unit-ball bound
  have bound_all : ∀ x : E, ‖T x‖ ≤ (‖T‖ / 2) * ‖x‖ := by
    intro x
    by_cases hx : x = 0
    · simpa [hx, norm_zero, mul_zero, div_nonneg, norm_nonneg] using
        (show (0 : ℝ) ≤ (‖T‖ / 2) * ‖x‖ from
          mul_nonneg (div_nonneg (norm_nonneg _) (by norm_num)) (norm_nonneg _))
    · have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      let u : E := (‖x‖)⁻¹ • x
      have hu_norm : ‖u‖ = 1 := by
        have h1 : ‖u‖ = ‖(‖x‖)⁻¹‖ * ‖x‖ := by simpa [u] using norm_smul ((‖x‖)⁻¹) x
        have h2 : ‖(‖x‖)⁻¹‖ = (‖x‖)⁻¹ := by
          have : 0 < ‖x‖ := norm_pos_iff.mpr hx
          simpa [Real.norm_of_nonneg (le_of_lt (inv_pos.mpr this))]
        have hxne : (‖x‖ : ℝ) ≠ 0 := ne_of_gt hxpos
        simpa [h2, hxne] using h1
      have hu_le : ‖u‖ ≤ 1 := by simpa [hu_norm]
      have hu_ball : ‖T u‖ ≤ ‖T‖ / 2 := h u hu_le
      have hxu : (‖x‖ : ℝ) • u = x := by
        have hxne : (‖x‖ : ℝ) ≠ 0 := ne_of_gt hxpos
        simpa [u] using smul_inv_smul₀ hxne x
      have h_Tx_eq : T x = (‖x‖) • T u := by
        simpa [hxu] using T.map_smul (‖x‖ : ℝ) u
      calc
        ‖T x‖ = ‖(‖x‖) • T u‖       := by rw [h_Tx_eq]
        _     = ‖x‖ * ‖T u‖         := by
          rw [norm_smul, Real.norm_of_nonneg (norm_nonneg x)]
        _     ≤ ‖x‖ * (‖T‖ / 2)     := by
          have := mul_le_mul_of_nonneg_left hu_ball (norm_nonneg x)
          simpa [mul_comm] using this
        _     = (‖T‖ / 2) * ‖x‖     := by simpa [mul_comm]
  have hnonneg : 0 ≤ ‖T‖ / 2 := div_nonneg (norm_nonneg _) (by norm_num)
  have hle : ‖T‖ ≤ ‖T‖ / 2 :=
    ContinuousLinearMap.opNorm_le_bound T hnonneg (by intro x; simpa [mul_comm] using bound_all x)
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

end ClassicalMeta

-- ----------------------------- Constructive API -----------------------------

-- Delegate normability to the OpNorm core.
lemma hasOpNorm_zero {X} [NormedAddCommGroup X] [NormedSpace ℝ X] :
  OpNorm.HasOpNorm (0 : X →L[ℝ] ℝ) :=
  OpNorm.hasOpNorm_zero

lemma hasOpNorm_CLF {X} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (h : X →L[ℝ] ℝ) : OpNorm.HasOpNorm h :=
  OpNorm.hasOpNorm_CLF h

/-- Ishihara kernel: the constructive consumer interface. -/
structure IshiharaKernel (X : Type _) [NormedAddCommGroup X] [NormedSpace ℝ X] where
  y     : (X →L[ℝ] ℝ) →L[ℝ] ℝ
  f     : X →L[ℝ] ℝ
  g     : (ℕ → Bool) → (X →L[ℝ] ℝ)
  δ     : ℝ
  δpos  : 0 < δ
  sep   : ∀ α : ℕ → Bool, |y (f + g α)| = 0 ∨ δ ≤ |y (f + g α)|
  zero_iff_allFalse :
    ∀ α : ℕ → Bool, (∀ n, α n = false) ↔ y (f + g α) = 0
  closed_add : ∀ α, OpNorm.HasOpNorm (f + g α)

/-- Monomorphic witness package to transport instances cleanly. -/
structure KernelWitness where
  X : Type
  [Xng : NormedAddCommGroup X]
  [Xns : NormedSpace ℝ X]
  [Xc  : CompleteSpace X]
  K : IshiharaKernel X

attribute [instance] KernelWitness.Xng KernelWitness.Xns KernelWitness.Xc

/-- A tiny helper: just re-expose the separation disjunction. -/
lemma kernel_threshold
  {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (K : IshiharaKernel X) (α : ℕ → Bool) :
  |K.y (K.f + K.g α)| = 0 ∨ |K.y (K.f + K.g α)| ≥ K.δ := by
  rcases K.sep α with h0 | hge
  · exact Or.inl h0
  · exact Or.inr hge

/-- Constructive consumer: a kernel with a positive gap yields `WLPO`. -/
theorem WLPO_of_kernel
  {X : Type _} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (K : IshiharaKernel X) : WLPO := by
  intro α
  rcases K.sep α with h0 | hpos
  · have yz0 : K.y (K.f + K.g α) = 0 := abs_eq_zero.mp h0
    exact Or.inl ((K.zero_iff_allFalse α).mpr yz0)
  ·
    have pos : 0 < |K.y (K.f + K.g α)| := lt_of_lt_of_le K.δpos hpos
    have hne : K.y (K.f + K.g α) ≠ 0 := by
      intro yz0; have : |K.y (K.f + K.g α)| = 0 := by simp [yz0]
      exact (ne_of_gt pos) this
    have : ¬ (∀ n, α n = false) := by
      intro hall
      have yz0 : K.y (K.f + K.g α) = 0 := (K.zero_iff_allFalse α).mp hall
      exact hne yz0
    exact Or.inr this

/-- Wrapper used by the main equivalence file. -/
def WLPO_of_witness (W : KernelWitness) : WLPO :=
  @WLPO_of_kernel W.X W.Xng W.Xns W.K

-- ---------------- Classical meta-reasoning: kernel construction -------------
section ClassicalMeta
open Classical

/-- Gap ⇒ WLPO: classical extraction + constructive consumption. -/
theorem WLPO_of_gap (hGap : BidualGapStrong) : WLPO := by
  -- unpack
  rcases hGap with ⟨X, Xng, Xns, Xc, _dualBan, _bidualBan, hNotSurj⟩
  letI : NormedAddCommGroup X := Xng
  letI : NormedSpace ℝ X := Xns
  letI : CompleteSpace X := Xc

  -- extract y ∉ range j
  let j := NormedSpace.inclusionInDoubleDual ℝ X
  have : ∃ y : (X →L[ℝ] ℝ) →L[ℝ] ℝ, y ∉ Set.range j := by
    have : ¬ (∀ y, y ∈ Set.range j) := by
      simpa [Function.Surjective, Set.range] using hNotSurj
    push_neg at this; exact this
  rcases this with ⟨y, hy⟩

  -- y ≠ 0 (since 0 ∈ range j)
  have hy0 : y ≠ 0 := by
    intro h0; subst h0
    exact hy ⟨0, by simp⟩

  -- Half-norm witness h⋆ in X* (uses the classical lemma)
  obtain ⟨hstar, hstar_le1, hstar_big⟩ :
      ∃ h : (X →L[ℝ] ℝ), ‖h‖ ≤ 1 ∧ (‖y‖ / 2) < ‖y h‖ := by
    simpa using
      (exists_on_unitBall_gt_half_opNorm (E := (X →L[ℝ] ℝ)) y hy0)

  -- Define the gap from the actual evaluation; avoids norm-instance issues on the bidual
  let δ : ℝ := ‖y hstar‖ / 2
  have δpos : 0 < δ := by
    -- 0 ≤ ‖y‖/2, so from (‖y‖/2) < ‖y hstar‖ we get 0 < ‖y hstar‖
    have zero_le_half_norm_y : 0 ≤ ‖y‖ / 2 :=
      div_nonneg (norm_nonneg y) (by norm_num)
    have pos_yh : 0 < ‖y hstar‖ :=
      lt_of_le_of_lt zero_le_half_norm_y hstar_big
    simpa [δ] using half_pos pos_yh

  -- kernel pieces (LEM in the meta-logic)
  let f : X →L[ℝ] ℝ := 0
  let g : (ℕ → Bool) → (X →L[ℝ] ℝ) := fun α =>
    if (∀ n, α n = false) then 0 else hstar

  -- separation
  have sep : ∀ α, |y (f + g α)| = 0 ∨ δ ≤ |y (f + g α)| := by
    intro α; by_cases hall : ∀ n, α n = false
    · left;  simp [f, g, hall]      -- y(0) = 0
    · right
      -- δ ≤ ‖y hstar‖ because a/2 ≤ a for a ≥ 0
      have : δ ≤ ‖y hstar‖ := by
        have hnn : 0 ≤ ‖y hstar‖ := norm_nonneg _
        -- for ℝ, `half_le_self hnn : ‖y hstar‖/2 ≤ ‖y hstar‖`
        simpa [δ] using half_le_self hnn
      -- rewrite to abs and unfold f,g
      simpa [f, g, hall, zero_add, Real.norm_eq_abs] using this

  -- zero characterization
  have zero_iff_allFalse : ∀ α, (∀ n, α n = false) ↔ y (f + g α) = 0 := by
    intro α; constructor
    · intro hall; simp [f, g, hall]
    · intro h0; by_contra hnot
      have yh_eq : y (f + g α) = y hstar := by simpa [f, g, hnot, zero_add]
      have yhstar0 : y hstar = 0 := by simpa [yh_eq] using h0
      have pos : 0 < ‖y hstar‖ := by
        -- We already proved this in δpos proof
        have zero_le_half_norm_y : 0 ≤ ‖y‖ / 2 :=
          div_nonneg (norm_nonneg y) (by norm_num)
        exact lt_of_le_of_lt zero_le_half_norm_y hstar_big
      have zero : ‖y hstar‖ = 0 := by simpa [yhstar0]
      exact absurd zero (ne_of_gt pos)

  -- normability closure (delegations)
  have closed_add : ∀ α, OpNorm.HasOpNorm (f + g α) := by
    intro α; by_cases hall : ∀ n, α n = false
    · simpa [f, g, hall] using hasOpNorm_zero
    · simpa [f, g, hall] using hasOpNorm_CLF hstar

  -- consume kernel constructively
  exact @WLPO_of_kernel X Xng Xns
    { y := y, f := f, g := g, δ := δ, δpos := δpos
      sep := sep, zero_iff_allFalse := zero_iff_allFalse, closed_add := closed_add }

end ClassicalMeta

end -- noncomputable section
end Papers.P2.Constructive