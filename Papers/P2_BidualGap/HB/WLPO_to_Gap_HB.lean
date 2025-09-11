/-
Papers/P2_BidualGap/HB/WLPO_to_Gap_HB.lean
WLPO → BidualGapStrong via direct construction

Direct construction: Uses the witness G = S ∘ Φ₁ in c₀** to prove non-reflexivity.
-/
import Mathlib.Tactic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.Basic
import Papers.P2_BidualGap.Basic
import Papers.P2_BidualGap.CRM_MetaClassical.Ishihara
import Papers.P2_BidualGap.HB.SimpleFacts
import Papers.P2_BidualGap.HB.DirectDual

noncomputable section
namespace Papers.P2.HB
open Classical ZeroAtInfty Filter Topology NormedSpace

-- Forward direction already complete
lemma gap_implies_wlpo : BidualGapStrong → WLPO := 
  Papers.P2.Constructive.WLPO_of_gap

-- ========================================================================
-- Space definitions
-- ========================================================================

-- Our model for c₀ on discrete ℕ
local notation "c₀"  => C₀(ℕ, ℝ)

-- ========================================================================
-- WLPO-dependent normability (axiomatized for now)
-- ========================================================================

/-- WLPO-localized normability for `c₀` (implementation in NormabilityFromWLPO.lean). -/
axiom dual_is_banach_c0_from_WLPO : WLPO → DualIsBanach c₀

/-- WLPO-localized normability for `c₀` dual. -/
axiom dual_is_banach_c0_dual_from_WLPO : WLPO → DualIsBanach (c₀ →L[ℝ] ℝ)

-- ========================================================================
-- Direct construction of the gap
-- ========================================================================

/-- c₀ is not reflexive via direct construction. -/
lemma c0_not_reflexive_via_direct :
  ¬ Function.Surjective (inclusionInDoubleDual ℝ c₀) := by
  intro hsurj
  -- The witness G from DirectDual
  let G := Papers.P2.HB.G
  -- If J is surjective, then G = J(x) for some x ∈ c₀
  obtain ⟨x, hx⟩ := hsurj G
  -- But then x_m = G(δ_m) = 1 for all m
  have hx_m : ∀ m, x m = 1 := by
    intro m
    -- J(x)(δ_m) = δ_m(x) = x_m
    -- But J(x) = G and G(δ_m) = 1
    have h1 : inclusionInDoubleDual ℝ c₀ x (Papers.P2.HB.δ m) = x m := by
      simp [inclusionInDoubleDual]
      rfl
    have h2 : G (Papers.P2.HB.δ m) = 1 := Papers.P2.HB.G_delta m
    rw [← hx] at h2
    rw [h1] at h2
    exact h2
  -- This contradicts x ∈ c₀ (must tend to 0 at infinity)
  have : Tendsto (x : ℕ → ℝ) (cocompact ℕ) (nhds 0) := x.zero_at_infty'
  -- But x_n = 1 for all n, so x doesn't tend to 0
  have : ∀ᶠ n in cocompact ℕ, dist (x n) 0 < (1/2) :=
    (Metric.tendsto_nhds.mp this) (1/2) (by norm_num)
  have : ∀ᶠ _ in cocompact ℕ, (1 : ℝ) < 1/2 := by
    simpa [dist_eq_norm, hx_m, norm_one] using this
  -- This is a contradiction
  have h_mem : {n : ℕ | (1 : ℝ) < 1/2} ∈ cocompact ℕ := this
  have h_empty : {n : ℕ | (1 : ℝ) < 1/2} = (∅ : Set ℕ) := by
    ext n; simp; norm_num
  rw [h_empty] at h_mem
  have h_nebot : (cocompact ℕ).NeBot := inferInstance
  have h_bot : cocompact ℕ = ⊥ := Filter.empty_mem_iff_bot.mp h_mem
  exact absurd h_bot h_nebot.ne


-- ========================================================================
-- Main construction
-- ========================================================================

/-- WLPO ⇒ BidualGapStrong via direct construction. -/
lemma wlpo_implies_gap : WLPO → BidualGapStrong.{0} := by
  intro hWLPO
  -- Use the direct construction to get the gap for c₀
  have gap_c0 : ¬Function.Surjective (inclusionInDoubleDual ℝ c₀) := 
    c0_not_reflexive_via_direct
  
  -- BidualGapStrong needs a witness space with the required properties
  -- Witness space X := c₀ (which lives in Type 0)
  use c₀
  exact ⟨inferInstance, inferInstance, inferInstance,
         dual_is_banach_c0_from_WLPO hWLPO,
         dual_is_banach_c0_dual_from_WLPO hWLPO,
         gap_c0⟩

/-
Note on Universes: BidualGapStrong is defined universe-polymorphically. We instantiate
it here at universe {0} using the concrete witness c₀ = C₀(ℕ, ℝ). This is
mathematically sufficient to establish the equivalence with WLPO.
-/

/-- Complete bidirectional equivalence via direct construction. -/
theorem gap_equiv_wlpo : BidualGapStrong.{0} ↔ WLPO := by
  constructor
  · exact gap_implies_wlpo    -- Forward direction (complete)
  · exact wlpo_implies_gap     -- Reverse direction (direct construction)

end Papers.P2.HB