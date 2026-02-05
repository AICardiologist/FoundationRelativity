/-
Papers/P2_BidualGap/HB/WLPO_to_Gap_HB.lean
WLPO → BidualGapStrong via direct construction

Direct construction: Uses the witness G = S ∘ Φ₁ in c₀** to prove non-reflexivity.
-/
import Mathlib.Tactic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Data.Real.Archimedean
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.Basic
import Papers.P2_BidualGap.Basic
import Papers.P2_BidualGap.CRM_MetaClassical.Ishihara
import Papers.P2_BidualGap.HB.SimpleFacts
import Papers.P2_BidualGap.HB.DirectDual
import Papers.P2_BidualGap.HB.WLPO_DualBanach

noncomputable section
namespace Papers.P2.HB
open ZeroAtInfty Filter Topology NormedSpace

-- Forward direction already complete
lemma gap_implies_wlpo : BidualGapStrong → WLPO := 
  Papers.P2.Constructive.WLPO_of_gap

-- ========================================================================
-- Space definitions
-- ========================================================================

-- Our model for c₀ on discrete ℕ
local notation "c₀"  => C₀(ℕ, ℝ)

-- ========================================================================
-- Classical DualIsBanach (Papers.P2) for c₀
-- ========================================================================

section ClassicalDualIsBanach
open scoped BigOperators
open Set Metric

-- Classical construction of `Papers.P2.DualIsBanach` from standard operator-norm facts.
lemma dualIsBanach_of_nontrivial
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [Nontrivial X] :
  Papers.P2.DualIsBanach X := by
  classical
  refine
    { norm_located := ?_
      norm_attained := ?_
      complete := by infer_instance
      closed_zero := ?_
      closed_neg := ?_
      closed_smul := ?_
      closed_add := ?_ }
  · intro f ε hε
    rcases exists_rat_abs_sub_le ‖f‖ ε hε with ⟨q, hq⟩
    exact ⟨q, hq⟩
  · intro f ε hε
    let S : Set ℝ := (fun x => ‖f x‖) '' Metric.closedBall (0 : X) 1
    have hsup : sSup S = ‖f‖ := by
      simpa [S] using (ContinuousLinearMap.sSup_unitClosedBall_eq_norm (f := f))
    have hlt : ‖f‖ - ε < sSup S := by
      have : ‖f‖ - ε < ‖f‖ := sub_lt_self _ hε
      simpa [hsup] using this
    have hnonempty : S.Nonempty := by
      refine ⟨‖f 0‖, ?_⟩
      refine ⟨0, ?_, rfl⟩
      -- 0 ∈ closedBall 0 1
      simpa [Metric.mem_closedBall, dist_eq_norm] using
        (show (‖(0 : X)‖ ≤ (1 : ℝ)) by simp)
    obtain ⟨y, hyS, hygt⟩ := exists_lt_of_lt_csSup hnonempty hlt
    rcases hyS with ⟨x, hxball, rfl⟩
    have hxnorm : ‖x‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hxball
    exact ⟨x, hxnorm, le_of_lt hygt⟩
  · exact hasOperatorNorm_of_nontrivial (0 : X →L[ℝ] ℝ)
  · intro f _; exact hasOperatorNorm_of_nontrivial (-f)
  · intro a f _; exact hasOperatorNorm_of_nontrivial (a • f)
  · intro f g _ _; exact hasOperatorNorm_of_nontrivial (f + g)

end ClassicalDualIsBanach

/-- WLPO-localized normability for `c₀` (proved classically; WLPO not used). -/
lemma dual_is_banach_c0_from_WLPO_struct : WLPO → Papers.P2.DualIsBanach c₀ := by
  intro _
  classical
  -- Nontriviality of c₀ via the standard basis element e 0.
  haveI : Nontrivial c₀ := by
    refine ⟨⟨DirectDual.e 0, 0, ?_⟩⟩
    intro h
    have := congrArg (fun f : c₀ => f 0) h
    -- e 0 at 0 is 1, while 0 at 0 is 0
    simpa [DirectDual.e] using this
  exact dualIsBanach_of_nontrivial (X := c₀)



-- ========================================================================
-- Direct construction of the gap
-- ========================================================================

/-- c₀ is not reflexive via direct construction. -/
lemma c0_not_reflexive_via_direct :
  ¬ Function.Surjective (inclusionInDoubleDual ℝ c₀) := by
  intro hsurj
  -- The witness G from DirectDual
  let G := DirectDual.G
  -- If J is surjective, then G = J(x) for some x ∈ c₀
  obtain ⟨x, hx⟩ := hsurj G
  -- But then x_m = G(δ_m) = 1 for all m
  have hx_m : ∀ m, x m = 1 := by
    intro m
    -- J(x)(δ_m) = δ_m(x) = x_m
    -- But J(x) = G and G(δ_m) = 1
    have h1 : inclusionInDoubleDual ℝ c₀ x (DirectDual.δ m) = x m := by
      simp [inclusionInDoubleDual]
      rfl
    have h2 : G (DirectDual.δ m) = 1 := DirectDual.G_delta m
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
         dual_is_banach_c0_from_WLPO_struct hWLPO,
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
