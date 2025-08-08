/-
  Papers/P2_BidualGap/Constructive/Ishihara.lean
  Constructive skeleton for Ishihara's argument (BidualGapStrong → WLPO).

  We do NOT open classical or use by_cases here.
-/
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Group.Completeness
import Papers.P2_BidualGap.Basic

namespace Papers.P2.Constructive
open Papers.P2

/-- Data needed to run Ishihara's trick on some Banach space `X`:
    we require constructive-Banach behavior of the dual to ensure
    sums of normable functionals are normable (i.e., the "norm" exists). -/
structure IshiharaKernel
  (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] : Prop where
  (dual_is_banach : DualIsBanach X)
  (f : X →L[ℝ] ℝ)
  (g : (ℕ → Bool) → (X →L[ℝ] ℝ))
  (f_normable : HasOperatorNorm f)
  (g_normable : ∀ α, HasOperatorNorm (g α))
  /- Separation of the sum's norm allows WLPO-decoding for any α. We only
     encode the *conclusion shape* needed; the concrete construction will follow
     the standard l¹-style design (f = Σ x_k, gα = Σ (2α(k)-1) x_k). -/
  (sum_normable : ∀ α, HasOperatorNorm (f + g α))
  (separation :
    ∃ (δ : ℝ), 0 < δ ∧
      ∀ α, ((∀ n, α n = false) → ‖f + g α‖ = 0) ∧ (¬ (∀ n, α n = false) → δ ≤ ‖f + g α‖))

/-- (Stub) From an Ishihara kernel we can decide WLPO. -/
theorem WLPO_of_kernel
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] :
  IshiharaKernel X → WLPO := by
  -- TODO(P2-Ishihara-forward):
  --   Use the separation property: compare ‖f + g α‖ against δ to decide WLPO.
  sorry

end Papers.P2.Constructive