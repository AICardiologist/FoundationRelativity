/-
  Papers/P2_BidualGap/Constructive/Ishihara.lean
  Constructive skeleton for Ishihara's argument (BidualGap → WLPO).
-/
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Group.Completeness
import Papers.P2_BidualGap.Basic

-- Constructive kernel - no classical logic unless absolutely necessary for stubs
set_option autoImplicit false

namespace Papers.P2.Constructive

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- Data needed from a non-surjective canonical embedding `j : X → X**`. -/
structure IshiharaKernel : Type :=
  (j : X →L[ℝ] (NormedSpace.Dual ℝ (NormedSpace.Dual ℝ X)))
  (not_surj : ¬ Function.Surjective j)

/-- Given a Boolean sequence `α`, synthesize an element `x_α ∈ X`
    whose evaluation by some `x'' ∈ X** \ im(j)` carries the WLPO signal. -/
def encode (K : IshiharaKernel) (α : ℕ → Bool) : X :=
  -- TODO (Option A from the professor):
  --   * Define `x_α` as a properly convergent series in X depending on α.
  --   * Arrange that `⟪K.some_f, x_α⟫` semidecides `(∀ n, α n = false)`.
  0  -- Placeholder: will be a summable series ∑' n, (encode_weight α n) • K.x n

/-- (Stub) Forward direction: from a bidual gap kernel to WLPO. -/
noncomputable theorem WLPO_of_kernel (K : IshiharaKernel) : Papers.P2.WLPO := by
  -- TODO: Formalize Ishihara's argument using `encode`.
  intro α
  -- Let `xα := encode K α`; use `K.not_surj` to extract the WLPO disjunction.
  sorry -- SORRY(P2-Ishihara-forward)

end Papers.P2.Constructive