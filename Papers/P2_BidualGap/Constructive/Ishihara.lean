/-
  Papers/P2_BidualGap/Constructive/Ishihara.lean
  Constructive skeleton for Ishihara's argument (BidualGapStrong → WLPO).

  We do NOT open classical or use by_cases here.
-/
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Group.Completeness
import Papers.P2_BidualGap.Basic
import Papers.P2_BidualGap.Constructive.DualStructure

namespace Papers.P2.Constructive
open Papers.P2

/-- (Prop-level) Statement that an Ishihara kernel exists for a space X with proper separation. -/
def IshiharaKernel (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] : Prop :=
  DualIsBanach X ∧ 
  ∃ (f : X →L[ℝ] ℝ) (g : (ℕ → Bool) → (X →L[ℝ] ℝ)),
    HasOperatorNorm f ∧
    (∀ α, HasOperatorNorm (g α)) ∧
    (∀ α, HasOperatorNorm (f + g α)) ∧
    ∃ (δ : ℝ), 0 < δ ∧
      ∀ α, ((∀ n, α n = false) → ‖f + g α‖ = 0) ∧ (¬ (∀ n, α n = false) → δ ≤ ‖f + g α‖)

/-- (Stub) From an Ishihara kernel we can decide WLPO. -/
theorem WLPO_of_kernel
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] :
  IshiharaKernel X → WLPO := by
  -- TODO(P2-Ishihara-forward):
  --   Use the separation property: compare ‖f + g α‖ against δ to decide WLPO.
  sorry

/-- A *Type-level* package bundling the space and its instances together with an Ishihara kernel.
    Monomorphic on `Type` to avoid universe metavariables when transporting across files. -/
structure KernelWitness where
  X : Type
  instGroup : NormedAddCommGroup X
  instSpace : NormedSpace ℝ X
  instComplete : CompleteSpace X
  K : @IshiharaKernel X instGroup instSpace instComplete

/-- Convenience wrapper that avoids instance synthesis/defeq issues by passing instances explicitly. -/
theorem WLPO_of_witness (W : KernelWitness) : WLPO :=
  @WLPO_of_kernel W.X W.instGroup W.instSpace W.instComplete W.K

/-- (Stub) Extract a packaged Ishihara kernel from a strong bidual gap witness.
    Returns a `KernelWitness` in `Type` rather than an existential in `Prop`,
    so universe/instance resolution is straightforward for callers. -/
def kernel_from_gap : BidualGapStrong → KernelWitness := by
  -- TODO(P2-kernel-from-gap):
  --   Unpack `BidualGapStrong`:
  --     ⟨X, insts…, dualIsBanachX, dualIsBanachX**, notSurj⟩
  --   Build the kernel data (f, g, δ, separation).
  --   Return `⟨X, _, _, _, kernel⟩`.
  sorry

end Papers.P2.Constructive