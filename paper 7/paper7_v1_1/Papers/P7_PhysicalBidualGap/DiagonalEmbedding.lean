/-
Papers/P7_PhysicalBidualGap/DiagonalEmbedding.lean
Module 3 (Lemma C): Abstract interface for S₁(H) containing ℓ¹.

We axiomatize the existence of a separable Banach space X (witness: S₁(ℓ²(ℕ)),
the trace-class operators) containing ℓ¹ as a closed isometric subspace via
diagonal embedding ι(λ) = Σ λₙ |eₙ⟩⟨eₙ|.

Option A (abstract) is used: avoids building Schatten class infrastructure
(not in Mathlib, would be 1000+ lines).
-/
import Mathlib.Analysis.Normed.Lp.lpSpace
import Papers.P7_PhysicalBidualGap.Basic

noncomputable section
namespace Papers.P7

/-- ℓ¹(ℕ, ℝ) as an lp space. -/
abbrev ell1 : Type := lp (fun _ : ℕ => ℝ) 1

/-- Abstract interface for a separable Banach space containing ℓ¹ isometrically
    as a closed subspace. The canonical witness is S₁(ℓ²(ℕ)), the trace-class
    operators on a separable Hilbert space, with ι being the diagonal embedding
    ι(λ) = Σ λₙ |eₙ⟩⟨eₙ|. -/
class HasTraceClassContainer where
  /-- The ambient Banach space (e.g., S₁(ℓ²(ℕ))). -/
  X : Type
  [instNAG : NormedAddCommGroup X]
  [instNS : NormedSpace ℝ X]
  [instCS : CompleteSpace X]
  [instSep : TopologicalSpace.SeparableSpace X]
  /-- The isometric embedding ℓ¹ ↪ X. -/
  ι : ell1 →L[ℝ] X
  /-- ι is an isometry. -/
  ι_isometry : Isometry ι
  /-- The range of ι is closed in X. -/
  ι_closedRange : IsClosed (Set.range ι)

-- Make typeclass fields available as instances
attribute [instance] HasTraceClassContainer.instNAG
attribute [instance] HasTraceClassContainer.instNS
attribute [instance] HasTraceClassContainer.instCS
attribute [instance] HasTraceClassContainer.instSep

end Papers.P7
