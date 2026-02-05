/- 
  Papers/P2_BidualGap/HB/Compat.lean
  Compatibility lemmas for transporting completeness along linear isometries.
-/
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Data.Real.Basic

namespace Papers.P2_BidualGap.HB.Compat

/-- Transfer completeness across a linear isometry equivalence. -/
theorem completeSpace_of_linearIsometryEquiv
  {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  (e : X ≃ₗᵢ[ℝ] Y) [CompleteSpace Y] : CompleteSpace X := by
  -- use the underlying isometry equivalence
  simpa using (IsometryEquiv.completeSpace (e := e.toIsometryEquiv))

end Papers.P2_BidualGap.HB.Compat
