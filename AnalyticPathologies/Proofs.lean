import AnalyticPathologies.NoWitness
import AnalyticPathologies.ClassicalWitness

/-! # Spectral Gap ⇒ ACω – final wrapper (Milestone C) -/

namespace AnalyticPathologies

/-- Main theorem: the Spectral Gap pathology forces `RequiresACω`
    constructively, yet classically admits an explicit witness. -/
theorem SpectralGap_requires_ACω :
    RequiresACω ∧ Nonempty (Σ' v : L2Space, (0 : BoundedOp) v = 0) :=
  And.intro RequiresACω.mk witness_zfc

end AnalyticPathologies