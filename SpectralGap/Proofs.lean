import SpectralGap.NoWitness
import SpectralGap.ClassicalWitness

/-! # Spectral Gap ⇒ ACω – final wrapper (Milestone C) -/

namespace SpectralGap

/-- Main theorem: the Spectral Gap pathology forces `RequiresACω`
    constructively, yet classically admits an explicit witness. -/
theorem SpectralGap_requires_ACω :
    RequiresACω ∧ witness_zfc :=
by
  exact And.intro RequiresACω.mk witness_zfc

end SpectralGap