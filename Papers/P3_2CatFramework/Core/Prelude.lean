import Papers.P3_2CatFramework.Core.UniverseLevels
import Papers.P3_2CatFramework.Core.FoundationBasic
import Papers.P3_2CatFramework.Core.Coherence
import Papers.P3_2CatFramework.Core.CoherenceTwoCellSimp
-- Removed: import CategoryTheory.WitnessGroupoid.Core (doesn't exist yet)

-- Foundation, Interp, and GapWitness are available directly from FoundationBasic
-- GenericWitness will be available from WitnessGroupoid.Core in Phase 3+

-- Re-export the pattern-matchable placeholders and plumbing
export Papers.P3
  (AssocHolds UnitorHolds PentagonHolds WitnessElimination BiCatCoherence)

-- Re-export ergonomic lemmas without shadowing mathlib names:
export Papers.P3.Interp (id_vcomp vcomp_id vcomp_assoc)

-- Use: `open scoped Papers.P3` to enable ≫ᵢ and 𝟙ᵢ notation.