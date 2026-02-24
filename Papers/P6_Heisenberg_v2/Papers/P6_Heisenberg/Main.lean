/-
Papers/P6_Heisenberg/Main.lean
Paper 6 v2: Aggregator and axiom audit.

Imports all modules and provides #print axioms smoke tests.
-/
import Papers.P6_Heisenberg.RobertsonSchrodinger
import Papers.P6_Heisenberg.MeasurementUncertainty

namespace Papers.P6_Heisenberg

-- ========================================================================
-- Axiom audit
-- ========================================================================

#print axioms robertson_schrodinger
#print axioms schrodinger
#print axioms measurement_uncertainty_requires_dcω

-- Output:
--   robertson_schrodinger: [propext, Classical.choice, Quot.sound]
--   schrodinger:           [propext, Classical.choice, Quot.sound]
--   measurement_uncertainty_requires_dcω: does not depend on any axioms
--
-- Note: Classical.choice appears because Mathlib's InnerProductSpace and
-- ContinuousLinearMap.adjoint infrastructure transitively uses it (Riesz
-- representation theorem, norm completions, etc.). This is a Mathlib
-- implementation artifact — the mathematical content of the proofs is
-- constructive (Cauchy-Schwarz + algebraic identities). No custom axioms
-- are introduced. All mathematical prerequisites come from Mathlib.
--
-- The key verification: zero `sorry`, zero custom axioms, zero `Axiom` declarations.
-- Everything is proved from Mathlib's InnerProductSpace API.

end Papers.P6_Heisenberg
