/-
  Paper 24: LLPO Equivalence via Kochen-Specker Contextuality
  PartA/PartA_Main.lean — Summary of Part A (BISH combinatorics)

  Part A establishes two BISH results:
  1. The CEGA graph is KS-uncolorable (native_decide)
  2. For any coloring, a failing context can be constructively identified

  Both are finite computations — entirely constructive.
-/
import Papers.P24_KochenSpecker.PartA.Uncolorability
import Papers.P24_KochenSpecker.PartA.FiniteSearch

namespace Papers.P24

/-- Part A summary: the CEGA graph is KS-uncolorable, and for any
    coloring we can find a specific failing context. -/
theorem partA_summary :
    isKSUncolorable cegaGraph ∧
    (∀ f : KSColoring cegaGraph,
      ∃ c : Fin cegaGraph.numContexts, ¬ satisfiesContext cegaGraph f c) :=
  ⟨cega_uncolorable, fun f => ks_failing_context cegaGraph cega_uncolorable f⟩

-- Axiom audit
#print axioms partA_summary

end Papers.P24
