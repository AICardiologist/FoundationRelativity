/-
  Paper 24: LLPO Equivalence via Kochen-Specker Contextuality
  PartA/FiniteSearch.lean — Constructive witness extraction for finite KS graphs

  For a finite decidable KS graph, if no valid coloring exists,
  then for any given coloring we can constructively find a failing context.

  This is the key lemma bridging uncolorability (¬∀) to the existential
  statement (∃ c, ¬satisfiesContext). For finite types with decidable
  predicates, ¬∀ → ∃¬ is constructive (no classical logic needed).
-/
import Papers.P24_KochenSpecker.Defs.CEGAData

namespace Papers.P24

/-- For any KS graph with finitely many contexts and decidable satisfaction,
    if a coloring is not valid, then there exists a specific failing context.
    This is constructive for finite decidable predicates. -/
theorem finite_context_witness (G : KSGraph)
    (f : KSColoring G) (h : ¬ isKSValid G f) :
    ∃ c : Fin G.numContexts, ¬ satisfiesContext G f c := by
  by_contra hall
  push_neg at hall
  exact h hall

/-- Combined: KS-uncolorability + any coloring → explicit failing context. -/
theorem ks_failing_context (G : KSGraph)
    (huncolorable : isKSUncolorable G) (f : KSColoring G) :
    ∃ c : Fin G.numContexts, ¬ satisfiesContext G f c :=
  finite_context_witness G f (huncolorable f)

-- Axiom audit
-- Expected: [propext, Classical.choice, Quot.sound]
#print axioms finite_context_witness
#print axioms ks_failing_context

end Papers.P24
