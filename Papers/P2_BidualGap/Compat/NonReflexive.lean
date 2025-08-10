/-
  Papers/P2_BidualGap/Compat/NonReflexive.lean

  Compatibility layer for non-reflexive witnesses in the *weak* sense:
  It does NOT encode the constructive dual-Banach assumptions. We keep it
  as a utility for classical tests, but it is not used in the BISH equivalence.
-/
import Papers.P2_BidualGap.Basic
import Papers.P2_BidualGap.Compat.Axioms

namespace Papers.P2.Compat
open Papers.P2
open Papers.P2.Compat.Axioms

-- Re-export the definition and axiom for backward compatibility
export Papers.P2.Compat.Axioms (NonReflexiveWitness c0_or_l1_witness_weak)

/-- (For classical sanity checks) package a real witness as the weak gap prop. -/
lemma witness_to_BidualGapWeak (_ : NonReflexiveWitness ℝ) : True := by
  -- NOTE: We return `True` to make it unusable in the strong equivalence.
  -- If needed, one can repack the witness to the old weak `∃ X, ¬ surj(j)` shape,
  -- but that is intentionally decoupled from the strong BISH equivalence.
  trivial

end Papers.P2.Compat