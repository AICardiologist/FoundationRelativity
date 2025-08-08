/-
  Papers/P2_BidualGap/Compat/NonReflexive.lean

  Compatibility layer for non-reflexive witnesses in the *weak* sense:
  It does NOT encode the constructive dual-Banach assumptions. We keep it
  as a utility for classical tests, but it is not used in the BISH equivalence.
-/
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Group.Completeness
import Papers.P2_BidualGap.Basic

namespace Papers.P2.Compat
open Papers.P2

/-- A *weak* non-reflexive witness over `𝕂` — classical notion. -/
def NonReflexiveWitness (𝕂 : Type*) [NontriviallyNormedField 𝕂] : Prop :=
  ∃ (X : Type*) (_ : NormedAddCommGroup X) (_ : NormedSpace 𝕂 X) (_ : CompleteSpace X),
    ¬ Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕂 X)

/-- (For classical sanity checks) package a real witness as the weak gap prop. -/
lemma witness_to_BidualGapWeak (h : NonReflexiveWitness ℝ) : True := by
  -- NOTE: We return `True` to make it unusable in the strong equivalence.
  -- If needed, one can repack `h` to the old weak `∃ X, ¬ surj(j)` shape,
  -- but that is intentionally decoupled from the strong BISH equivalence.
  trivial

/-- (Stub) Placeholder for a concrete weak witness; not used in BidualGapStrong. -/
lemma c0_or_l1_witness_weak : NonReflexiveWitness ℝ := by
  -- TODO: Fill with c₀ or ℓ¹ classical witness if/when we want a separate
  --       classical regression test. This is NOT part of the BISH equivalence.
  sorry -- SORRY(P2-c0-or-l1-weak)

end Papers.P2.Compat