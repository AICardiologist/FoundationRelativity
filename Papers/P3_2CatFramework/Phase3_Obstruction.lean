/-
  Papers/P3_2CatFramework/Phase3_Obstruction.lean
  Generic no-uniformization lemma at pinned Σ₀ object.
-/
import Papers.P3_2CatFramework.Phase2_UniformHeight
import Mathlib.Logic.Equiv.Basic

namespace Papers.P3.Phase3

open Papers.P3.Phase1Simple

/-- If at some pinned X we can *prove* there is no equivalence across Φ, then uniformization fails. -/
theorem no_uniformization_at_pinned
  {WF : Papers.P3.Phase2.WitnessFamily} {W : Papers.P3.Phase1Simple.Foundation → Prop}
  {F F' : Papers.P3.Phase1Simple.Foundation} (Φ : Papers.P3.Phase1Simple.Interp F F') (hF : W F) (hF' : W F')
  (X : Papers.P3.Phase2.Sigma0)
  (h : ¬ Nonempty ((WF.C F X) ≃ (WF.C F' X))) :
  ¬ Nonempty (Papers.P3.Phase2.UniformizableOn W WF) := by
  intro ⟨U⟩
  have e : (WF.C F X) ≃ (WF.C F' X) := U.η Φ hF hF' X
  exact h ⟨e⟩

/-- Specialization: the gap at ℓ∞ kills uniformization at level 0. -/
theorem gap_obstructs_at_zero :
  ¬ Nonempty (Papers.P3.Phase2.UniformizableOn Papers.P3.Phase2.W_ge0 Papers.P3.Phase2.GapFamily) := by
  -- Pick Φ : BISH → BISH+WLPO and X = ℓ∞
  have h : ¬ Nonempty (Papers.P3.Phase2.Truth (Papers.P3.Phase1Simple.BISH.wlpo) ≃ Papers.P3.Phase2.Truth (Papers.P3.Phase1Simple.BISH_WLPO.wlpo)) := by
    intro ⟨e⟩
    -- Left is Empty, right is PUnit (Phase 2 facts)
    have : Empty := (e.symm ⟨⟩)
    cases this
  exact no_uniformization_at_pinned (Φ := Papers.P3.Phase2.inclusionBW)
    (F := Papers.P3.Phase1Simple.BISH) (F' := Papers.P3.Phase1Simple.BISH_WLPO) (hF := trivial) (hF' := trivial)
    (X := Papers.P3.Phase2.Sigma0.ellInf) h

end Papers.P3.Phase3