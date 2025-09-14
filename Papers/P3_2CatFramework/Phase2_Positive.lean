/-
  Papers/P3_2CatFramework/Phase2_Positive.lean
  Positive uniformization (Part II): uniformization + fiber non-emptiness.
  Strengthens the gap result to "height = 1" in the positive sense.
-/
import Papers.P3_2CatFramework.Phase2_UniformHeight
import Papers.P3_2CatFramework.Phase2_API

namespace Papers.P3.Phase2Positive

open Papers.P3.Phase1Simple
open Papers.P3.Phase2
open Papers.P3.Phase2API

/-! ## Helper lemmas for Truth -/

@[simp] lemma nonempty_Truth_true : Nonempty (Truth true) := ⟨⟨⟩⟩

@[simp] lemma nonempty_Truth_false : Nonempty (Truth false) ↔ False := by
  simp [Truth_false]

/-- Helper: `Truth b` is nonempty iff `b = true`. -/
@[simp] lemma nonempty_Truth_iff {b : Bool} : Nonempty (Truth b) ↔ b = true := by
  cases b
  · simp [nonempty_Truth_false]
  · simp [nonempty_Truth_true]

/-! ## Definition: Positive uniformization -/

/-- Positive uniformization = uniformization + fiber non-emptiness. -/
def PosUniformizableOn (W : Phase2.Foundation → Prop) (WF : WitnessFamily) : Prop :=
  ∃ (_ : UniformizableOn W WF),
    ∀ {F} (_ : W F) (X : Sigma0), Nonempty (WF.C F X)

@[simp] theorem PosUniformizableOn.uniformizable {W WF} :
  PosUniformizableOn W WF → Nonempty (UniformizableOn W WF) :=
by rintro ⟨U, _⟩; exact ⟨U⟩

/-- Positive height on the 0/1 levels (mirrors `HeightAt`). -/
noncomputable def PosHeightAt (WF : WitnessFamily) : Option Level := by
  classical
  exact 
    if PosUniformizableOn W_ge0 WF then some Level.zero
    else if PosUniformizableOn W_ge1 WF then some Level.one
    else none

/-! ## Gap strengthened results -/

/-- No positive uniformization at level 0 follows from the old no-uniformization. -/
lemma no_pos_uniformization_height0 :
  ¬ PosUniformizableOn W_ge0 GapFamily :=
by
  intro h
  exact no_uniformization_height0 (PosUniformizableOn.uniformizable h)

/-- Positive uniformization at level 1 for the gap. -/
lemma pos_uniformization_height1 :
  PosUniformizableOn W_ge1 GapFamily :=
by
  refine ⟨uniformization_height1, ?_⟩
  intro F hF X
  -- All non-ℓ∞ fibers are `PUnit`.
  -- At ℓ∞, the fiber is `Truth (hasWLPO F)`; with `hF : hasWLPO F = true` it's nonempty.
  cases X <;> try exact ⟨⟨⟩⟩
  case ellInf =>
    -- `GapFamily.C F Sigma0.ellInf = Truth (hasWLPO F)`
    -- `hF : hasWLPO F = true`
    simp only [GapFamily_at_ellInf]
    rw [hF]
    exact nonempty_Truth_true

/-- The gap has positive height = 1. -/
theorem pos_gap_height_eq_one :
  PosHeightAt GapFamily = some Level.one :=
by
  simp only [PosHeightAt]
  have h0 : ¬ PosUniformizableOn W_ge0 GapFamily := no_pos_uniformization_height0
  have h1 : PosUniformizableOn W_ge1 GapFamily := pos_uniformization_height1
  simp only [h0, if_false, h1, if_true]

/-! ## Convenience -/

/-- Positivity implies regular uniformization. -/
@[simp] theorem pos_implies_regular {W WF} :
  PosUniformizableOn W WF → Nonempty (UniformizableOn W WF) :=
PosUniformizableOn.uniformizable

@[simp] lemma PosHeightAt_gap :
  PosHeightAt GapFamily = some Level.one :=
pos_gap_height_eq_one

end Papers.P3.Phase2Positive