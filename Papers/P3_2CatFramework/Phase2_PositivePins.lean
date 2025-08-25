/-
  Papers/P3_2CatFramework/Phase2_PositivePins.lean
  
  Pins-aware positive uniformization: restricts the non-emptiness
  requirement to a chosen set S ⊆ Σ₀, while keeping uniformization on W.
  This is a *relaxation* of the existing PosUniformizableOn.
-/
import Papers.P3_2CatFramework.Phase2_PositiveTruthAlgebra

namespace Papers.P3.Phase2Positive

open Papers.P3.Phase2
open Papers.P3.Phase2API

/-- Positivity on a chosen set of pins `S`. -/
def PosUniformizableOnPins
  (W : Foundation → Prop) (WF : WitnessFamily) (S : Set Sigma0) : Prop :=
  ∃ (U : UniformizableOn W WF),
    ∀ {F} (hF : W F) {X}, X ∈ S → Nonempty (WF.C F X)

/-- Old (all pins) notion is the special case `S = Set.univ`. -/
@[simp] lemma PosUniformizableOn_univ {W : Foundation → Prop} {WF : WitnessFamily} :
  PosUniformizableOnPins W WF Set.univ ↔ PosUniformizableOn W WF := by
  constructor
  · intro h
    rcases h with ⟨U, ne⟩
    exact ⟨U, fun {F} hF X => ne hF trivial⟩
  · intro h
    rcases h with ⟨U, ne⟩
    exact ⟨U, fun {F} hF X _ => ne hF X⟩

/-- Any all-pins positivity gives pins-aware positivity for every `S`. -/
lemma PosUniformizableOn.toPins {W : Foundation → Prop} {WF : WitnessFamily} {S : Set Sigma0} :
  PosUniformizableOn W WF → PosUniformizableOnPins W WF S := by
  intro h; rcases h with ⟨U, ne⟩
  exact ⟨U, by intro F hF X _; exact ne hF X⟩

/-- Truth-family characterization over a set of pins. -/
lemma posUL_truth_on_iff
  {W : Foundation → Prop}
  {B : Foundation → Sigma0 → Bool}
  {S : Set Sigma0} :
  PosUniformizableOnPins W (TruthFamily B) S
    ↔ (Nonempty (UniformizableOn W (TruthFamily B)) ∧
        ∀ {F} (hF : W F) {X}, X ∈ S → B F X = true) := by
  constructor
  · intro h
    rcases h with ⟨U, ne⟩
    refine ⟨⟨U⟩, ?_⟩
    intro F hF X hX
    have : Nonempty (Truth (B F X)) := ne hF hX
    simpa using (nonempty_Truth_iff (b := B F X)).1 this
  · intro h
    rcases h with ⟨⟨U⟩, htrue⟩
    refine ⟨U, ?_⟩
    intro F hF X hX
    have hb : B F X = true := htrue hF hX
    simpa [TruthFamily_C, hb, Truth_true] using
      (nonempty_Truth_true : Nonempty (Truth true))

/-- Pointwise disjunction over the chosen pins. -/
theorem pos_UL_or_pointwise_on
  (W : Foundation → Prop) (S : Set Sigma0)
  (B C : Foundation → Sigma0 → Bool) :
  PosUniformizableOnPins W (TruthFamily (fun F X => B F X || C F X)) S
    ↔ (Nonempty (UniformizableOn W (TruthFamily (fun F X => B F X || C F X))) ∧
        ∀ {F} (hF : W F) {X}, X ∈ S → (B F X = true ∨ C F X = true)) := by
  rw [posUL_truth_on_iff]
  constructor <;> intro h
  · refine ⟨h.1, ?_⟩
    intro F hF X hXS
    have := h.2 hF hXS
    cases hB : B F X <;> cases hC : C F X <;> simp [hB, hC] at this ⊢
  · refine ⟨h.1, ?_⟩
    intro F hF X hXS
    have := h.2 hF hXS
    cases this with
    | inl hB => simp [hB]
    | inr hC => simp [hC]

/-- From positivity of a conjunction on pins, you get both booleans true on `S`. -/
lemma pos_UL_and_on_elim_bool
  (W : Foundation → Prop) (S : Set Sigma0)
  (B C : Foundation → Sigma0 → Bool)
  (h : PosUniformizableOnPins W (TruthFamily (fun F X => B F X && C F X)) S) :
  ∀ {F} (hF : W F) {X}, X ∈ S → (B F X = true ∧ C F X = true) := by
  intro F hF X hXS
  have := (posUL_truth_on_iff (W := W)
              (B := fun F X => B F X && C F X) (S := S)).1 h
  simpa [and_eq_true] using this.2 hF hXS

/-! Example usage: For the Gap family, we could state positive uniformization 
    with pins at ℓ∞ only, matching the paper's refined notion:
    `PosUniformizableOnPins W_ge1 GapFamily {Sigma0.ellInf}` 
    This would reduce the non-emptiness requirement to just the ℓ∞ case. -/

end Papers.P3.Phase2Positive