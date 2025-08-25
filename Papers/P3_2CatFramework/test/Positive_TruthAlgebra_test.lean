/-
  Papers/P3_2CatFramework/test/Positive_TruthAlgebra_test.lean

  Sanity checks for truth-family algebra (products / conjunction).
-/
import Papers.P3_2CatFramework.Phase2_PositiveTruthAlgebra

open Papers.P3.Phase2
open Papers.P3.Phase2Positive

-- Shorthands for constant predicate families
def B_true  : Papers.P3.Phase2.Foundation → Sigma0 → Bool := fun _ _ => true
def B_false : Papers.P3.Phase2.Foundation → Sigma0 → Bool := fun _ _ => false

-- Positive UL of the always-true family at any W
example (W : Papers.P3.Phase2.Foundation → Prop) :
  PosUniformizableOn W (TruthFamily B_true) :=
  (posUL_truth_iff (W := W) (B := B_true)).2 (by intro F hF X; rfl)

-- Non‑positive UL of the always-false family at any W (simplified test)
example (W : Papers.P3.Phase2.Foundation → Prop) (hW : ∃ F, W F) :
  ¬ PosUniformizableOn W (TruthFamily B_false) := by
  intro h
  -- Extract `false = true` contradiction from the characterization
  simp only [posUL_truth_iff] at h
  -- h says that for all F with W F and all X, B_false F X = true
  -- But B_false is constantly false
  rcases hW with ⟨F, hF⟩
  have := h hF Sigma0.nat
  simp [B_false] at this

-- Conjunction law reduces to expected booleans
example (W : Papers.P3.Phase2.Foundation → Prop) :
  PosUniformizableOn W (TruthFamily (fun F X => B_true F X && B_true F X))
  ↔ (PosUniformizableOn W (TruthFamily B_true) ∧ PosUniformizableOn W (TruthFamily B_true)) := by
  exact pos_UL_and W B_true B_true

-- OR (pointwise): true || false is always true
example (W : Papers.P3.Phase2.Foundation → Prop) :
  PosUniformizableOn W (TruthFamily (fun F X => B_true F X || B_false F X)) :=
  (pos_UL_or_pointwise W B_true B_false).2
    (by intro F hF X; simp [B_true, B_false])

-- Monotonicity: B_true ⇒ (B_true || B_false)
example (W : Papers.P3.Phase2.Foundation → Prop) :
  PosUniformizableOn W (TruthFamily B_true) →
  PosUniformizableOn W (TruthFamily (fun F X => B_true F X || B_false F X)) :=
  pos_UL_mono_truth W (by intro F X; simp [B_true, B_false])

#eval "Positive_TruthAlgebra tests: OK!"