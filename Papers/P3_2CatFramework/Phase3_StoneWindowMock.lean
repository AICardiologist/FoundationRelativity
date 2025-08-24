/-
  Papers/P3_2CatFramework/Phase3_StoneWindowMock.lean
  A mock Σ₀ witness family that is uniformizable at height 0.
-/
import Papers.P3_2CatFramework.Phase2_UniformHeight

namespace Papers.P3.Phase3

open Papers.P3.Phase1Simple

/-- A toy family that is constant on Σ₀, meant to mimic a natural identification. -/
def StoneWindowMock : Papers.P3.Phase2.WitnessFamily where
  C := fun _ _ => PUnit

/-- Trivial uniformization at height 0: everything is `PUnit`. -/
def stone_uniformization_h0 : Papers.P3.Phase2.UniformizableOn Papers.P3.Phase2.W_ge0 StoneWindowMock where
  η := fun _ _ _ _ => Equiv.refl _
  η_id := fun _ _ => rfl
  η_comp := fun _ _ _ _ _ _ => rfl

end Papers.P3.Phase3