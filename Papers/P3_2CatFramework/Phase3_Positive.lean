/-
  Papers/P3_2CatFramework/Phase3_Positive.lean
  Numeric API for positive uniformization + bridges to Phase 2.
-/
import Papers.P3_2CatFramework.Phase3_Levels
import Papers.P3_2CatFramework.Phase3_StoneWindowMock
import Papers.P3_2CatFramework.Phase2_Positive

namespace Papers.P3.Phase3Positive

open Papers.P3.Phase1Simple
open Papers.P3.Phase2
open Papers.P3.Phase3
open Papers.P3.Phase2Positive
open Papers.P3.Phase2API

/-! ## Numeric positive uniformization -/

/-- Positive uniformization at numeric level k. -/
def PosUniformizableOnN (k : Nat) (WF : WitnessFamily) : Prop :=
  ∃ (_ : UniformizableOnN k WF),
    ∀ {F} (_ : W_ge k F) (X : Sigma0), Nonempty (WF.C F X)

/-- Positive numeric height (0/1 implemented for now). -/
noncomputable def PosHeightAtNat (WF : WitnessFamily) : Option Nat := by
  classical
  exact
    if PosUniformizableOnN 0 WF then some 0
    else if PosUniformizableOnN 1 WF then some 1
    else none

/-! ## Bridges on {0,1} -/

@[simp] lemma pos_bridge0 (WF : WitnessFamily) :
  PosUniformizableOn W_ge0 WF ↔ PosUniformizableOnN 0 WF :=
by
  constructor
  · rintro ⟨U, ne⟩
    exact ⟨(UniformizableOn.toN0 U), by intro F _ X; exact ne (by trivial) X⟩
  · rintro ⟨U0, ne⟩
    exact ⟨(toW0 U0), by intro F _ X; exact ne (by trivial) X⟩

@[simp] lemma pos_bridge1 (WF : WitnessFamily) :
  PosUniformizableOn W_ge1 WF ↔ PosUniformizableOnN 1 WF :=
by
  constructor
  · rintro ⟨U, ne⟩
    exact ⟨(UniformizableOn.toN1 U), by intro F hF X; exact ne hF X⟩
  · rintro ⟨U1, ne⟩
    exact ⟨(toW1 U1), by intro F hF X; exact ne hF X⟩

/-- Equality of the positive height APIs on {0,1}. -/
theorem PosHeightAt_agrees_on_0_1 (WF : WitnessFamily) :
  PosHeightAt WF = (PosHeightAtNat WF).bind ofNatLevel? :=
by
  simp only [PosHeightAt, PosHeightAtNat]
  by_cases h0 : PosUniformizableOn W_ge0 WF
  · -- h0 : PosUniformizableOn W_ge0 WF
    -- So PosHeightAt WF = some Level.zero
    -- Need to show PosHeightAtNat = some 0
    have h0' : PosUniformizableOnN 0 WF := (pos_bridge0 WF).mp h0
    simp only [h0, if_true, h0', Option.bind_some, ofNatLevel?]
  · -- h0 : ¬PosUniformizableOn W_ge0 WF
    have h0' : ¬PosUniformizableOnN 0 WF := mt (pos_bridge0 WF).mpr h0
    simp only [h0, if_false, h0']
    by_cases h1 : PosUniformizableOn W_ge1 WF
    · -- h1 : PosUniformizableOn W_ge1 WF
      have h1' : PosUniformizableOnN 1 WF := (pos_bridge1 WF).mp h1
      simp only [h1, if_true, h1', Option.bind_some, ofNatLevel?]
    · -- h1 : ¬PosUniformizableOn W_ge1 WF  
      have h1' : ¬PosUniformizableOnN 1 WF := mt (pos_bridge1 WF).mpr h1
      simp only [h1, if_false, h1', Option.bind_none]

/-! ## Examples -/

/-- Gap: positive numeric height = 1. -/
theorem pos_gap_height_nat_is_one :
  PosHeightAtNat GapFamily = some 1 :=
by
  -- If there were level-0 positive uniformization numerically, we'd contradict Phase 2's 0-level negative.
  have h0neg : ¬ PosUniformizableOnN 0 GapFamily := by
    intro ⟨U0, _⟩
    have : Nonempty (UniformizableOn W_ge0 GapFamily) := ⟨toW0 U0⟩
    exact no_uniformization_height0 this
  -- Level-1 positivity is the bridged Phase 2 result.
  have h1pos : PosUniformizableOnN 1 GapFamily :=
    (pos_bridge1 _).mp pos_uniformization_height1
  simp only [PosHeightAtNat]
  simp only [h0neg, if_false, h1pos, if_true]

/-- Stone window mock: positive numeric height = 0. -/
theorem pos_stone_height_nat_is_zero :
  PosHeightAtNat StoneWindowMock = some 0 :=
by
  have h0 : PosUniformizableOnN 0 StoneWindowMock :=
    ⟨UniformizableOn.toN0 stone_uniformization_h0, by intro F _ X; exact ⟨PUnit.unit⟩⟩
  simp only [PosHeightAtNat, h0, if_true]

/-! ## Convenience aliases -/

@[simp] lemma PosHeightAtNat_gap :
  PosHeightAtNat GapFamily = some 1 :=
pos_gap_height_nat_is_one

@[simp] lemma PosHeightAtNat_stone :
  PosHeightAtNat StoneWindowMock = some 0 :=
pos_stone_height_nat_is_zero

/-! ## Always-positive example -/

/-- `StoneWindowMock`: positively uniformizable at *every* numeric level `k`. -/
@[simp] theorem stone_pos_uniform_all_k (k : Nat) :
  PosUniformizableOnN k StoneWindowMock :=
by
  -- Uniformization: the equivalence is constantly `Equiv.refl PUnit`.
  refine ⟨
    { η := by
        intro F F' _ _ _ X
        -- `StoneWindowMock.C _ _ = PUnit`
        exact Equiv.refl PUnit
      η_id := by
        intro F _ X
        rfl
      η_comp := by
        intro F G H φ ψ _ _ _ X
        -- `Equiv.refl ≫ Equiv.refl = Equiv.refl`
        rfl },
    ?_⟩
  -- Non-emptiness of each fiber:
  intro F _ X
  exact ⟨PUnit.unit⟩

end Papers.P3.Phase3Positive