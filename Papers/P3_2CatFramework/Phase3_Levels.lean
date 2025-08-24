/-
  Papers/P3_2CatFramework/Phase3_Levels.lean
  Numeric levels + bridges to Phase 2 (0/1).
-/
import Papers.P3_2CatFramework.Phase2_UniformHeight
import Mathlib.Logic.Equiv.Basic

namespace Papers.P3.Phase3

-- Bring Phase 1 names in (Foundation comes from here)
open Papers.P3.Phase1Simple

/-- Level k requirement on foundations. Extend beyond k = 1 in later phases. -/
def W_ge : Nat → (Foundation → Prop)
| 0 => fun _ => True
| 1 => fun F => F.wlpo = true
| _+2 => fun _ => True   -- placeholder for future levels (DC_ω, etc.)

@[simp] lemma W_ge_zero (F : Foundation) : W_ge 0 F := trivial
@[simp] lemma W_ge_one (F : Foundation) : (W_ge 1 F ↔ F.wlpo = true) := Iff.rfl

@[simp] lemma W_ge_zero_iff_true (F : Foundation) : (W_ge 0 F ↔ True) := Iff.rfl
@[simp] lemma W_ge_zero_iff_W_ge0 (F : Foundation) : W_ge 0 F ↔ Papers.P3.Phase2.W_ge0 F := Iff.rfl

@[simp] lemma W_ge_succ_succ {k} {F : Foundation} :
  W_ge (Nat.succ (Nat.succ k)) F := by simp [W_ge]

@[simp] lemma W_ge_succ {F : Foundation} :
  W_ge 1 F → W_ge 2 F := by intro; simp [W_ge]

-- Phase 2's level-1 predicate is definitionally the same as our numeric level 1.
-- (Here W_ge1 F := hasWLPO F = true and hasWLPO F is defeq F.wlpo.)
@[simp] lemma W_ge_one_iff_W_ge1 (F : Foundation) :
  W_ge 1 F ↔ Papers.P3.Phase2.W_ge1 F := by rfl

-- True from 2 upwards in the current scaffold.
lemma W_ge_mono_from_two : ∀ k F, 2 ≤ k → W_ge k F → W_ge (k+1) F := by
  intro k F hk _
  -- For k ≥ 2, both W_ge k and W_ge (k+1) are True
  cases k with
  | zero => contradiction  -- 2 ≤ 0 is false
  | succ k' =>
    cases k' with
    | zero => contradiction  -- 2 ≤ 1 is false
    | succ k'' => simp [W_ge]  -- k = k''+2, so both levels are True

/-- Uniformization at numeric level k (Σ₀-only, same packaging as Phase 2). -/
structure UniformizableOnN (k : Nat) (WF : Papers.P3.Phase2.WitnessFamily) : Type where
  η :
    ∀ {F F'} (_ : Interp F F'), W_ge k F → W_ge k F' →
      ∀ X : Papers.P3.Phase2.Sigma0, (WF.C F X) ≃ (WF.C F' X)
  η_id :
    ∀ {F} (hF : W_ge k F) X,
      η (id_interp F) hF hF X = Equiv.refl (WF.C F X)
  η_comp :
    ∀ {F G H} (φ : Interp F G) (ψ : Interp G H)
      (hF : W_ge k F) (hG : W_ge k G) (hH : W_ge k H) X,
      η (comp_interp φ ψ) hF hH X
        = (η φ hF hG X).trans (η ψ hG hH X)

/-- Bridge from Phase 2's `UniformizableOn W_ge0` and `UniformizableOn W_ge1`. -/
def UniformizableOn.toN0 {WF} :
  Papers.P3.Phase2.UniformizableOn Papers.P3.Phase2.W_ge0 WF → UniformizableOnN 0 WF :=
fun U => {
  η := fun Φ hF hF' X => U.η Φ (by trivial) (by trivial) X
  η_id := fun {F} _ X => by simpa using U.η_id (by trivial) X
  η_comp := fun {F G H} φ ψ _ _ _ X => by
    simpa using U.η_comp φ ψ (by trivial) (by trivial) (by trivial) X
}

def UniformizableOn.toN1 {WF} :
  Papers.P3.Phase2.UniformizableOn Papers.P3.Phase2.W_ge1 WF → UniformizableOnN 1 WF :=
fun U => {
  η := fun Φ hF hF' X => by
    -- W_ge 1 F means F.wlpo = true, which matches W_ge1 F
    have hF_phase2 : Papers.P3.Phase2.W_ge1 _ := hF
    have hF'_phase2 : Papers.P3.Phase2.W_ge1 _ := hF'
    exact U.η Φ hF_phase2 hF'_phase2 X
  η_id := fun {F} hF X => by
    have hF_phase2 : Papers.P3.Phase2.W_ge1 F := hF
    exact U.η_id hF_phase2 X
  η_comp := fun {F G H} φ ψ hF hG hH X => by
    have hF_phase2 : Papers.P3.Phase2.W_ge1 F := hF
    have hG_phase2 : Papers.P3.Phase2.W_ge1 G := hG
    have hH_phase2 : Papers.P3.Phase2.W_ge1 H := hH
    exact U.η_comp φ ψ hF_phase2 hG_phase2 hH_phase2 X
}

/-- Bridge back to Phase 2: numeric level 0 → W_ge0. -/
def toW0 {WF} :
    UniformizableOnN 0 WF → Papers.P3.Phase2.UniformizableOn Papers.P3.Phase2.W_ge0 WF :=
fun U => {
  η      := fun Φ _ _ X => U.η Φ (by trivial) (by trivial) X
  η_id   := fun {F} _ X   => by simpa using U.η_id (by trivial) X
  η_comp := fun {F G H} φ ψ _ _ _ X =>
    by simpa using U.η_comp φ ψ (by trivial) (by trivial) (by trivial) X
}

/-- Bridge back to Phase 2: numeric level 1 → W_ge1. -/
def toW1 {WF} :
    UniformizableOnN 1 WF → Papers.P3.Phase2.UniformizableOn Papers.P3.Phase2.W_ge1 WF :=
fun U => {
  η      := fun Φ hF hF' X => U.η Φ hF hF' X
  η_id   := fun hF X    => U.η_id hF X
  η_comp := fun φ ψ hF hG hH X =>
    U.η_comp φ ψ hF hG hH X
}

/-- Minimal "height as Nat" (0, 1, or none for now). Extend later. -/
noncomputable def HeightAtNat (WF : Papers.P3.Phase2.WitnessFamily) : Option Nat :=
  open Classical in
  if Nonempty (UniformizableOnN 0 WF) then some 0
  else if Nonempty (UniformizableOnN 1 WF) then some 1
  else none

/-- Gap bridge: same numerical height. -/
theorem gap_height_nat_is_one :
  HeightAtNat Papers.P3.Phase2.GapFamily = some 1 := by
  -- No uniformization at 0 → `if h0` branch closed
  have h0neg : ¬ Nonempty (UniformizableOnN 0 Papers.P3.Phase2.GapFamily) := by
    intro ⟨U0⟩
    -- From U0, get a W_ge0-uniformization (trivial bridge)
    -- But Phase 2 already proved no uniformization at W_ge0.
    have : Nonempty (Papers.P3.Phase2.UniformizableOn Papers.P3.Phase2.W_ge0 Papers.P3.Phase2.GapFamily) := ⟨{
      η := fun Φ _ _ X => U0.η Φ (by trivial) (by trivial) X
      η_id := fun {F} _ X => by simpa using U0.η_id (by trivial) X
      η_comp := fun {F G H} φ ψ _ _ _ X =>
        by simpa using U0.η_comp φ ψ (by trivial) (by trivial) (by trivial) X
    }⟩
    exact Papers.P3.Phase2.no_uniformization_height0 this
  -- Uniformization at 1 (Phase 2) gives the witness for `if h1`.
  have h1pos : Nonempty (UniformizableOnN 1 Papers.P3.Phase2.GapFamily) :=
    ⟨(UniformizableOn.toN1 Papers.P3.Phase2.uniformization_height1)⟩
  -- Manually unfold the definition
  unfold HeightAtNat
  -- Since we can't decide Nonempty in general, the definition uses Classical
  -- The definition becomes: if ... then some 0 else if ... then some 1 else none
  -- We know: not at 0 (h0neg) and yes at 1 (h1pos)
  -- So the result should be some 1
  simp only [h0neg, h1pos, ite_false, ite_true]

end Papers.P3.Phase3