/-
  Height certificates for the schematic meta layer.
  Records an *upper bound* stage together with a proof at that stage.
-/
import Papers.P3_2CatFramework.P4_Meta.PartV_Collision
import Papers.P3_2CatFramework.P4_Meta.Meta_Ladders

namespace Papers.P4Meta
open Papers.P4Meta

/-- Iterate single-axiom extension by a step-function `step`. -/
def ExtendIter (T : Theory) (step : Nat → Formula) : Nat → Theory
| 0     => T
| (n+1) => Extend (ExtendIter T step n) (step n)

@[simp] theorem ExtendIter_zero (T : Theory) (step : Nat → Formula) :
  ExtendIter T step 0 = T := rfl

@[simp] theorem ExtendIter_succ (T : Theory) (step : Nat → Formula) (n : Nat) :
  ExtendIter T step (n+1) = Extend (ExtendIter T step n) (step n) := rfl

/-- One-step monotonicity: stage `i` ≤ stage `i+1`. -/
theorem ExtendIter_succ_mono
  (T : Theory) (step : Nat → Formula) (i : Nat) {φ : Formula} :
  (ExtendIter T step i).Provable φ →
  (ExtendIter T step (i+1)).Provable φ := by
  intro h
  -- stage (i+1) = Extend (stage i) (step i)
  simpa [ExtendIter_succ] using
    (Extend_mono (T := ExtendIter T step i) (φ := step i) (ψ := φ) h)

/-- Monotonicity in the stage index: if `i ≤ j` then proofs at `i` lift to `j`. -/
theorem ExtendIter_le_mono
  (T : Theory) (step : Nat → Formula) {i j : Nat} (hij : i ≤ j) {φ : Formula} :
  (ExtendIter T step i).Provable φ → (ExtendIter T step j).Provable φ := by
  induction hij with
  | refl =>
      intro h; simpa using h
  | @step j hij ih =>
      intro h
      exact
        (ExtendIter_succ_mono T step j)
          (ih h)

/-- A lightweight certificate: we record `n` and a proof at stage `n`. -/
structure HeightCertificate (T : Theory) (step : Nat → Formula) (φ : Formula) where
  (n     : Nat)
  (upper : (ExtendIter T step n).Provable φ)
  (note  : String := "")  -- optional provenance / pointer

/-- The RFN→Con pipeline, then anything else constant. -/
def godelSteps (T : Theory) : Nat → Formula
| 0     => Papers.P4Meta.PartV.RFN_Sigma1 T
| 1     => Papers.P4Meta.PartV.Con T
| _     => Papers.P4Meta.PartV.Con T

open Papers.P4Meta.PartV

/-- Upper bound: after 2 steps (RFN then Con) we can prove `GodelSentence T`. -/
theorem godel_upper_two
  (T : Theory) [HBL T] [RE T] [CodesProofs T] [Sigma1Sound T] :
  (ExtendIter T (godelSteps T) 2).Provable (GodelSentence T) := by
  -- Unfold two steps to match the collision theorem
  simp [ExtendIter_succ, godelSteps]
  -- Use the formal collision chain already present in Part V
  exact Papers.P4Meta.PartV.collision_chain T

/-- A height certificate for Gödel's sentence at stage `2`. -/
def godel_height2_cert
  (T : Theory) [HBL T] [RE T] [CodesProofs T] [Sigma1Sound T] :
  HeightCertificate T (godelSteps T) (GodelSentence T) :=
{ n     := 2
, upper := godel_upper_two T
, note  := "Upper bound: RFN→Con→G_T; lower bound via classical G1 lower axiom."
}

/-- Lift a certificate to a later stage `j` using `i ≤ j`. -/
def HeightCertificate.lift
  {T : Theory} {step : Nat → Formula} {φ : Formula}
  (c : HeightCertificate T step φ) (j : Nat) (h : c.n ≤ j) :
  HeightCertificate T step φ :=
{ n := j
, upper := ExtendIter_le_mono (T := T) (step := step) h c.upper
, note := c.note ++ s!", lifted to stage {j}."
}

end Papers.P4Meta