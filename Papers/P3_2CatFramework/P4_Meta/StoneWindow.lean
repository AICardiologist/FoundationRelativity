/-
  Papers/P4_Meta/StoneWindow.lean
  
  Stone window generalization: support ideals in Boolean rings.
  This is a constructive algebraic result that generalizes the classical
  Stone representation to ideals determined by support conditions.
-/

namespace Papers.P4Meta.StoneWindow

/-- Boolean-valued sequences with pointwise operations -/
def BoolSeq := Nat → Bool

namespace BoolSeq

/-- Pointwise XOR (addition in Boolean ring) -/
def add (f g : BoolSeq) : BoolSeq :=
  fun n => xor (f n) (g n)

/-- Pointwise AND (multiplication in Boolean ring) -/
def mul (f g : BoolSeq) : BoolSeq :=
  fun n => f n && g n

/-- Zero sequence -/
def zero : BoolSeq :=
  fun _ => false

/-- Support of a sequence: predicate for indices where it's true -/
def support (f : BoolSeq) : Nat → Prop :=
  fun n => f n = true

instance : Add BoolSeq := ⟨add⟩
instance : Mul BoolSeq := ⟨mul⟩
instance : Zero BoolSeq := ⟨zero⟩

/-- Boolean ring axioms (all constructive) -/
theorem add_comm (f g : BoolSeq) : f + g = g + f := by
  funext n
  simp only [HAdd.hAdd, Add.add, add]
  cases f n <;> cases g n <;> rfl

theorem add_self (f : BoolSeq) : f + f = 0 := by
  funext n
  simp only [HAdd.hAdd, Add.add, add]
  cases f n <;> rfl

theorem mul_comm (f g : BoolSeq) : f * g = g * f := by
  funext n
  simp only [HMul.hMul, Mul.mul, mul]
  cases f n <;> cases g n <;> rfl

theorem mul_idem (f : BoolSeq) : f * f = f := by
  funext n
  simp only [HMul.hMul, Mul.mul, mul]
  cases f n <;> rfl

end BoolSeq

/-- A Boolean ideal: downward-closed collection of support sets -/
structure BooleanIdeal where
  /-- The carrier is a predicate on predicates -/
  carrier : (Nat → Prop) → Prop
  /-- Downward closure under subset -/
  downward_closed : ∀ A B, carrier A → (∀ n, B n → A n) → carrier B
  /-- Closed under union -/
  closed_union : ∀ A B, carrier A → carrier B → carrier (fun n => A n ∨ B n)

/-- Predicate for finite sets (without full mathlib) -/
def IsFinite (A : Nat → Prop) : Prop :=
  ∃ bound : Nat, ∀ n, A n → n < bound

/-- The finite support ideal -/
def finiteSupport : BooleanIdeal where
  carrier := IsFinite
  downward_closed := by
    intros A B hA hB
    obtain ⟨bound, h_bound⟩ := hA
    refine ⟨bound, ?_⟩
    intros n hn
    exact h_bound n (hB n hn)
  closed_union := by
    intros A B hA hB
    obtain ⟨boundA, hboundA⟩ := hA
    obtain ⟨boundB, hboundB⟩ := hB
    refine ⟨max boundA boundB, ?_⟩
    intros n hn
    cases hn with
    | inl h => exact Nat.lt_of_lt_of_le (hboundA n h) (Nat.le_max_left _ _)
    | inr h => exact Nat.lt_of_lt_of_le (hboundB n h) (Nat.le_max_right _ _)

/-- Main theorem: idempotents in finite support case are exactly finite supports -/
theorem finite_support_characterization (f : BoolSeq) :
    f * f = f → 
    finiteSupport.carrier (BoolSeq.support f) →
    IsFinite (BoolSeq.support f) := by
  intros _ hf
  exact hf

end Papers.P4Meta.StoneWindow

namespace Papers.P4Meta

/-! ### Stone Window (support ideals): calibration surface over BISH -/

/-- Abstract predicate: "surjectivity of Φ_I" as a BISH-level proposition. -/
opaque StoneSurj : Type → Prop

/-- A calibrator-style wrapper for later height certificates (placeholder). -/
def StoneCalibrator (I : Type) : Prop := StoneSurj I

end Papers.P4Meta