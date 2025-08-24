/-
  Papers/P4_Meta/Meta_Signature.lean
  Schematic signature for meta-theoretic reasoning (sorry-free).
-/
namespace Papers.P4Meta

/-- Toy formula language: just atoms indexed by Nat. -/
inductive Formula where
  | atom : Nat → Formula
deriving DecidableEq, Repr

/-- A "theory" is just a predicate of provable formulas. -/
structure Theory where
  Provable : Formula → Prop

namespace Theory

/-- Extend a theory by adding a single axiom `φ`. -/
def Extend (T : Theory) (φ : Formula) : Theory :=
  { Provable := fun ψ => T.Provable ψ ∨ ψ = φ }

/-- In the extension, `φ` is provable by construction. -/
@[simp] theorem Extend_Proves {T : Theory} {φ : Formula} :
    (Extend T φ).Provable φ := Or.inr rfl

/-- Monotonicity: everything provable in `T` remains provable in `Extend T φ`. -/
@[simp] theorem Extend_mono {T : Theory} {φ ψ : Formula} (h : T.Provable ψ) :
    (Extend T φ).Provable ψ := Or.inl h

end Theory

/-- A placeholder "Paper 3" theory; for the skeleton we let everything be provable. -/
def Paper3Theory : Theory :=
  { Provable := fun _ => True }

/-- A placeholder "ClassicalLogic" theory; same as above at this abstraction level. -/
def ClassicalLogic : Theory :=
  { Provable := fun _ => True }

export Theory (Extend Extend_Proves Extend_mono)

end Papers.P4Meta