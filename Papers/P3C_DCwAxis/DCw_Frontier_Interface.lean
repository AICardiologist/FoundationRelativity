/-! Paper 3C interface: DCω and an opaque Baire token. -/
namespace Papers.P3C.DCw

/-- Dependent Choice (ω), standard token. -/
def DCω : Prop :=
  ∀ {α : Type} (R : α → α → Prop),
    (∀ x : α, ∃ y : α, R x y) →
    ∀ x₀ : α, ∃ f : Nat → α, f 0 = x₀ ∧ ∀ n, R (f n) (f (n+1))

/-- Opaque token for "ℕ^ℕ is Baire". Defined abstractly in 3C-lite, bound to
    `BaireSpace (ℕ → ℕ)` in a mathlib file outside the 3A CI surface. -/
opaque BaireNN : Prop

/-- Target statement for the calibrator. -/
abbrev BaireFromDCωStatement : Prop := DCω → BaireNN

end Papers.P3C.DCw