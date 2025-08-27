/-
  File: Papers/P3_2CatFramework/P4_Meta/StoneWindow_SupportIdeals.lean
  
  Purpose: WP-D Stone Window for Support Ideals
  - Generalizes Stone window beyond Fin to arbitrary Boolean ideals
  - Parameterized by rings with only trivial idempotents
  - Algebraic proof without topology or choice
-/

namespace Papers.P4Meta

section SupportIdeals

variable {R : Type*} [Semiring R]

/-- 'Only trivial idempotents' for R (holds for integral domains). -/
class TwoIdempotents (R : Type*) [Semiring R] : Prop where
  idemp_trivial : ∀ x : R, x * x = x → x = 0 ∨ x = 1

/-- Functions ℕ → R with pointwise operations (our ℓ∞). -/
abbrev Linf {R : Type*} [Semiring R] := ℕ → R

variable [Zero R] [One R]

/-- Characteristic function. -/
def chi (A : Set ℕ) : @Linf R _ := fun n => if n ∈ A then (1 : R) else 0

/-- Support. -/
def supp (x : @Linf R _) : Set ℕ := {n | x n ≠ 0}

/-- Boolean ideals on ℕ. -/
structure BoolIdeal : Type where
  mem          : Set (Set ℕ)
  nonempty     : ∃ S, S ∈ mem
  downward     : ∀ {A B}, B ⊆ A → A ∈ mem → B ∈ mem
  union_closed : ∀ {A B}, A ∈ mem → B ∈ mem → A ∪ B ∈ mem

variable (𝓘 : BoolIdeal)

/-- Support ideal in ℓ∞: functions whose support is in 𝓘. -/
def I_support : Set (@Linf R _) := {x | supp x ∈ 𝓘.mem}

/-- Symmetric-difference modulo 𝓘. -/
def sdiff_equiv (A B : Set ℕ) : Prop := (A \ B) ∪ (B \ A) ∈ 𝓘.mem

-- (Next steps: quotient of sets mod 𝓘; quotient of Linf by I_support; define Φ_𝓘 and prove the isomorphism.)

end SupportIdeals

/-! ### Calibration Program

The constructive principles needed for surjectivity of Φ_I depend on I:
- For FinIdeal: constructively provable (no extra axioms)
- For DensityZeroIdeal: requires principles related to WLPO
- For other ideals: calibrate case by case

This provides a flexible testbed for measuring constructive strength.
-/

end Papers.P4Meta