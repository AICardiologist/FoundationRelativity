/-! # Weak Choice DSL for Milestone C

`RequiresACω` is an internal proposition we'll use to re-express
the constructive impossibility witness.
-/

namespace SpectralGap

/-! ## Weak Countable Choice -/

/-- "We need countable choice."  ▸ Dummy until Milestone D. -/
inductive RequiresACω : Prop
| mk : RequiresACω

attribute [simp] RequiresACω.mk

/-- **ACω** – every family of inhabited types indexed by `Nat` admits a choice function. -/
def ACω : Prop :=
  ∀ (α : Nat → Type) (_ : ∀ n, Nonempty (α n)), Nonempty (∀ n, α n)

/-- `RequiresACω` is strong enough to give **ACω** (placeholder proof). -/
theorem acω_from_requires : RequiresACω → ACω := by
  intro _
  intro α hα
  -- Placeholder: in the final proof we'll unpack RequiresACω
  sorry

end SpectralGap