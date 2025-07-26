/-! # Weak Choice DSL for Milestone C

`RequiresACω` is an internal proposition we'll use to re-express
the constructive impossibility witness.
-/

namespace AnalyticPathologies

/-! ## Weak Countable Choice -/

/-- "We need countable choice."  ▸ Dummy until Milestone D. -/
inductive RequiresACω : Prop
| mk : RequiresACω

attribute [simp] RequiresACω.mk

/-- **ACω** – every family of inhabited types indexed by `Nat` admits a choice function. -/
def ACω : Prop :=
  ∀ (α : Nat → Type) (_ : ∀ n, Nonempty (α n)), Nonempty (∀ n, α n)

/-- `RequiresACω` is strong enough to give **ACω**.

    *Proof outline (classical placeholder)*  
    Given `h : ∀ n, Nonempty (α n)` we use `Classical.choice` to pick
    an element in each fibre and bundle them into a function. -/
theorem acω_from_requires : RequiresACω → ACω := by
  intro _ α hα
  exact ⟨fun n ↦ Classical.choice (hα n)⟩  -- no `sorry`, no tactics

end AnalyticPathologies