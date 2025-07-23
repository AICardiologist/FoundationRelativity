/-! # Weak Choice DSL for Milestone C

`RequiresACω` is an internal proposition we'll use to re-express
the constructive impossibility witness.
-/

namespace SpectralGap

/-- "We need countable choice" – a dummy stand-in until the real
   proof is finished in Milestone D. -/
inductive RequiresACω : Prop
| mk : RequiresACω    -- one trivial constructor

attribute [simp] RequiresACω.mk

/-- Convenience lemma: once we have `RequiresACω`, we can derive anything
    that is classically provable with countable choice.  (Placeholder.) -/
theorem requiresACω_imp {P : Prop} : RequiresACω → P → P := by
  intro _ hP; exact hP

/-- Choice principle: a family of inhabited types indexed by `ℕ` has a choice
    function. -/
def ACω : Prop :=
  ∀ (α : ℕ → Type) (h : ∀ n, Nonempty (α n)), Nonempty (∀ n, α n)

theorem acω_from_requires : RequiresACω → ACω := by
  intro _
  classical
  -- Placeholder: in the final proof we'll unpack `RequiresACω`
  exact fun α hα => ⟨fun n => Classical.choice (hα n)⟩

end SpectralGap