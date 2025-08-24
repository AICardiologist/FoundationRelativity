/-
  Papers/P3_2CatFramework/P4_Meta/PartIV_Limit.lean
  
  ω-limit scaffolding for instancewise and universal provability.
  Provides tools for stating that "at ω we have all instances" cleanly.
-/
import Papers.P3_2CatFramework.P4_Meta.Meta_Signature

namespace Papers.P4Meta

open Papers.P4Meta

/-- Iterate single-axiom extension by a step-function `step`. -/
def ExtendIterLimit (T : Theory) (step : Nat → Formula) : Nat → Theory
| 0     => T
| (n+1) => Extend (ExtendIterLimit T step n) (step n)

/-- ω-limit theory: `ψ` is provable iff it's provable at *some* finite stage. -/
def Extendω (T : Theory) (step : Nat → Formula) : Theory :=
{ Provable := fun ψ => ∃ n, (ExtendIterLimit T step n).Provable ψ }

@[simp] theorem Extendω_of_stage {T : Theory} {step : Nat → Formula} {n : Nat} {ψ : Formula} :
  (ExtendIterLimit T step n).Provable ψ → (Extendω T step).Provable ψ := fun h => ⟨n, h⟩

/-- Instancewise reflection at ω (schematic): if each instance `ϕ n` is
    provable at some finite stage (maybe depending on `n`), then all those
    instances are provable in the ω-limit theory. -/
theorem limit_has_instances
  (T : Theory) (step : Nat → Formula) (ϕ : Nat → Formula)
  (H : ∀ n, ∃ k, (ExtendIterLimit T step k).Provable (ϕ n)) :
  ∀ n, (Extendω T step).Provable (ϕ n) := by
  intro n
  rcases H n with ⟨k, hk⟩
  exact Extendω_of_stage (T := T) (step := step) hk

end Papers.P4Meta