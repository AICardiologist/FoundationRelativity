/-
  Papers/P3_2CatFramework/P4_Meta/PartIV_Limit.lean
  
  ω-limit scaffolding for instancewise and universal provability.
  Provides tools for stating that "at ω we have all instances" cleanly.
-/
import Papers.P3_2CatFramework.P4_Meta.Meta_Signature
import Papers.P3_2CatFramework.P4_Meta.PartIII_Certificates

namespace Papers.P4Meta

open Papers.P4Meta

/-- ω-limit theory: `ψ` is provable iff it's provable at *some* finite stage. -/
def Extendω (T : Theory) (step : Nat → Formula) : Theory :=
{ Provable := fun ψ => ∃ n, (ExtendIter T step n).Provable ψ }

@[simp] theorem Extendω_of_stage {T : Theory} {step : Nat → Formula} {n : Nat} {ψ : Formula} :
  (ExtendIter T step n).Provable ψ → (Extendω T step).Provable ψ := fun h => ⟨n, h⟩

/-- Instancewise reflection at ω (schematic): if each instance `ϕ n` is
    provable at some finite stage (maybe depending on `n`), then all those
    instances are provable in the ω-limit theory. -/
theorem limit_has_instances
  (T : Theory) (step : Nat → Formula) (ϕ : Nat → Formula)
  (H : ∀ n, ∃ k, (ExtendIter T step k).Provable (ϕ n)) :
  ∀ n, (Extendω T step).Provable (ϕ n) := by
  intro n
  rcases H n with ⟨k, hk⟩
  exact Extendω_of_stage (T := T) (step := step) hk

/-- Any finite-stage certificate yields an ω-stage proof (by definition). -/
def certToOmega
  {T : Theory} {step : Nat → Formula} {φ : Formula}
  (c : HeightCertificate T step φ) :
  (Extendω T step).Provable φ :=
⟨c.n, c.upper⟩

end Papers.P4Meta