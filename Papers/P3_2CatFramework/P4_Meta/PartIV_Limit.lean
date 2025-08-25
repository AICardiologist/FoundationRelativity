/-
  Papers/P3_2CatFramework/P4_Meta/PartIV_Limit.lean
  
  ω-limit scaffolding for instancewise and universal provability.
  Provides tools for stating that "at ω we have all instances" cleanly.
-/
import Papers.P3_2CatFramework.P4_Meta.Meta_Signature
import Papers.P3_2CatFramework.P4_Meta.PartIII_Certificates
import Papers.P3_2CatFramework.P4_Meta.PartIII_ProductSup
import Papers.P3_2CatFramework.P4_Meta.PartIII_Concat

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

/-- Push a pair certificate to the ω-limit: both goals hold in `Extendω`. -/
def pairToOmega
  {T : Theory} {step : Nat → Formula}
  {g : PairGoal}
  (c : HeightCertificatePair T step g) :
  (Extendω T step).Provable g.φ ∧ (Extendω T step).Provable g.ψ :=
⟨⟨c.n, c.upper_left⟩, ⟨c.n, c.upper_right⟩⟩

/-- From a prefix certificate `i ≤ k`, conclude the ω‑limit provability on
    the concatenated ladder. -/
theorem omega_of_prefixCert
  {T : Theory} {A B : Nat → Formula} {φ : Formula}
  (k : Nat) (cA : HeightCertificate T A φ) (hAk : cA.n ≤ k) :
  (Extendω T (concatSteps k A B)).Provable φ :=
by
  -- Lift into the concatenation at the same finite stage, then go to ω.
  let cA' := prefixLiftCert (T := T) (A := A) (B := B) k cA hAk
  exact certToOmega cA'

/-- From a tail certificate over `ExtendIter T A k`, conclude the ω‑limit
    provability on the concatenated ladder. -/
theorem omega_of_tailCert
  {T : Theory} {A B : Nat → Formula} {ψ : Formula}
  (k : Nat) (cB : HeightCertificate (ExtendIter T A k) B ψ) :
  (Extendω T (concatSteps k A B)).Provable ψ :=
by
  -- Shift the tail to the concatenation at stage `k + cB.n`, then go to ω.
  let cB' := tailLiftCert (T := T) (A := A) (B := B) k cB
  exact certToOmega cB'

/-- Compose prefix+tail into a pair on the concatenation and push both parts to ω. -/
theorem omega_of_concat_pair
  {T : Theory} {A B : Nat → Formula} {φ ψ : Formula}
  (k : Nat)
  (cA : HeightCertificate T A φ) (hAk : cA.n ≤ k)
  (cB : HeightCertificate (ExtendIter T A k) B ψ) :
  (Extendω T (concatSteps k A B)).Provable φ ∧
  (Extendω T (concatSteps k A B)).Provable ψ :=
by
  -- Build the pair at finite stage…
  let p := concatPairCert (T := T) (A := A) (B := B) k cA hAk cB
  -- …and push it to ω.
  simpa using pairToOmega p

/-- Push a list of certificates to the ω-limit in one shot. -/
def certsToOmega
  {T : Theory} {step : Nat → Formula}
  (cs : List (Σ φ, HeightCertificate T step φ)) :
  List (PSigma fun φ => (Extendω T step).Provable φ) :=
cs.map (fun ⟨φ, c⟩ => PSigma.mk φ (certToOmega c))

/-- By definition, `ω`-provability is "provable at some finite stage". -/
@[simp] theorem Extendω_Provable_iff
  {T : Theory} {step : Nat → Formula} {ψ : Formula} :
  (Extendω T step).Provable ψ ↔ ∃ n, (ExtendIter T step n).Provable ψ :=
Iff.rfl

/-- `Extendω` is invariant under global, pointwise equality of step functions. -/
theorem Extendω_provable_congr
  {T : Theory} {A B : Nat → Formula} (h : ∀ i, A i = B i) (ψ : Formula) :
  (Extendω T A).Provable ψ ↔ (Extendω T B).Provable ψ := by
  constructor <;> intro hω
  · rcases hω with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hagree : ∀ i, i < n → A i = B i := fun i _ => h i
    have hstage := ExtendIter_congr (T := T) (A := A) (B := B) n hagree
    rw [← hstage]
    exact hn
  · rcases hω with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hagree : ∀ i, i < n → B i = A i := fun i _ => (h i).symm
    have hstage := ExtendIter_congr (T := T) (A := B) (B := A) n hagree
    rw [← hstage]
    exact hn

/-! ### Tiny order layer on theories -/

/-- `T ≤ᵀ U` means: every `T`-provable sentence is `U`-provable. -/
def theoryLE (T U : Theory) : Prop :=
  ∀ ψ, T.Provable ψ → U.Provable ψ

infix:50 " ≤ᵀ " => theoryLE

@[simp] theorem theoryLE_refl (T : Theory) : T ≤ᵀ T := by
  intro ψ h; exact h

theorem theoryLE_trans {T U V : Theory}
  (h₁ : T ≤ᵀ U) (h₂ : U ≤ᵀ V) : T ≤ᵀ V := by
  intro ψ h; exact h₂ ψ (h₁ ψ h)

/-- Monotonicity along the finite chain of stages. -/
theorem ExtendIter_le_of_le
  {T : Theory} {step : Nat → Formula} {i j : Nat} (hij : i ≤ j) :
  ExtendIter T step i ≤ᵀ ExtendIter T step j := by
  intro ψ h; exact ExtendIter_le_mono (T := T) (step := step) hij h

/-- Each finite stage embeds into the ω-limit. -/
theorem stage_le_omega {T : Theory} {step : Nat → Formula} (n : Nat) :
  ExtendIter T step n ≤ᵀ Extendω T step := by
  intro ψ h; exact ⟨n, h⟩

/-- `Extendω T step` is the least upper bound of the chain of finite stages. -/
theorem Extendω_is_lub
  {T : Theory} {step : Nat → Formula} {U : Theory}
  (hU : ∀ n, ExtendIter T step n ≤ᵀ U) :
  Extendω T step ≤ᵀ U := by
  intro ψ hω
  rcases hω with ⟨n, hn⟩
  exact hU n ψ hn

end Papers.P4Meta