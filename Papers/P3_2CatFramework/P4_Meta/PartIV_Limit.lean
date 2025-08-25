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

  /-! ### Theory equivalence (≃ᵀ) -/

  /-- `T ≃ᵀ U` means: `T ≤ᵀ U` and `U ≤ᵀ T`. -/
  def theoryEqv (T U : Theory) : Prop := T ≤ᵀ U ∧ U ≤ᵀ T
  infix:50 " ≃ᵀ " => theoryEqv

  theorem theoryEqv_refl (T : Theory) : T ≃ᵀ T :=
    ⟨theoryLE_refl _, theoryLE_refl _⟩

  theorem theoryEqv_symm {T U : Theory} : (T ≃ᵀ U) → (U ≃ᵀ T)
  | ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩

  theorem theoryEqv_trans {T U V : Theory} :
      (T ≃ᵀ U) → (U ≃ᵀ V) → (T ≃ᵀ V)
  | ⟨TU, UT⟩, ⟨UV, VU⟩ => ⟨theoryLE_trans TU UV, theoryLE_trans VU UT⟩

  @[simp] theorem theoryEqv_iff {T U : Theory} :
      (T ≃ᵀ U) ↔ (T ≤ᵀ U ∧ U ≤ᵀ T) := Iff.rfl


  /-! ### A finite tail beyond ω: `ExtendωPlus` -/

  /-- `ExtendωPlus T step ε` captures "provable at some stage `n + ε`".
      This is the `ω + ε` stepping stone without committing to full ordinal machinery. -/
  def ExtendωPlus (T : Theory) (step : Nat → Formula) (ε : Nat) : Theory :=
  { Provable := fun ψ => ∃ n, (ExtendIter T step (n + ε)).Provable ψ }

  @[simp] theorem ExtendωPlus_Provable_iff
      {T : Theory} {step : Nat → Formula} {ε : Nat} {ψ : Formula} :
      (ExtendωPlus T step ε).Provable ψ ↔ ∃ n, (ExtendIter T step (n + ε)).Provable ψ := Iff.rfl

  /-- At `ε = 0`, `ExtendωPlus` *is* `Extendω` (definitionally). -/
  @[simp] theorem ExtendωPlus_zero
      {T : Theory} {step : Nat → Formula} :
      ExtendωPlus T step 0 = Extendω T step := rfl

  /-- Every ω‑provable sentence is ω+ε‑provable (monotone tail). -/
  theorem omega_le_omegaPlus
      {T : Theory} {step : Nat → Formula} (ε : Nat) :
      Extendω T step ≤ᵀ ExtendωPlus T step ε :=
  by
    intro ψ hω
    rcases hω with ⟨n, hn⟩
    exact ⟨n, ExtendIter_le_mono (T := T) (step := step) (Nat.le_add_right _ _) hn⟩

  /-- Monotonicity in the finite tail: `ε ≤ ε'` implies `ω+ε ≤ ω+ε'`. -/
  theorem ExtendωPlus_mono
      {T : Theory} {step : Nat → Formula} {ε ε' : Nat} (h : ε ≤ ε') :
      ExtendωPlus T step ε ≤ᵀ ExtendωPlus T step ε' :=
  by
    intro ψ hε
    rcases hε with ⟨n, hn⟩
    have : n + ε ≤ n + ε' := Nat.add_le_add_left h n
    exact ⟨n, ExtendIter_le_mono (T := T) (step := step) this hn⟩

  /-- Each `(n + ε)`‑stage embeds into `ExtendωPlus _ _ ε`. -/
  theorem stage_le_omegaPlus
      {T : Theory} {step : Nat → Formula} (ε n : Nat) :
      ExtendIter T step (n + ε) ≤ᵀ ExtendωPlus T step ε :=
  by
    intro ψ h
    exact ⟨n, h⟩

  /-- `ExtendωPlus` is the least upper bound of the shifted chain `n ↦ n+ε`. -/
  theorem ExtendωPlus_is_lub
      {T : Theory} {step : Nat → Formula} {ε : Nat} {U : Theory}
      (hU : ∀ n, ExtendIter T step (n + ε) ≤ᵀ U) :
      ExtendωPlus T step ε ≤ᵀ U :=
  by
    intro ψ h
    rcases h with ⟨n, hn⟩
    exact hU n ψ hn

  /-- Congruence for ω+ε: if steps agree pointwise, provability is preserved. -/
  @[simp] theorem ExtendωPlus_provable_congr
    {T : Theory} {A B : Nat → Formula} (ε : Nat)
    (h : ∀ i, A i = B i) (ψ : Formula) :
    (ExtendωPlus T A ε).Provable ψ ↔ (ExtendωPlus T B ε).Provable ψ := by
  constructor
  · intro hA; rcases hA with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hstage :=
      ExtendIter_congr (T := T) (A := A) (B := B) (n := n + ε) (fun i _ => h i)
    -- rewrite the stage theory and reuse the proof
    rw [← hstage]; exact hn
  · intro hB; rcases hB with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hstage :=
      ExtendIter_congr (T := T) (A := B) (B := A) (n := n + ε) (fun i _ => (h i).symm)
    rw [← hstage]; exact hn

  /-- Theory equivalence for ω+ε from step equality. -/
  theorem ExtendωPlus_equiv_of_steps_eq
    {T : Theory} {A B : Nat → Formula} (ε : Nat) (h : ∀ i, A i = B i) :
    ExtendωPlus T A ε ≃ᵀ ExtendωPlus T B ε :=
  ⟨ (by intro ψ hψ; exact (ExtendωPlus_provable_congr (T := T) (A := A) (B := B) ε h ψ).1 hψ)
   ,(by intro ψ hψ; exact (ExtendωPlus_provable_congr (T := T) (A := A) (B := B) ε h ψ).2 hψ) ⟩

  /-- Congruence for ω+ε using only *bounded* agreement:
      if `A` and `B` agree on all indices `< (n + ε)` for each witness `n`,
      then ω+ε-provability transports. -/
  @[simp] theorem ExtendωPlus_provable_congr_up_to
    {T : Theory} {A B : Nat → Formula} (ε : Nat)
    (h : ∀ n i, i < n + ε → A i = B i) (ψ : Formula) :
    (ExtendωPlus T A ε).Provable ψ ↔ (ExtendωPlus T B ε).Provable ψ := by
    constructor
    · intro hA
      rcases hA with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      -- stagewise transport at `n+ε` using bounded pointwise equality
      have hstage :=
        ExtendIter_congr (T := T) (A := A) (B := B) (n := n + ε)
          (fun i hi => h n i hi)
      -- rewrite the stage theory and reuse the proof
      rw [← hstage]; exact hn
    · intro hB
      rcases hB with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have hstage :=
        ExtendIter_congr (T := T) (A := B) (B := A) (n := n + ε)
          (fun i hi => (h n i hi).symm)
      rw [← hstage]; exact hn

  /-- ExtendωPlus with finite ε is equivalent to Extendω.
      This follows from monotonicity: any stage n+ε embeds into ω,
      and ω already contains all finite stages including ε itself. -/
  theorem ExtendωPlus_equiv_omega {T : Theory} {step : Nat → Formula} (ε : Nat) :
    ExtendωPlus T step ε ≃ᵀ Extendω T step := by
    constructor
    · -- ExtendωPlus ≤ᵀ Extendω
      intro ψ ⟨n, hn⟩
      exact ⟨n + ε, hn⟩
    · -- Extendω ≤ᵀ ExtendωPlus
      intro ψ ⟨m, hm⟩
      -- Any stage m embeds into some n+ε by choosing n large enough
      if h : m ≥ ε then
        refine ⟨m - ε, ?_⟩
        have : m - ε + ε = m := Nat.sub_add_cancel h
        rw [this]; exact hm
      else
        refine ⟨0, ?_⟩
        apply ExtendIter_le_mono (T := T) (step := step)
        · have : m < ε := Nat.lt_of_not_le h
          simp only [Nat.zero_add]
          exact Nat.le_of_lt this
        · exact hm

  /-- Push a single certificate to `ω+ε`. -/
  theorem certToOmegaPlus
    {T : Theory} {step : Nat → Formula} {φ : Formula}
    (ε : Nat) (c : HeightCertificate T step φ) :
    (ExtendωPlus T step ε).Provable φ :=
  by
    refine ⟨c.n, ?_⟩
    exact ExtendIter_le_mono (T := T) (step := step) (Nat.le_add_right _ _) c.upper

  /-- Push a pair certificate to `ω+ε`. -/
  theorem pairToOmegaPlus
    {T : Theory} {step : Nat → Formula} {g : PairGoal}
    (ε : Nat) (p : HeightCertificatePair T step g) :
    (ExtendωPlus T step ε).Provable g.φ ∧
    (ExtendωPlus T step ε).Provable g.ψ :=
  by
    refine ⟨?φ, ?ψ⟩
    · refine ⟨p.n, ?_⟩
      exact ExtendIter_le_mono (T := T) (step := step) (Nat.le_add_right _ _) p.upper_left
    · refine ⟨p.n, ?_⟩
      exact ExtendIter_le_mono (T := T) (step := step) (Nat.le_add_right _ _) p.upper_right

  /-- From a prefix certificate `cA.n ≤ k`, conclude `ω+ε` provability on the concatenation. -/
  theorem omegaPlus_of_prefixCert
    {T : Theory} {A B : Nat → Formula} {φ : Formula}
    (k ε : Nat) (cA : HeightCertificate T A φ) (hAk : cA.n ≤ k) :
    (ExtendωPlus T (concatSteps k A B) ε).Provable φ :=
  by
    -- lift `cA` into the concatenation at the same stage, then bump by `ε`.
    exact certToOmegaPlus (T := T) (step := concatSteps k A B) (ε := ε)
      (prefixLiftCert (T := T) (A := A) (B := B) k cA hAk)

  /-- From a tail certificate over `ExtendIter T A k`, conclude `ω+ε` provability on the concatenation. -/
  theorem omegaPlus_of_tailCert
    {T : Theory} {A B : Nat → Formula} {ψ : Formula}
    (k ε : Nat) (cB : HeightCertificate (ExtendIter T A k) B ψ) :
    (ExtendωPlus T (concatSteps k A B) ε).Provable ψ :=
  by
    -- lift the tail certificate to stage `k + cB.n` on the concatenation, then bump by `ε`.
    exact certToOmegaPlus (T := T) (step := concatSteps k A B) (ε := ε)
      (tailLiftCert (T := T) (A := A) (B := B) k cB)

  /-- Compose prefix+tail into a pair on the concatenation and push both parts to `ω+ε`. -/
  theorem omegaPlus_of_concat_pair
    {T : Theory} {A B : Nat → Formula} {φ ψ : Formula}
    (k ε : Nat)
    (cA : HeightCertificate T A φ) (hAk : cA.n ≤ k)
    (cB : HeightCertificate (ExtendIter T A k) B ψ) :
    (ExtendωPlus T (concatSteps k A B) ε).Provable φ ∧
    (ExtendωPlus T (concatSteps k A B) ε).Provable ψ :=
  by
    -- build the finite pair at the cut, then push the pair to `ω+ε`.
    exact pairToOmegaPlus (T := T) (step := concatSteps k A B) (ε := ε)
      (concatPairCert (T := T) (A := A) (B := B) k cA hAk cB)

  /-- Re-express ω+ε provability as "provable at some stage `m ≥ ε`". -/
  @[simp] theorem ExtendωPlus_Provable_iff_exists_ge
    {T : Theory} {step : Nat → Formula} {ε : Nat} {ψ : Formula} :
    (ExtendωPlus T step ε).Provable ψ
      ↔ ∃ m, ε ≤ m ∧ (ExtendIter T step m).Provable ψ :=
  by
    constructor
    · intro h
      rcases h with ⟨n, hn⟩
      have hε : ε ≤ n + ε := by
        -- `ε ≤ ε + n` then commute addition
        simp [Nat.add_comm, Nat.le_add_left]
      exact ⟨n + ε, hε, hn⟩
    · intro h
      rcases h with ⟨m, hεm, hm⟩
      refine ⟨m - ε, ?_⟩
      -- because `ε ≤ m`, we can peel off the ε-tail
      simp [Nat.sub_add_cancel hεm]
      exact hm

  /-- Under theory equivalence, provability is logically equivalent in both directions. -/
  theorem theoryEqv.provable_iff
    {T U : Theory} (h : T ≃ᵀ U) (ψ : Formula) :
    T.Provable ψ ↔ U.Provable ψ :=
  ⟨fun hT => h.left  ψ hT, fun hU => h.right ψ hU⟩

end Papers.P4Meta