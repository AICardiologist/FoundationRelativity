/-
  Papers/P3_2CatFramework/P4_Meta/ProofTheory/Progressions.lean

  **Key change (PR-6 support)**:
  Define ladders *semantically* and carry their arithmetization instances along
  the recursion. Then introduce *notation* tags that are defeq to those semantic
  formulas. This avoids circular dependencies and eliminates bridge axioms.
-/

import Papers.P3_2CatFramework.P4_Meta.ProofTheory.Core
import Papers.P3_2CatFramework.P4_Meta.ProofTheory.Reflection

namespace Papers.P4Meta.ProofTheory

open Papers.P4Meta
open Classical
noncomputable section

/-- Scoped notation for Extend to improve readability -/
scoped notation:55 T " ⊕ " φ => Extend T φ

/-! ## Semantic ladders via carried instances -/

/-- A ladder stage bundles a theory with its arithmetization instance. -/
structure Stage where
  T     : Theory
  inst  : HasArithmetization T

attribute [instance] Stage.inst

namespace Stage
  /-- Extend a stage by adding a formula; the instance is inferred from the previous stage. -/
  def extend (s : Stage) (φ : Formula) : Stage :=
    -- `inferInstance` comes from PR-1: Extend preserves arithmetization
    let T' := Extend s.T φ
    haveI : HasArithmetization T' := inferInstance
    ⟨T', inferInstance⟩
end Stage

/-- Consistency ladder on `Stage`. -/
def LConsS (s0 : Stage) : Nat → Stage
| 0     => s0
| n+1   =>
  let prev := LConsS s0 n
  -- Use the instance carried by `prev` to form the semantic consistency formula
  letI : HasArithmetization prev.T := prev.inst
  Stage.extend prev (ConsistencyFormula prev.T)

/-- Reflection ladder on `Stage`. -/
def LReflectS (s0 : Stage) : Nat → Stage
| 0     => s0
| n+1   =>
  let prev := LReflectS s0 n
  -- Use the instance carried by `prev` to form the Σ₁-RFN formula
  letI : HasArithmetization prev.T := prev.inst
  Stage.extend prev (RFN_Sigma1_Formula prev.T)

/-! ## Projected ladders and instances -/

/-- Consistency ladder (projected theory). -/
def LCons (T0 : Theory) [i0 : HasArithmetization T0] (n : Nat) : Theory :=
  (LConsS ⟨T0, i0⟩ n).T

/-- Reflection ladder (projected theory). -/
def LReflect (T0 : Theory) [i0 : HasArithmetization T0] (n : Nat) : Theory :=
  (LReflectS ⟨T0, i0⟩ n).T

instance (T0 : Theory) [i0 : HasArithmetization T0] (n : Nat) :
    HasArithmetization (LCons T0 n) :=
  (LConsS ⟨T0, i0⟩ n).inst

instance (T0 : Theory) [i0 : HasArithmetization T0] (n : Nat) :
    HasArithmetization (LReflect T0 n) :=
  (LReflectS ⟨T0, i0⟩ n).inst

/-! ## Tag notations (defeq to semantic formulas) -/

scoped notation "RfnTag[" T0 "] " n =>
  RFN_Sigma1_Formula (LReflect T0 n)

scoped notation "ConTag[" T0 "] " n =>
  ConsistencyFormula (LReflect T0 n)

/-! ## Basic Properties -/

@[simp] theorem LCons_zero (T0 : Theory) [HasArithmetization T0] :
  LCons T0 0 = T0 := rfl

@[simp] theorem LReflect_zero (T0 : Theory) [HasArithmetization T0] :
  LReflect T0 0 = T0 := rfl

@[simp] theorem LCons_succ (T0 : Theory) [HasArithmetization T0] (n : Nat) :
  LCons T0 (n+1) = Extend (LCons T0 n) (ConsistencyFormula (LCons T0 n)) := rfl

@[simp] theorem LReflect_succ (T0 : Theory) [HasArithmetization T0] (n : Nat) :
  LReflect T0 (n+1) = Extend (LReflect T0 n) (RFN_Sigma1_Formula (LReflect T0 n)) := rfl

/-- Each step adds the consistency of the previous -/
theorem LCons_proves_Con (T0 : Theory) [HasArithmetization T0] (n : Nat) :
  (LCons T0 (n+1)).Provable (ConsistencyFormula (LCons T0 n)) :=
  Extend_Proves

/-- Each step adds the Σ₁ reflection principle -/
theorem LReflect_proves_RFN (T0 : Theory) [HasArithmetization T0] (n : Nat) :
  (LReflect T0 (n+1)).Provable (RfnTag[T0] n) :=
  Extend_Proves

/-! ## Classicality Ladder -/

/-- The classicality ladder from HA to PA -/
noncomputable def LClass : Nat → Theory
  | 0 => HA
  | n+1 => Extend (LClass n) (ClassicalitySteps n)

@[simp]
theorem LClass_zero : LClass 0 = HA := rfl

@[simp]
theorem LClass_succ (n : Nat) :
  LClass (n+1) = Extend (LClass n) (ClassicalitySteps n) := rfl

/-- Each step adds the next excluded middle fragment -/
theorem LClass_proves_EM (n : Nat) :
  (LClass (n+1)).Provable (ClassicalitySteps n) := by
  simp [LClass, Extend_Proves]

/-! ## Limit Constructions -/

/-- Limit of a ladder at ω -/
def ExtendOmega (T0 : Theory) (step : Nat → Formula) : Theory :=
  { Provable := fun φ => ∃ n, (ExtendIter T0 step n).Provable φ }

/-- Instancewise provability at ω -/
theorem ExtendOmega_instancewise (T0 : Theory) (step : Nat → Formula) (n : Nat) (φ : Formula) :
  (ExtendIter T0 step n).Provable φ → (ExtendOmega T0 step).Provable φ := 
  fun h => ⟨n, h⟩

/-! ## Ladder Morphisms -/

/-- A morphism between ladders preserves provability -/
structure LadderMorphism (L1 L2 : Nat → Theory) where
  /-- The underlying map on indices -/
  map : Nat → Nat
  /-- Provability is preserved -/
  preserves : ∀ n φ, (L1 n).Provable φ → (L2 (map n)).Provable φ

/-- Identity morphism -/
def LadderMorphism.id (L : Nat → Theory) : LadderMorphism L L :=
  { map := fun n => n
  , preserves := fun _ _ h => h }

/-- Composition of morphisms -/
def LadderMorphism.comp {L1 L2 L3 : Nat → Theory} 
  (g : LadderMorphism L2 L3) (f : LadderMorphism L1 L2) : 
  LadderMorphism L1 L3 :=
  { map := g.map ∘ f.map
  , preserves := fun n φ h => g.preserves (f.map n) φ (f.preserves n φ h) }

@[simp]
theorem LadderMorphism.id_map (L : Nat → Theory) (n : Nat) :
  (LadderMorphism.id L).map n = n := rfl

@[simp]
theorem LadderMorphism.comp_map {L M N : Nat → Theory} 
  (f : LadderMorphism L M) (g : LadderMorphism M N) (n : Nat) :
  (LadderMorphism.comp g f).map n = g.map (f.map n) := rfl

/-! ## Monotonicity Properties -/

/-- Ladders are monotone: later stages prove more -/
theorem LCons_mono (T0 : Theory) [HasArithmetization T0] {m n : Nat} (h : m ≤ n) :
  ∀ φ, (LCons T0 m).Provable φ → (LCons T0 n).Provable φ := by
  intro φ
  induction h with
  | refl => intro h; exact h
  | step h ih => 
    intro h_prov
    apply Extend_mono
    exact ih h_prov

theorem LReflect_mono (T0 : Theory) [HasArithmetization T0] {m n : Nat} (h : m ≤ n) :
  ∀ φ, (LReflect T0 m).Provable φ → (LReflect T0 n).Provable φ := by
  intro φ
  induction h with
  | refl => intro h; exact h
  | step h ih =>
    intro h_prov
    apply Extend_mono
    exact ih h_prov

theorem LClass_mono {m n : Nat} (h : m ≤ n) :
  ∀ φ, (LClass m).Provable φ → (LClass n).Provable φ := by
  intro φ
  induction h with
  | refl => intro h; exact h
  | step h ih =>
    intro h_prov
    apply Extend_mono
    exact ih h_prov

/-! ## Consistency Steps -/

/-- Steps for the consistency ladder -/
def consSteps (T0 : Theory) [HasArithmetization T0] : Nat → Formula := 
  fun n => ConsistencyFormula (LCons T0 n)

/-- Steps for the reflection ladder -/
def reflSteps (T0 : Theory) [HasArithmetization T0] : Nat → Formula := 
  fun n => RFN_Sigma1_Formula (LReflect T0 n)

-- Note: ExtendIter equivalence theorems are not needed for PR-6
-- The Stage-based approach directly carries instances to avoid circular dependencies

/-! ## Limit Axiom -/

namespace Ax

/-- At the limit, LClass reaches PA.
    Provenance: Classical result from ordinal analysis. -/
axiom LClass_omega_eq_PA : ExtendOmega HA ClassicalitySteps = PA

end Ax

-- Export for compatibility
export Ax (LClass_omega_eq_PA)

end -- noncomputable section
end Papers.P4Meta.ProofTheory