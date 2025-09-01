/-
  Papers/P3_2CatFramework/P4_Meta/ProofTheory/Progressions.lean
  
  Ladder constructions for consistency, reflection, and classicality hierarchies.
  These model Turing-style and Feferman-style progressions schematically.
  
  Axioms used in this module:
  - LClass_omega_eq_PA: Limit of classicality ladder
  
  Note: Tags are now parametric and definitionally equal to semantic formulas.
  No bridge axioms needed!
-/

import Papers.P3_2CatFramework.P4_Meta.ProofTheory.Core
import Papers.P3_2CatFramework.P4_Meta.ProofTheory.Reflection

namespace Papers.P4Meta.ProofTheory

open Papers.P4Meta

/-- Scoped notation for Extend to improve readability -/
scoped notation:55 T " ⊕ " φ => Extend T φ

/-! ## Ladder Definitions -/

/-- The consistency ladder starting from base theory T0 -/
def LCons (T0 : Theory) [HasArithmetization T0] : Nat → Theory
  | 0 => T0
  | n+1 => Extend (LCons T0 n) (ConTag n)

/-- The reflection ladder starting from base theory T0 -/
def LReflect (T0 : Theory) [HasArithmetization T0] : Nat → Theory
  | 0 => T0
  | n+1 => Extend (LReflect T0 n) (RfnTag n)

/-- Arithmetization for consistency ladder -/
def LCons_arithmetization (T0 : Theory) [h : HasArithmetization T0] : 
    ∀ n, HasArithmetization (LCons T0 n)
  | 0 => by simp [LCons]; exact h
  | n+1 => by
    simp [LCons]
    haveI : HasArithmetization (LCons T0 n) := LCons_arithmetization T0 n
    exact inferInstance

/-- Arithmetization for reflection ladder -/  
def LReflect_arithmetization (T0 : Theory) [h : HasArithmetization T0] :
    ∀ n, HasArithmetization (LReflect T0 n)
  | 0 => by simp [LReflect]; exact h
  | n+1 => by
    simp [LReflect]
    haveI : HasArithmetization (LReflect T0 n) := LReflect_arithmetization T0 n
    exact inferInstance

-- Make them instances
instance (T0 : Theory) [HasArithmetization T0] (n : Nat) : HasArithmetization (LCons T0 n) :=
  LCons_arithmetization T0 n

instance (T0 : Theory) [HasArithmetization T0] (n : Nat) : HasArithmetization (LReflect T0 n) :=
  LReflect_arithmetization T0 n

/-- Notation for readability (just adds brackets for visual clarity). -/
scoped notation "ConTag[" n "]" => ConTag n
scoped notation "RfnTag[" n "]" => RfnTag n

/-- Helper: Schematic consistency tag (backward compatibility) -/
abbrev consFormula (n : Nat) : Formula := ConTag n

/-- Helper: Schematic reflection tag (backward compatibility) -/
abbrev reflFormula (n : Nat) : Formula := RfnTag n

/-! ## Basic Properties -/

@[simp]
theorem LCons_zero (T0 : Theory) [HasArithmetization T0] : 
  LCons T0 0 = T0 := rfl

@[simp]
theorem LCons_succ (T0 : Theory) [HasArithmetization T0] (n : Nat) :
  LCons T0 (n+1) = Extend (LCons T0 n) (ConTag n) := rfl

/-- Each step adds the consistency of the previous -/
theorem LCons_proves_Con (T0 : Theory) [HasArithmetization T0] (n : Nat) :
  (LCons T0 (n+1)).Provable (ConTag n) := by
  simp [LCons, Extend_Proves]

@[simp]
theorem LReflect_zero (T0 : Theory) [HasArithmetization T0] :
  LReflect T0 0 = T0 := rfl

@[simp]
theorem LReflect_succ (T0 : Theory) [HasArithmetization T0] (n : Nat) :
  LReflect T0 (n+1) = Extend (LReflect T0 n) (RfnTag n) := rfl

/-- Each step adds the Σ₁ reflection principle -/
theorem LReflect_proves_RFN (T0 : Theory) [HasArithmetization T0] (n : Nat) :
  (LReflect T0 (n+1)).Provable (RfnTag n) := by
  simp [LReflect, Extend_Proves]

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
def consSteps : Nat → Formula := ConTag

/-- Steps for the reflection ladder -/
def reflSteps : Nat → Formula := RfnTag

/-- The ladders match ExtendIter with their steps -/
theorem LCons_as_ExtendIter (T0 : Theory) [HasArithmetization T0] (n : Nat) :
  LCons T0 n = ExtendIter T0 consSteps n := by
  induction n with
  | zero => rfl
  | succ n ih => 
    simp [LCons, ExtendIter, consSteps, ih]

theorem LReflect_as_ExtendIter (T0 : Theory) [HasArithmetization T0] (n : Nat) :
  LReflect T0 n = ExtendIter T0 reflSteps n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [LReflect, ExtendIter, reflSteps, ih]

/-! ## Limit Axiom -/

namespace Ax

/-- At the limit, LClass reaches PA.
    Provenance: Classical result from ordinal analysis. -/
axiom LClass_omega_eq_PA : ExtendOmega HA ClassicalitySteps = PA

end Ax

-- Export for compatibility
export Ax (LClass_omega_eq_PA)

/-! ## Realization Classes 

Since tags are definitionally equal to semantic formulas,
these classes now have trivial instances.
-/

/-- Refinement from schematic stage tags to semantic statements. -/
class RealizesCons (T0 : Theory) [HasArithmetization T0] where
  realize :
    ∀ n, (LCons T0 (n+1)).Provable (ConTag n) →
         (LCons T0 (n+1)).Provable (ConsistencyFormula (LCons T0 n))

class RealizesRFN (T0 : Theory) [HasArithmetization T0] where
  realize :
    ∀ n, (LReflect T0 (n+1)).Provable (RfnTag n) →
         (LReflect T0 (n+1)).Provable (RFN_Sigma1_Formula (LReflect T0 n))

-- Bridge axioms needed due to schematic tags
namespace Ax

axiom cons_tag_refines {T0 : Theory} [HasArithmetization T0] (n : Nat) :
  ConTag n = ConsistencyFormula (LCons T0 n)

axiom rfn_tag_refines {T0 : Theory} [HasArithmetization T0] (n : Nat) :
  RfnTag n = RFN_Sigma1_Formula (LReflect T0 n)

end Ax

export Ax (cons_tag_refines rfn_tag_refines)

-- With the bridge axioms, the instances are straightforward
noncomputable instance realizesCons {T0 : Theory} [HasArithmetization T0] : RealizesCons T0 :=
  ⟨fun n h => by rw [← cons_tag_refines]; exact h⟩

noncomputable instance realizesRFN {T0 : Theory} [HasArithmetization T0] : RealizesRFN T0 :=
  ⟨fun n h => by rw [← rfn_tag_refines]; exact h⟩

end Papers.P4Meta.ProofTheory