/-
  Papers/P3_2CatFramework/P4_Meta/ProofTheory/Progressions.lean
  
  Ladder constructions for consistency, reflection, and classicality hierarchies.
  These model Turing-style and Feferman-style progressions schematically.
-/

import Papers.P3_2CatFramework.P4_Meta.ProofTheory.Core
import Papers.P3_2CatFramework.P4_Meta.ProofTheory.Reflection

namespace Papers.P4Meta.ProofTheory

open Papers.P4Meta

/-! ## Formula Sequences for Ladders -/

/-- Consistency formulas indexed by level -/
def consFormula : Nat → Formula
  | n => Formula.atom (600 + n)

/-- Reflection formulas indexed by level -/
def reflFormula : Nat → Formula  
  | n => Formula.atom (800 + n)

/-! ## Consistency Ladder (Turing-style) -/

/-- The consistency ladder starting from base theory T0 -/
def LCons (T0 : Theory) : Nat → Theory
  | 0 => T0
  | n+1 => Extend (LCons T0 n) (consFormula n)

@[simp]
theorem LCons_zero (T0 : Theory) : 
  LCons T0 0 = T0 := rfl

@[simp]
theorem LCons_succ (T0 : Theory) (n : Nat) :
  LCons T0 (n+1) = Extend (LCons T0 n) (consFormula n) := rfl

/-- Each step adds the consistency of the previous -/
theorem LCons_proves_Con (T0 : Theory) (n : Nat) :
  (LCons T0 (n+1)).Provable (consFormula n) := by
  simp [LCons, Extend_Proves]

/-! ## Reflection Ladder (Feferman-style) -/

/-- The reflection ladder starting from base theory T0 -/
def LReflect (T0 : Theory) : Nat → Theory
  | 0 => T0
  | n+1 => Extend (LReflect T0 n) (reflFormula n)

@[simp]
theorem LReflect_zero (T0 : Theory) :
  LReflect T0 0 = T0 := rfl

@[simp]
theorem LReflect_succ (T0 : Theory) (n : Nat) :
  LReflect T0 (n+1) = Extend (LReflect T0 n) (reflFormula n) := rfl

/-- Each step adds the Σ₁ reflection principle -/
theorem LReflect_proves_RFN (T0 : Theory) (n : Nat) :
  (LReflect T0 (n+1)).Provable (reflFormula n) := by
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

/-- At the limit, LClass reaches PA -/
axiom LClass_omega_eq_PA : ExtendOmega HA ClassicalitySteps = PA

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

/-! ## Monotonicity Properties -/

/-- Ladders are monotone: later stages prove more -/
theorem LCons_mono (T0 : Theory) {m n : Nat} (h : m ≤ n) :
  ∀ φ, (LCons T0 m).Provable φ → (LCons T0 n).Provable φ := by
  intro φ
  induction h with
  | refl => intro h; exact h
  | step h ih => 
    intro h_prov
    apply Extend_mono
    exact ih h_prov

theorem LReflect_mono (T0 : Theory) {m n : Nat} (h : m ≤ n) :
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
def consSteps : Nat → Formula := consFormula

/-- Steps for the reflection ladder -/
def reflSteps : Nat → Formula := reflFormula

/-- The ladders match ExtendIter with their steps -/
theorem LCons_as_ExtendIter (T0 : Theory) (n : Nat) :
  LCons T0 n = ExtendIter T0 consSteps n := by
  induction n with
  | zero => rfl
  | succ n ih => 
    simp [LCons, ExtendIter, consSteps, consFormula, ih]

theorem LReflect_as_ExtendIter (T0 : Theory) (n : Nat) :
  LReflect T0 n = ExtendIter T0 reflSteps n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [LReflect, ExtendIter, reflSteps, reflFormula, ih]

/-! ## Schematic-Semantic Bridge -/

/-- Instance propagation for arithmetization.
    Provenance: Standard extension preserves arithmetization; deferred for 3B. -/
axiom LCons_arithmetization_instance [HasArithmetization T0] (n : Nat) : 
  HasArithmetization (LCons T0 n)

axiom LReflect_arithmetization_instance [HasArithmetization T0] (n : Nat) : 
  HasArithmetization (LReflect T0 n)

instance LCons_arithmetization [HasArithmetization T0] (n : Nat) : 
  HasArithmetization (LCons T0 n) := LCons_arithmetization_instance n

instance LReflect_arithmetization [HasArithmetization T0] (n : Nat) : 
  HasArithmetization (LReflect T0 n) := LReflect_arithmetization_instance n

/-- Axiomatic refinement from schematic stage tags to semantic statements.
    These are intentionally axioms for 3B minimal surface; we can discharge later. -/
class RealizesCons (T0 : Theory) [HasArithmetization T0] where
  realize : ∀ n, (LCons T0 (n+1)).Provable (consFormula n) →
    (LCons T0 (n+1)).Provable (ConsistencyFormula (LCons T0 n))

class RealizesRFN (T0 : Theory) [HasArithmetization T0] where
  realize : ∀ n, (LReflect T0 (n+1)).Provable (reflFormula n) →
    (LReflect T0 (n+1)).Provable (RFN_Sigma1_Formula (LReflect T0 n))

/-- Axiomatized: the schematic tag at step n indeed codes Con(LCons T0 n).
    Provenance: standard arithmetization; deferred in 3B minimal surface. -/
axiom cons_tag_refines (T0 : Theory) [HasArithmetization T0] (n : Nat) :
  (LCons T0 (n+1)).Provable (consFormula n) →
  (LCons T0 (n+1)).Provable (ConsistencyFormula (LCons T0 n))

/-- Axiomatized: the schematic tag at step n indeed codes RFN(LReflect T0 n).
    Provenance: standard arithmetization; deferred in 3B minimal surface. -/
axiom rfn_tag_refines (T0 : Theory) [HasArithmetization T0] (n : Nat) :
  (LReflect T0 (n+1)).Provable (reflFormula n) →
  (LReflect T0 (n+1)).Provable (RFN_Sigma1_Formula (LReflect T0 n))

instance [HasArithmetization T0] : RealizesCons T0 := ⟨cons_tag_refines T0⟩
instance [HasArithmetization T0] : RealizesRFN T0 := ⟨rfn_tag_refines T0⟩

end Papers.P4Meta.ProofTheory