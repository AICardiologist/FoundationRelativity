/-
  Papers/P3_2CatFramework/P4_Meta/ProofTheory/Heights.lean
  
  Height certificates for proof-theoretic hierarchies.
  Proves upper bounds constructively, axiomatizes classical lower bounds.
  
  Axioms used in this module:
  - con_implies_godel: Con → G connection
  - G1_lower, G2_lower, RFN_lower: Classical lower bounds
  - cons_hierarchy_proper, refl_hierarchy_proper: Hierarchy strictness
  - WLPO_height_upper, LPO_height_upper: Classicality bounds
  - WLPO_lower, LPO_lower: Independence results
-/

import Papers.P3_2CatFramework.P4_Meta.ProofTheory.Progressions
import Papers.P3_2CatFramework.P4_Meta.PartIII_Certificates

namespace Papers.P4Meta.ProofTheory

open Papers.P4Meta

/-! ## Upper Bounds (Constructive) -/

/-- Consistency has height 1 on the consistency ladder -/
theorem con_height_upper (T0 : Theory) :
  (LCons T0 1).Provable (consFormula 0) := by
  simp [LCons, Extend_Proves]

/-- Gödel sentence tag (schematic, not the actual Gödel sentence) -/
def godelFormula : Nat → Formula
  | n => GTagFormula n

/-- Gödel sentence follows from consistency (classical) -/
axiom con_implies_godel (T : Theory) (n : Nat) :
  T.Provable (consFormula n) → T.Provable (godelFormula n)

/-- Gödel sentence has height 1 on the consistency ladder -/
theorem godel_height_upper (T0 : Theory) :
  (LCons T0 1).Provable (godelFormula 0) := by
  apply con_implies_godel
  exact con_height_upper T0

/-- RFN has height 1 on the reflection ladder -/
theorem rfn_height_upper (T0 : Theory) :
  (LReflect T0 1).Provable (reflFormula 0) := by
  simp [LReflect, Extend_Proves]

/-- Iterated consistency at height n -/
theorem con_iter_height_upper (T0 : Theory) (n : Nat) :
  (ExtendIter T0 consSteps (n+1)).Provable (consFormula n) := by
  rw [← LCons_as_ExtendIter]
  apply LCons_proves_Con

/-! ## Lower Bounds (Classical, Axiomatized) -/

/-- Typeclass for consistent theories -/
class Consistent (T : Theory) : Prop where
  not_proves_bot : ¬T.Provable Bot

/-- Typeclass for theories satisfying HBL conditions -/
class HBL (T : Theory) extends HasDerivability T

/-- G2: Gödel's second incompleteness theorem (classical)
    Provenance: Gödel 1931, standard proof-theoretic result -/
axiom G2_lower (T : Theory) [Consistent T] [HBL T] :
  ¬(T.Provable (ConTag 0))

/-- G1: Gödel's first incompleteness theorem (classical)
    Provenance: Gödel 1931, via fixed-point construction -/
axiom G1_lower (T : Theory) [Consistent T] [HBL T] :
  ¬(T.Provable (GTagFormula 0))

/-- Reflection does not prove its own reflection (classical)
    Provenance: Feferman 1962, iteration of reflection principles -/
axiom RFN_lower (T : Theory) [Consistent T] [HBL T] :
  ¬(T.Provable (RfnTag 0))

/-! ## Height Certificates -/

/-- Certificate for consistency on LCons -/
def con_height_cert (T0 : Theory) [Consistent T0] [HBL T0] :
  HeightCertificate T0 consSteps (consFormula 0) :=
{ n := 1
, upper := con_height_upper T0
, note := "Upper: definitional; Lower: G2 (classical)" }

/-- Certificate for Gödel sentence on LCons -/
def godel_height_cert (T0 : Theory) [Consistent T0] [HBL T0] :
  HeightCertificate T0 consSteps (godelFormula 0) :=
{ n := 1
, upper := godel_height_upper T0
, note := "Upper: via Con→G; Lower: G1 (classical)" }

/-- Certificate for RFN on LReflect -/
def rfn_height_cert (T0 : Theory) [Consistent T0] [HBL T0] :
  HeightCertificate T0 reflSteps (reflFormula 0) :=
{ n := 1
, upper := rfn_height_upper T0
, note := "Upper: definitional; Lower: Feferman (classical)" }

/-! ## Classicality Heights -/

/-- WLPO has height 1 on classicality ladder 
    TODO: Complete proof that WLPO ⊆ EM_Σ₀ -/
axiom WLPO_height_upper : (LClass 1).Provable WLPO_formula

/-- LPO has height 2 on classicality ladder
    TODO: Complete proof that LPO ⊆ EM_Σ₁ -/
axiom LPO_height_upper : (LClass 2).Provable LPO_formula

/-- WLPO is independent of HA (classical)
    Provenance: Constructive reverse mathematics -/
axiom WLPO_lower : ¬(HA.Provable WLPO_formula)

/-- LPO is independent of HA + EM_Σ₀ (classical)
    Provenance: Constructive reverse mathematics -/
axiom LPO_lower : ¬((LClass 1).Provable LPO_formula)

/-- Certificate for WLPO on classicality ladder -/
def WLPO_height_cert : HeightCertificate HA ClassicalitySteps WLPO_formula :=
{ n := 1
, upper := WLPO_height_upper
, note := "Upper: WLPO ⊆ EM_Σ₀; Lower: constructive independence" }

/-- Certificate for LPO on classicality ladder -/
def LPO_height_cert : HeightCertificate HA ClassicalitySteps LPO_formula :=
{ n := 2
, upper := LPO_height_upper
, note := "Upper: LPO ⊆ EM_Σ₁; Lower: constructive independence" }

/-! ## Iterated Heights -/

/-- Height n consistency on the consistency ladder -/
def con_n_height (T0 : Theory) [Consistent T0] [HBL T0] (n : Nat) :
  HeightCertificate T0 consSteps (consFormula n) :=
{ n := n + 1
, upper := con_iter_height_upper T0 n
, note := s!"Upper: iteration; Lower: G2^{n+1} (classical)" }

/-- The consistency hierarchy is proper (classical) -/
axiom cons_hierarchy_proper (T0 : Theory) [Consistent T0] [HBL T0] (n : Nat) :
  ¬((LCons T0 n).Provable (ConTag n))

/-- The reflection hierarchy is proper (classical) -/
axiom refl_hierarchy_proper (T0 : Theory) [Consistent T0] [HBL T0] (n : Nat) :
  ¬((LReflect T0 n).Provable (RfnTag n))

end Papers.P4Meta.ProofTheory