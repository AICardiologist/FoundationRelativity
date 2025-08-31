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
theorem con_height_upper (T0 : Theory) [HasArithmetization T0] :
  (LCons T0 1).Provable (ConTag[T0] 0) := by
  simp [LCons, Extend_Proves]

/-- Gödel sentence tag (schematic, not the actual Gödel sentence) -/
abbrev godelFormula := GTagFormula

namespace Ax

/-- Gödel sentence follows from consistency (classical).
    Provenance: Gödel 1931, via fixed-point construction. -/
axiom con_implies_godel (T : Theory) [HasArithmetization T] (n : Nat) :
  T.Provable (ConTag[T] n) → T.Provable (godelFormula n)

end Ax

export Ax (con_implies_godel)

/-- Gödel sentence has height 1 on the consistency ladder -/
theorem godel_height_upper (T0 : Theory) [HasArithmetization T0] :
  (LCons T0 1).Provable (godelFormula 0) := by
  apply con_implies_godel
  exact con_height_upper T0

/-- RFN has height 1 on the reflection ladder -/
theorem rfn_height_upper (T0 : Theory) [HasArithmetization T0] :
  (LReflect T0 1).Provable (RfnTag[T0] 0) := by
  simp [LReflect, Extend_Proves]

/-- Iterated consistency at height n -/
theorem con_iter_height_upper (T0 : Theory) [HasArithmetization T0] (n : Nat) :
  (ExtendIter T0 (consSteps T0) (n+1)).Provable (ConTag[T0] n) := by
  rw [← LCons_as_ExtendIter]
  apply LCons_proves_Con

/-! ## Lower Bounds (Classical, Axiomatized) -/

/-- Typeclass for consistent theories -/
class Consistent (T : Theory) : Prop where
  not_proves_bot : ¬T.Provable Bot

/-- Typeclass for theories satisfying HBL conditions -/
class HBL (T : Theory) extends HasDerivability T

namespace Ax

/-- G2: Gödel's second incompleteness theorem (classical).
    Provenance: Gödel 1931, standard proof-theoretic result. -/
axiom G2_lower (T : Theory) [Consistent T] [HBL T] :
  ¬(T.Provable (ConTag 0))

/-- G1: Gödel's first incompleteness theorem (classical).
    Provenance: Gödel 1931, via fixed-point construction. -/
axiom G1_lower (T : Theory) [Consistent T] [HBL T] :
  ¬(T.Provable (GTagFormula 0))

/-- Reflection does not prove its own reflection (classical).
    Provenance: Feferman 1962, iteration of reflection principles. -/
axiom RFN_lower (T : Theory) [Consistent T] [HBL T] :
  ¬(T.Provable (RfnTag 0))

/-- The consistency hierarchy is proper (classical). -/
axiom cons_hierarchy_proper (T0 : Theory) [Consistent T0] [HBL T0] (n : Nat) :
  ¬((LCons T0 n).Provable (ConTag n))

/-- The reflection hierarchy is proper (classical). -/
axiom refl_hierarchy_proper (T0 : Theory) [Consistent T0] [HBL T0] (n : Nat) :
  ¬((LReflect T0 n).Provable (RfnTag n))

end Ax

-- Export axioms except the ones we're about to discharge (and WLPO/LPO_lower which come later)
export Ax (G2_lower G1_lower RFN_lower cons_hierarchy_proper refl_hierarchy_proper)

/-- WLPO has height 1 on classicality ladder.
    Proved via Extend_Proves since WLPO_formula = ClassicalitySteps 0. -/
theorem WLPO_height_upper : (LClass 1).Provable WLPO_formula := by
  -- LClass 1 = Extend HA (ClassicalitySteps 0)
  -- and WLPO_formula = ClassicalitySteps 0
  -- so Extend proves the added formula
  simp only [LClass, WLPO_formula]
  exact Extend_Proves

/-- LPO has height 2 on classicality ladder.
    Proved via Extend_Proves since LPO_formula = ClassicalitySteps 1. -/
theorem LPO_height_upper : (LClass 2).Provable LPO_formula := by
  -- LClass 2 = Extend (LClass 1) (ClassicalitySteps 1)
  -- and LPO_formula = ClassicalitySteps 1
  -- so Extend proves the added formula
  simp only [LClass, LPO_formula]
  exact Extend_Proves

namespace Ax

/-- WLPO is independent of HA (classical).
    Provenance: Constructive reverse mathematics. -/
axiom WLPO_lower : ¬(HA.Provable WLPO_formula)

/-- LPO is independent of HA + EM_Σ₀ (classical).
    Provenance: Constructive reverse mathematics. -/
axiom LPO_lower : ¬((LClass 1).Provable LPO_formula)

end Ax

-- Export remaining axioms (WLPO_height_upper and LPO_height_upper are now theorems)
export Ax (WLPO_lower LPO_lower)

/-! ## Height Certificates -/

/-- Certificate for consistency on LCons -/
def con_height_cert (T0 : Theory) [HasArithmetization T0] [Consistent T0] [HBL T0] :
  HeightCertificate T0 (consSteps T0) (ConTag[T0] 0) :=
{ n := 1
, upper := con_height_upper T0
, note := "Upper: definitional; Lower: G2 (classical)" }

/-- Certificate for Gödel sentence on LCons -/
def godel_height_cert (T0 : Theory) [HasArithmetization T0] [Consistent T0] [HBL T0] :
  HeightCertificate T0 (consSteps T0) (godelFormula 0) :=
{ n := 1
, upper := godel_height_upper T0
, note := "Upper: via Con→G; Lower: G1 (classical)" }

/-- Certificate for RFN on LReflect -/
def rfn_height_cert (T0 : Theory) [HasArithmetization T0] [Consistent T0] [HBL T0] :
  HeightCertificate T0 (reflSteps T0) (RfnTag[T0] 0) :=
{ n := 1
, upper := rfn_height_upper T0
, note := "Upper: definitional; Lower: Feferman (classical)" }

/-! ## Classicality Heights -/


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
def con_n_height (T0 : Theory) [HasArithmetization T0] [Consistent T0] [HBL T0] (n : Nat) :
  HeightCertificate T0 (consSteps T0) (ConTag[T0] n) :=
{ n := n + 1
, upper := con_iter_height_upper T0 n
, note := s!"Upper: iteration; Lower: G2^{n+1} (classical)" }


end Papers.P4Meta.ProofTheory