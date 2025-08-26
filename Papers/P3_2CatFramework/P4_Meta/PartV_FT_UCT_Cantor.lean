/-
  Papers/P3_2CatFramework/P4_Meta/PartV_FT_UCT_Cantor.lean
  
  FT→UCT (Cantor) height analysis:
  Full Tabulation implies Unrestricted Church's Thesis
  using Cantor's diagonalization argument.
  
  This demonstrates the height-3 structure of the FT→UCT derivation
  as a data-only meta-theoretic framework (no proofs needed).
-/
import Papers.P3_2CatFramework.P4_Meta.PartIII_Certificates
import Papers.P3_2CatFramework.P4_Meta.Meta_Signature

namespace Papers.P4Meta.PartV

open Papers.P4Meta

/-- Full Tabulation: Every total computable function can be tabulated. -/
def FullTabulation : Formula := Formula.atom 300

/-- Unrestricted Church's Thesis: Every total function is computable. -/
def UnrestrictedChurchThesis : Formula := Formula.atom 301

/-- Cantor's Diagonal: The diagonal function that contradicts FT. -/
def CantorDiagonal : Formula := Formula.atom 302

/-- FT implies tabulation (atom 303). -/
def FT_implies_Tabulation : Formula := Formula.atom 303

/-- Negation of tabulation (atom 304). -/
def Not_Tabulation : Formula := Formula.atom 304

/-- FT implies UCT (atom 305). -/
def FT_implies_UCT : Formula := Formula.atom 305

/-- The 3-step schedule for FT→UCT derivation. -/
def FT_to_UCT_schedule : Nat → Formula
  | 0 => FullTabulation
  | 1 => CantorDiagonal
  | _ => UnrestrictedChurchThesis

/-- Height-3 data certificate recording the FT→UCT derivation structure. -/
structure FT_UCT_Data where
  steps : Nat → Formula
  height : Nat
  note : String

def FT_to_UCT_height3_data : FT_UCT_Data :=
{ steps := FT_to_UCT_schedule
, height := 3
, note := "Height 3: (1) FT axiom, (2) Cantor diagonal, (3) UCT resolution" }

/-- Axiomatize that this schedule achieves the derivation at height 3. -/
axiom FT_to_UCT_height3_witness :
  HeightCertificate emptyTheory FT_to_UCT_schedule FT_implies_UCT

/-- The height bound is tight (axiomatized as a meta-theoretic fact). -/
axiom FT_UCT_height_optimal :
  ∀ (steps : Nat → Formula),
    HeightCertificate emptyTheory steps FT_implies_UCT →
    ∃ n, n ≥ 2 ∧ steps n ≠ Formula.atom 0

/-! ### Smoketests -/

#check FT_to_UCT_schedule
#check FT_to_UCT_height3_data
#check FT_to_UCT_height3_witness
#check FullTabulation
#check UnrestrictedChurchThesis
#check CantorDiagonal

end Papers.P4Meta.PartV