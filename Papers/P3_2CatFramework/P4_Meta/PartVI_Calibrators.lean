/-
  Papers/P3_2CatFramework/P4_Meta/PartVI_Calibrators.lean
  Scaffolds for two analytic calibrators used in Part VI:
    • UCT@[0,1] witnessed under FT
    • Baire (pinned Polish) witnessed under DC_ω
  The mathematical payload is paper-backed; here we expose Lean-level calibrator constants
  and height certificates (as named axioms), so they compose with the P4_Meta machinery.
-/
import Papers.P3_2CatFramework.P4_Meta.PartIII_Certificates
import Papers.P3_2CatFramework.P4_Meta.PartIV_Limit
import Papers.P3_2CatFramework.P4_Meta.PartIII_PosFam

namespace Papers.P4Meta

/-! ### Calibrator constants (formulas) -/

/-- Fan Theorem (FT) – abstract as a formula. -/
def FT : Formula := Formula.atom 500
/-- Dependent Choice along ω (DC_ω) – abstract as a formula. -/
def DCω : Formula := Formula.atom 501

/-- UCT@[0,1] packaged as a single formula (pinned interval). -/
def UCT01 : Formula := Formula.atom 502
/-- Baire property for a pinned Polish space – abstracted as a single formula. -/
def BairePinned : Formula := Formula.atom 503

/-! ### Steps (ladders) that carry the calibrator axioms -/

/-- Ladder that reiterates `FT` as the step axiom (redundantly ok). -/
def ftSteps (_T : Theory) : Nat → Formula := fun _ => FT

/-- Ladder that reiterates `DCω` as the step axiom (redundantly ok). -/
def dcωSteps (_T : Theory) : Nat → Formula := fun _ => DCω

/-! ### Upper-bound certificates (paper-backed, named axioms)

  These encode the Lean-facing "upper bound" direction:
    FT  ⟹  UCT01
    DCω ⟹  BairePinned
  at some finite stage (the actual stage index is part of the certificate).
-/

/-- Certificate: FT yields UCT@[0,1] at some finite stage. -/
axiom uct_upper_from_FT_cert (T : Theory) :
  HeightCertificate T (ftSteps T) UCT01

/-- Certificate: DC_ω yields Baire for the pinned Polish space at some finite stage. -/
axiom baire_upper_from_DCω_cert (T : Theory) :
  HeightCertificate T (dcωSteps T) BairePinned

/-! ### Immediate corollaries at ω and ω+ε -/

@[simp] theorem UCT_at_omega (T : Theory) :
  (Extendω T (ftSteps T)).Provable UCT01 :=
  certToOmega (T := T) (step := ftSteps T) (c := uct_upper_from_FT_cert T)

@[simp] theorem UCT_at_omegaPlus (T : Theory) (ε : Nat) :
  (ExtendωPlus T (ftSteps T) ε).Provable UCT01 :=
  certToOmegaPlus (T := T) (step := ftSteps T) (ε := ε) (c := uct_upper_from_FT_cert T)

@[simp] theorem Baire_at_omega (T : Theory) :
  (Extendω T (dcωSteps T)).Provable BairePinned :=
  certToOmega (T := T) (step := dcωSteps T) (c := baire_upper_from_DCω_cert T)

@[simp] theorem Baire_at_omegaPlus (T : Theory) (ε : Nat) :
  (ExtendωPlus T (dcωSteps T) ε).Provable BairePinned :=
  certToOmegaPlus (T := T) (step := dcωSteps T) (ε := ε) (c := baire_upper_from_DCω_cert T)

/-! ### Tiny PosFam helpers -/

/-- A one-item positive family for the UCT certificate. -/
noncomputable def UCT_posFam (T : Theory) : PosFam T (ftSteps T) :=
  [⟨UCT01, uct_upper_from_FT_cert T⟩]

/-- A one-item positive family for the Baire certificate. -/
noncomputable def Baire_posFam (T : Theory) : PosFam T (dcωSteps T) :=
  [⟨BairePinned, baire_upper_from_DCω_cert T⟩]

end Papers.P4Meta