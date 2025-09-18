/-
  Papers/P3_2CatFramework/P4_Meta/FTc_MC_UCT.lean
  
  FTc + MC ↔ UCT equivalence for the revised CRM calibration in Paper 3A.
  
  ## CRM Context
  
  In constructive reverse mathematics:
  - FTc (Fan Theorem for decidable c-bars) alone does not imply UCT
  - MC (Majorized Choice) is needed for the equivalence
  - UCT ↔ FTc + MC over BISH
  - Under BD-N, some fan variants collapse (FTc → FAN_Π⁰₁)
  
  See Bridges & Diener (2007) for the pseudocompactness characterization
  
  Part of the CRM hygiene update for Paper 3A
-/

import Papers.P3_2CatFramework.P4_Meta.WKL_UCT

namespace Papers.P4Meta

/-- Fan Theorem for decidable c-bars (FTc) as a formula -/
def FTc : Formula := Formula.atom 403

/-- Majorized Choice (MC) as a formula -/
def MC : Formula := Formula.atom 404

/-- FAN_Π⁰₁ (bars that are Π⁰₁ with extension-closure) as a formula -/
def FAN_Pi01 : Formula := Formula.atom 405

/-- FAN_Δ (Dini-type fan theorem) as a formula -/
def FAN_Delta : Formula := Formula.atom 406

/-- BD-N (Bar Decidability for N) as a formula -/
def BDN : Formula := Formula.atom 407

/-- FTc + MC is equivalent to UCT over BISH -/
axiom FTc_plus_MC_iff_UCT :
  ∀ (T0 : Theory),
    (Extend (Extend T0 FTc) MC).Provable UCT ↔
    (Extend T0 UCT).Provable FTc ∧ (Extend T0 UCT).Provable MC

/-- Without MC, FTc alone does not entail UCT (currently) -/
axiom FTc_alone_not_UCT :
  ¬((Extend EmptyTheory FTc).Provable UCT)

/-- Fan variant hierarchy: FAN_Δ → FTc → FAN_Π⁰₁ -/
axiom fan_hierarchy :
  (Extend EmptyTheory FAN_Delta).Provable FTc ∧
  (Extend EmptyTheory FTc).Provable FAN_Pi01

/-- Under BD-N, FTc implies FAN_Π⁰₁ -/
axiom BDN_collapses_fans :
  (Extend (Extend EmptyTheory BDN) FTc).Provable FAN_Pi01

/-- UCT height on FTc+MC ladder is 1 (axiomatized) -/
axiom UCT_height_one_FTc_MC_axiom (T0 : Theory) :
    (ExtendIter T0 (fun n => if n = 0 then FTc else if n = 1 then MC else Formula.atom 999) 1).Provable UCT

/-- UCT height certificate on FTc+MC ladder -/
def UCT_height_one_FTc_MC (T0 : Theory) :
    HeightCertificate T0 (fun n => if n = 0 then FTc else if n = 1 then MC else Formula.atom 999) UCT :=
{ n := 1
, upper := UCT_height_one_FTc_MC_axiom T0
, note := "UCT provable from FTc+MC at height 1; not from FTc alone"
}

/-- Scope note for the CRM calibration -/
def FTc_MC_UCT_scope_note : String :=
  "All calibrations are over BISH (intuitionistic analysis) without BD-N or WKL. " ++
  "The equivalence UCT ↔ FTc+MC holds in this base theory. " ++
  "Admitting BD-N or WKL can collapse some heights as documented in Paper 3A."

/-- Independence registry entry -/
def independence_note : String :=
  "These are assumptions relative to BISH without BD-N. " ++
  "Model-theoretic separations are cited from literature, not re-proved here."

end Papers.P4Meta