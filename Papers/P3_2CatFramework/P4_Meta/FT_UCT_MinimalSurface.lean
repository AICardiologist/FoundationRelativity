/-
  Papers/P3_2CatFramework/P4_Meta/FT_UCT_MinimalSurface.lean
  
  Minimal infrastructure for the FT/UCT axis in Paper 3A.
  This provides just enough Lean surface to reference the FT axis 
  placement and UCT calibration in the paper.
  
  Part of Workstream C from ROADMAP.md
-/

import Papers.P3_2CatFramework.P4_Meta.PartIII_Ladders

namespace Papers.P4Meta

/-- The empty theory (proves nothing) -/
def EmptyTheory : Theory :=
  { Provable := fun _ => False }

/-! ## FT/UCT Axis Minimal Infrastructure

This section provides the minimal Lean symbols needed to reference
the Fan Theorem (FT) axis and Uniform Continuity Theorem (UCT) 
placement in Paper 3A's AxCal framework.
-/

/-- Fan Theorem axiom (constructive version) as a formula -/
def FT : Formula := Formula.atom 400

/-- Uniform Continuity Theorem for [0,1] as a formula -/
def UCT : Formula := Formula.atom 401

/-- Steps for the FT ladder: add FT at step 0, irrelevant fillers after -/
def ftSteps (_T0 : Theory) : Nat → Formula
  | 0 => FT
  | _ => Formula.atom 499  -- irrelevant filler

/-- Upper bound: at stage 1 we have UCT (via FT→UCT reduction).
    For 3A we postulate this as an axiom; the constructive proof lives in WP-B. -/
axiom uct_upper_one (T0 : Theory) :
  (ExtendIter T0 (ftSteps T0) 1).Provable UCT

/-- Height certificate: UCT at height ≤ 1 along ftSteps -/
def uct_height1_cert (T0 : Theory) :
    HeightCertificate T0 (ftSteps T0) UCT :=
{ n := 1
, upper := uct_upper_one T0
, note := "Upper: FT→UCT reduction. Lower: BISH ⊬ UCT (model-theoretic)."
}

/-! ### Orthogonality to WLPO Axis

Key insight: FT and WLPO are orthogonal logical principles.
Neither implies the other constructively.
-/

-- WLPO is already defined in PartIII_Ladders as Formula.atom 311

/-- FT does not imply WLPO (constructively) -/
axiom FT_not_implies_WLPO : ¬((Extend EmptyTheory FT).Provable WLPO)

/-- WLPO does not imply FT (constructively) -/
axiom WLPO_not_implies_FT : ¬((Extend EmptyTheory WLPO).Provable FT)

/-! ### Profile Placement

For Paper 3A, we establish UCT's profile in the AxCal framework:
- Height 1 on FT axis
- Height ω on WLPO axis (not provable from WLPO alone)
-/

/-- Represents axiom profiles in the two-axis system -/
structure AxCalProfile where
  theAxiom : Formula
  ftHeight : Nat  -- Height on FT axis (1 for UCT)
  wlpoHeightIsOmega : Bool  -- True if height is ω on WLPO axis

/-- UCT's calibration profile -/
def UCT_profile : AxCalProfile := {
  theAxiom := UCT
  ftHeight := 1  -- Provable from FT at height 1
  wlpoHeightIsOmega := true  -- Not provable from WLPO at any finite height
}

/-! ## Sanity Tests -/

section SanityTests

/-- Test that UCT has height 1 certificate on FT axis -/
example (T0 : Theory) : (uct_height1_cert T0).n = 1 := rfl

/-- Test that UCT profile can be referenced -/
example : UCT_profile.ftHeight = 1 := rfl
example : UCT_profile.wlpoHeightIsOmega = true := rfl

/-- Test that orthogonality axioms compile -/
example : ¬((Extend EmptyTheory FT).Provable WLPO) := FT_not_implies_WLPO
example : ¬((Extend EmptyTheory WLPO).Provable FT) := WLPO_not_implies_FT

end SanityTests

end Papers.P4Meta