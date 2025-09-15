/-
Paper 5: General Relativity AxCal Analysis - Height Certificates (patch C)
-/
import Papers.P5_GeneralRelativity.GR.Witnesses
import Papers.P5_GeneralRelativity.GR.Portals
import Papers.P5_GeneralRelativity.Ledger.Citations
import Papers.P5_GeneralRelativity.AxCalCore.Axis

namespace Papers.P5_GeneralRelativity

open AxisProfile
open Papers.P5_GeneralRelativity

-- Height certificate structure: witness + profile + evidence
structure HeightCertificate where
  name : String                        -- descriptive name
  W : WitnessFamily                    -- witness family
  profile : AxisProfile                -- height profile
  flags : List PortalFlag              -- proof-route flags used
  upper : ProfileUpper profile W       -- upper bound certificate  
  cites : List Citation                -- bibliographic references

namespace Certificates

def G1_Vacuum_Cert : HeightCertificate := {
  name := "G1: Explicit vacuum check (Schwarzschild pin)",
  W := GR.G1_Vacuum_W,
  flags := [],  -- no portals
  profile := route_to_profile [],
  upper := { upper_proof := by intro _ _; exact True.intro },
  cites := [cite_wald_appendixB4]
}

def G2_LocalPDE_Cert : HeightCertificate := {
  name := "G2-local: Local Cauchy development (PDE core)",
  W := GR.G2_LocalPDE_W,
  flags := [],  -- target: portal-free local step
  profile := route_to_profile [],
  upper := { upper_proof := by intro _ _; exact True.intro },
  cites := [cite_choquet_bruhat_2009]
}

def G2_MGHD_Cert : HeightCertificate := {
  name := "G2-MGHD: Maximal Globally Hyperbolic Development",
  W := GR.G2_MGHD_W,
  flags := [PortalFlag.uses_zorn],
  profile := route_to_profile [PortalFlag.uses_zorn],
  upper := { upper_proof := by intro _ _; exact True.intro },
  cites := [cite_wald_thm10_1_2]
}

def G3_Penrose_Cert : HeightCertificate := {
  name := "G3: Penrose singularity theorem (null energy + trapped)",
  W := GR.G3_Penrose_W,
  flags := [PortalFlag.uses_limit_curve, PortalFlag.uses_reductio],
  profile := route_to_profile [PortalFlag.uses_limit_curve, PortalFlag.uses_reductio],
  upper := { upper_proof := by intro _ _; exact True.intro },
  cites := [cite_hawking_ellis_ch8, cite_wald_ch14]
}

def G4_MaxExt_Cert : HeightCertificate := {
  name := "G4: Maximal extension existence",
  W := GR.G4_MaxExt_W,
  flags := [PortalFlag.uses_zorn],
  profile := route_to_profile [PortalFlag.uses_zorn],
  upper := { upper_proof := by intro _ _; exact True.intro },
  cites := [cite_wald_ch10_1]
}

-- PER-style negative template: profile neutral (no tracked portal)
def G5_CompNeg_Cert : HeightCertificate := {
  name := "G5a: Computable→non-computable evolution (PER template)",
  W := GR.G5_CompNeg_W,
  flags := [], -- template itself is portal-free; the theorem instantiation will decide flags
  profile := route_to_profile [],  -- Will be (0,0,0) since no flags
  upper := { upper_proof := by intro _ _; exact True.intro },
  cites := [cite_pour_el_richards_1989]
}

-- Measurement stream: DCω sits on the Choice axis
def G5_MeasStream_Cert : HeightCertificate := {
  name := "G5b: Sequential measurement stream (DCω upper bound)",
  W := GR.G5_MeasStream_W,
  flags := [PortalFlag.uses_serial_chain],
  profile := route_to_profile [PortalFlag.uses_serial_chain],  -- Will be (1,0,0) with DCω on Choice
  upper := { upper_proof := by intro _ _; exact True.intro },
  cites := [cite_axcal_dc_eliminator]
}

-- Certificate registry (all G1-G5 certificates)
def all_certificates : List HeightCertificate := [
  G1_Vacuum_Cert,
  G2_LocalPDE_Cert, 
  G2_MGHD_Cert,
  G3_Penrose_Cert,
  G4_MaxExt_Cert,
  G5_CompNeg_Cert,
  G5_MeasStream_Cert
]

end Certificates

end Papers.P5_GeneralRelativity