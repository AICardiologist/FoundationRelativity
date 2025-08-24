/-
  Papers/P3_2CatFramework/P4_Meta/PartIII_MultiSup.lean

  A simple N-ary aggregator for height certificates.
  Collects multiple certificates and computes their max stage.
-/
import Papers.P3_2CatFramework.P4_Meta.PartIII_Certificates
import Papers.P3_2CatFramework.P4_Meta.PartIII_ProductSup
import Papers.P3_2CatFramework.P4_Meta.Meta_Signature

namespace Papers.P4Meta

/-- Compute the max stage from a list of certificates. -/
def maxStageOfCerts
  {T : Theory} {step : Nat → Formula}
  (cs : List (Σ φ, HeightCertificate T step φ)) : Nat :=
cs.foldl (fun acc ⟨_, c⟩ => Nat.max acc c.n) 0

/-- Simple aggregation: just track the max stage needed. -/
structure HeightCertificateBag
  (T : Theory) (step : Nat → Formula) where
  n    : Nat
  note : String := ""

/-- Create a bag from a list of certificates at their max stage. -/
def HeightCertificateBag.fromList
  {T : Theory} {step : Nat → Formula}
  (cs : List (Σ φ, HeightCertificate T step φ)) :
  HeightCertificateBag T step :=
{ n := maxStageOfCerts cs
, note := s!"aggregated {cs.length} certificates at max stage"
}

/-- Combine two certificates into a pair at max stage (simplified). -/
def combineCertsSimple
  {T : Theory} {step : Nat → Formula} {φ ψ : Formula}
  (cφ : HeightCertificate T step φ)
  (cψ : HeightCertificate T step ψ) :
  HeightCertificatePair T step ⟨φ, ψ⟩ :=
combineCertificates cφ cψ

end Papers.P4Meta