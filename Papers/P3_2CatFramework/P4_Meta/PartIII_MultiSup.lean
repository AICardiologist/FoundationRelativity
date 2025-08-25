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

/-! ### Axis independence (assumption surface for product heights) -/

/-- Independence placeholder stating that progress on `A` up to stage `n`
    does not already positively uniformize `B`, and conversely (symmetrically).
    This is deliberately abstract; concrete instances are supplied by model-theoretic arguments. -/
class AxisIndependent
    (T : Theory) (A B : Nat → Formula) : Prop

-- In later product-height lemmas, require `[AxisIndependent T A B]`.
-- Keep existing results intact; add new refined statements that assume independence.

/-! ### Fused steps (even/odd interleave)
    A simple, definitional interleave of two step streams.
    Even stages take from `A`, odd stages from `B`.
-/

/-- `fuseSteps A B` lists `A 0, B 0, A 1, B 1, …` by parity. -/
def fuseSteps (A B : Nat → Formula) (n : Nat) : Formula :=
  if n % 2 = 1 then B (n / 2) else A (n / 2)

@[simp] theorem fuseSteps_even (A B : Nat → Formula) (i : Nat) :
  fuseSteps A B (2 * i) = A i := by
  -- `2*i` is even, so `(2*i) % 2 = 0` and `(2*i) / 2 = i`
  simp [fuseSteps, Nat.mul_mod_right]

@[simp] theorem fuseSteps_odd (A B : Nat → Formula) (i : Nat) :
  fuseSteps A B (2 * i + 1) = B i := by
  -- `2*i+1` is odd, so `(2*i+1) % 2 = 1` and `(2*i+1) / 2 = i`
  simp only [fuseSteps]
  have h1 : (2 * i + 1) % 2 = 1 := by simp [Nat.add_mod, Nat.mul_mod_right]
  have h2 : (2 * i + 1) / 2 = i := by omega
  simp [h1, h2]

end Papers.P4Meta