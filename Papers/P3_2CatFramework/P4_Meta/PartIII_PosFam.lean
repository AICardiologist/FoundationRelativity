/-
  Papers/P3_2CatFramework/P4_Meta/PartIII_PosFam.lean

  A lightweight "positive family" wrapper around height certificates
  that composes neatly with the Part III/IV machinery:
    • stage(fam) := max stage among its certificates
    • toOmega    : push every certificate to the ω-limit theory
    • toBag      : reuse the existing bag aggregator (for bookkeeping)
-/
import Papers.P3_2CatFramework.P4_Meta.PartIII_Certificates
import Papers.P3_2CatFramework.P4_Meta.PartIII_MultiSup
import Papers.P3_2CatFramework.P4_Meta.PartIV_Limit

namespace Papers.P4Meta

/-- A positive family is just a list of named height certificates. -/
abbrev PosFam (T : Theory) (step : Nat → Formula) :=
  List (Σ φ, HeightCertificate T step φ)

namespace PosFam
  variable {T : Theory} {step : Nat → Formula}

  /-- The "stage" of a family is the maximum certificate height. -/
  def stage (fam : PosFam T step) : Nat :=
    maxStageOfCerts fam

  @[simp] theorem stage_nil : stage ([] : PosFam T step) = 0 := rfl

  /-- Convert the family to a bag (for consolidated stage bookkeeping). -/
  def toBag (fam : PosFam T step) : HeightCertificateBag T step :=
    HeightCertificateBag.fromList fam

  /-- The bag's consolidated stage is definitionally the family stage. -/
  @[simp] theorem toBag_n (fam : PosFam T step) : (toBag fam).n = stage fam := rfl

  /-- Push every member of the family to the ω‑limit theory. -/
  def toOmega (fam : PosFam T step) :
      List (PSigma fun φ => (Extendω T step).Provable φ) :=
    fam.map (fun ⟨φ, c⟩ => PSigma.mk φ (certToOmega (T := T) (step := step) c))

  /-- Just the goal formulas carried by the family (no proofs). -/
  def goals (fam : PosFam T step) : List Formula :=
    fam.map (fun ⟨φ, _⟩ => φ)

  @[simp] theorem goals_nil : goals ([] : PosFam T step) = [] := rfl

end PosFam

end Papers.P4Meta