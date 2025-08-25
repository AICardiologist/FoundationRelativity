/-
  Papers/P4_Meta/Meta_UpperBounds.lean
  Lean upper bounds (sorry-free).
-/
import Papers.P3_2CatFramework.P4_Meta.Meta_Ladders

namespace Papers.P4Meta
open Papers.P4Meta

/-- Formulas with Lean proofs from Paper 3 axioms -/
structure LeanProvable (phi : Formula) where
  leanProof : Paper3Theory.Provable phi

/-- Mark formula as Lean-proved (placeholder registry). -/
def leanProved (phi : Formula) : Prop :=
  ∃ (_ : LeanProvable phi), True

/-- Upper bound: a Lean proof yields a Paper3Theory proof immediately. -/
theorem lean_implies_classical (phi : Formula) :
    leanProved phi → Paper3Theory.Provable phi :=
  fun ⟨lp, _⟩ => lp.leanProof

-- Collection of Lean-proved results from Paper 3 (illustrative stubs).
section LeanProvedResults
  def uniformization_product : Formula := Formula.atom 2
  def pins_refinement        : Formula := Formula.atom 3

  def uniformization_product_proved : LeanProvable uniformization_product :=
    ⟨trivial⟩

  def pins_refinement_proved : LeanProvable pins_refinement :=
    ⟨trivial⟩
end LeanProvedResults

/-- Height 0 for any Lean-proved formula. -/
theorem lean_height_zero (phi : Formula) :
    leanProved phi → ProofHeight Paper3Theory phi 0 :=
  fun h => ProofHeight.base (lean_implies_classical phi h)

-- Give `simp` a way to discharge `leanProved` for the two sample entries.
@[simp] theorem leanProved_uniformization_product :
  leanProved uniformization_product :=
  ⟨uniformization_product_proved, trivial⟩

@[simp] theorem leanProved_pins_refinement :
  leanProved pins_refinement :=
  ⟨pins_refinement_proved, trivial⟩

end Papers.P4Meta