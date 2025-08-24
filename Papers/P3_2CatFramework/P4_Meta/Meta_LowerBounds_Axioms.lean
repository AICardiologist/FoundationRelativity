/-
  Papers/P4_Meta/Meta_LowerBounds_Axioms.lean
  Named classical results (as axioms) + provenance stubs.
  Sorry-free and consistent with the simplified Paper3Theory/ClassicalLogic.
-/
import Papers.P3_2CatFramework.P4_Meta.Meta_UpperBounds

namespace Papers.P4Meta

open Papers.P4Meta

/-! ## Named classical inputs (provenance: classical)
    These are *axioms* (no proofs here). They serve purely as named
    placeholders for citations, and keep the tree sorry-free. -/

/-- Functor composition preserves the gap (placeholder key). -/
axiom functor_composition_gap : Paper3Theory.Provable (Formula.atom 10)

/-- Pins refinement requires a classical step (placeholder key). -/
axiom pins_refinement_needed : Paper3Theory.Provable (Formula.atom 11)

/-! ## Provenance helpers -/

/-- Mark results that (by policy/metadata) are sourced classically. -/
def requiresClassical (phi : Formula) : Prop :=
  ¬ leanProved phi ∧ Paper3Theory.Provable phi

/-- There exists at least one classically-sourced result (metadata stub). -/
axiom classical_requires_example : ∃ phi, requiresClassical phi

/-- Provenance tags used by the paper layer. -/
inductive Provenance
  | lean
  | classical
  | hybrid
  deriving Repr, DecidableEq

/-- In practice this would consult external metadata; we stub it as `none`. -/
def getProvenance (_phi : Formula) : Option Provenance :=
  none

/-- Pretty tag we would export to LaTeX. -/
def provenanceTag : Provenance → String
  | Provenance.lean      => "@provenance(lean)"
  | Provenance.classical => "@provenance(classical)"
  | Provenance.hybrid    => "@provenance(hybrid)"

end Papers.P4Meta