/-
  File: Papers/P3_2CatFramework/P4_Meta/IndependenceRegistry.lean
  
  Purpose: WP-C Independence Registry
  - Prop-level tokens recording orthogonality of principles
  - Standard independence assumptions (WLPO ⟂ FT, FT ⟂ DCω)
  - Zero sorries - these are axiomatized assumptions with paper citations
-/

namespace Papers.P4Meta

/-- Marker proposition: 'P and Q are independent/orthogonal' (paper-level citation). -/
inductive Independent (P Q : Prop) : Prop | mk : Independent P Q

/-- Symmetry is immediate for the marker. -/
theorem Independent.symm {P Q : Prop} : Independent P Q → Independent Q P :=
  fun _ => Independent.mk

/-- Axis tokens (or import your existing ones). -/
constant WLPO : Prop
constant FT   : Prop
constant DCw  : Prop

/-! ### Standard Independence Assumptions 

These are recorded as axioms, justified by paper citations to models.
In practice these would cite:
- WLPO ⟂ FT: Models of BISH + WLPO + ¬FT (e.g., recursive mathematics)
- FT ⟂ DCω: Models with FT but not DCω (e.g., certain topos models)
-/

/-- WLPO and FT are independent: there are models with either but not both.
    Citation: Fridman-Simpson, reverse mathematics separations. -/
axiom indep_WLPO_FT : Independent WLPO FT

/-- FT and DCω are independent: compactness doesn't imply dependent choice.
    Citation: Standard topos models (e.g., effective topos). -/
axiom indep_FT_DCw : Independent FT DCw

/-- WLPO and DCω are independent.
    Citation: Models of recursive analysis. -/
axiom indep_WLPO_DCw : Independent WLPO DCw

-- Note: If P ⟂ Q and Q ⟂ R, we can't automatically conclude P ⟂ R
-- (independence is not transitive).

end Papers.P4Meta