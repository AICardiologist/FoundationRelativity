/-
  File: Papers/P3_2CatFramework/P4_Meta/WP_C_Sharpness_Sanity.lean
  
  Purpose: Zero-dependency smoke test for ProductSharpness composition
  - Tests that ProductSharpness composes as intended
  - Uses toy instantiation with HeightCert := id
  - Verifies combinators wire up correctly
-/

import Papers.P3_2CatFramework.P4_Meta.IndependenceRegistry
import Papers.P3_2CatFramework.P4_Meta.ProductSharpness

namespace Papers.P4Meta

-- Toy instantiation: use HeightCert := id (just for typechecking)
def HeightCert (P : Prop) := P

theorem height_mono_id {P Q} (h : P → Q) : HeightCert P → HeightCert Q := h
theorem height_and_id {P Q} : HeightCert P → HeightCert Q → HeightCert (P ∧ Q) :=
  fun p q => And.intro p q

-- Fake reductions (just witnesses to compose)
axiom Gap : Prop
axiom UCT : Prop
axiom gap_from_WLPO : WLPO → Gap
axiom uct_from_FT   : FT → UCT

-- Fake height-1 certificates
axiom wlpo_h1 : HeightCert WLPO
axiom ft_h1   : HeightCert FT

/-- Test that sharp_UCT_Gap_product composes correctly -/
example : HeightCert (Gap ∧ UCT) :=
  sharp_UCT_Gap_product (HeightCert := HeightCert)
    height_mono_id height_and_id gap_from_WLPO uct_from_FT wlpo_h1 ft_h1

/-- Test triple product composition -/
axiom Axiom1 : Prop
axiom Axiom2 : Prop
axiom Axiom3 : Prop
axiom axiom1_from_WLPO : WLPO → Axiom1
axiom axiom2_from_FT : FT → Axiom2
axiom axiom3_from_DCw : DCw → Axiom3
axiom dcw_h1 : HeightCert DCw

example : HeightCert (Axiom1 ∧ Axiom2 ∧ Axiom3) :=
  sharp_triple_product (HeightCert := HeightCert)
    height_mono_id height_and_id 
    axiom1_from_WLPO axiom2_from_FT axiom3_from_DCw
    wlpo_h1 ft_h1 dcw_h1

/-! ### Axiom Dependency Verification -/

#print axioms sharp_UCT_Gap_product
-- Should only show interface axioms (WLPO, FT, DCw, Independent, indep_WLPO_FT)

#print axioms sharp_triple_product  
-- Should only show interface axioms (WLPO, FT, DCw, Independent, indep_WLPO_FT, indep_FT_DCw, indep_WLPO_DCw)

end Papers.P4Meta