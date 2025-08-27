/-
  File: Papers/P3_2CatFramework/P4_Meta/ProductSharpness.lean

  Purpose: WP-C Sharpness from Independence (interface-level, no sorries)
  - Shows how to combine height certificates across orthogonal axes
  - Parametrized by two combinators:
      • height_mono : transports a certificate along an implication
      • height_and  : combines certificates for P and Q into one for (P ∧ Q)
  - Uses IndependenceRegistry just for tokens/axioms; proofs do not rely on them.
-/
import Papers.P3_2CatFramework.P4_Meta.Frontier_API
import Papers.P3_2CatFramework.P4_Meta.IndependenceRegistry

namespace Papers.P4Meta

section

variable {HeightCert : Prop → Prop}

/-- Transport along implication. Supplied by your framework. -/
variable (height_mono : ∀ {P Q}, (P → Q) → HeightCert P → HeightCert Q)

/-- Conjunction combiner. You can derive this from a product operator using
    `height_and_of_prod` (see Frontier_API.lean). -/
variable (height_and  : ∀ {P Q}, HeightCert P → HeightCert Q → HeightCert (P ∧ Q))

/-- Sharpness from orthogonality (interface-level).

    If `C` needs WLPO and `D` needs FT, then given height-1 certs for WLPO and FT,
    we obtain a height cert for `C ∧ D`.

    Note: the `Independent WLPO FT` argument documents the intended use
    (orthogonality), but the certificate composition itself only needs the two
    combinators above. -/
def sharp_product_of_indep
    {C D : Prop} {WLPO FT : Prop}
    (needs_W : WLPO → C) (needs_F : FT → D)
    (_h_indep : Independent WLPO FT)
    (hW : HeightCert WLPO) (hF : HeightCert FT) : HeightCert (C ∧ D) :=
  let hC : HeightCert C := height_mono needs_W hW
  let hD : HeightCert D := height_mono needs_F hF
  height_and hC hD

/-- Specialized example: combine Gap (from WLPO) with UCT (from FT). -/
theorem sharp_UCT_Gap_product
    (height_mono : ∀ {P Q}, (P → Q) → HeightCert P → HeightCert Q)
    (height_and  : ∀ {P Q}, HeightCert P → HeightCert Q → HeightCert (P ∧ Q))
    {Gap UCT : Prop}
    (gap_from_wlpo : WLPO → Gap)
    (uct_from_ft   : FT → UCT)
    (hW : HeightCert WLPO) (hF : HeightCert FT) :
    HeightCert (Gap ∧ UCT) :=
sharp_product_of_indep (HeightCert := HeightCert)
  height_mono height_and gap_from_wlpo uct_from_ft indep_WLPO_FT hW hF

/-- Triple product pattern across three axes WLPO, FT, and DCω. -/
theorem sharp_triple_product
    (height_mono : ∀ {P Q}, (P → Q) → HeightCert P → HeightCert Q)
    (height_and  : ∀ {P Q}, HeightCert P → HeightCert Q → HeightCert (P ∧ Q))
    {C D E : Prop}
    (needs_W : WLPO → C) (needs_F : FT → D) (needs_DC : DCw → E)
    (hW : HeightCert WLPO) (hF : HeightCert FT) (hDC : HeightCert DCw) :
    HeightCert (C ∧ D ∧ E) :=
by
  -- Combine C (from WLPO) and D (from FT)
  have hCD  : HeightCert (C ∧ D) :=
    sharp_product_of_indep (HeightCert := HeightCert)
      height_mono height_and needs_W needs_F indep_WLPO_FT hW hF
  -- Lift DCω to E
  have hE   : HeightCert E := height_mono needs_DC hDC
  -- Conjoin: (C ∧ D) ∧ E
  have hCDE : HeightCert ((C ∧ D) ∧ E) := height_and hCD hE
  -- Reassociate: ((C ∧ D) ∧ E) → (C ∧ (D ∧ E)) ≡ (C ∧ D ∧ E)
  exact height_mono (fun ⟨⟨c, d⟩, e⟩ => ⟨c, d, e⟩) hCDE

end
end Papers.P4Meta