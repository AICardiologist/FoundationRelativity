/-
  Paper 87: The Omniscience Cost of the Hodge Condition
  Theorem D: The Shiga-Wolfart Boundary

  For abelian varieties defined over ℚ̄, the normalised period matrix has
  algebraic entries if and only if A has complex multiplication (CM type).

  This is the Shiga-Wolfart theorem (1995), built on Wüstholz's analytic
  subgroup theorem (1989). It provides the arithmetic boundary for
  BISH-decidability of the Hodge test over number fields.

  Consequence for the biconditional: over ℚ̄, the CM route to BISH
  (Theorem A, Route 1) is the UNIQUE route that works via algebraic
  period entries. The MT-group route (Route 2) is independent — it
  works by knowing the Hodge classes abstractly, not by computing
  with algebraic periods.

  Connection to Mumford-Tate conjecture: If MT = G_ℓ (the ℓ-adic
  monodromy group, which is computable), then Route 2 is always
  available for varieties over ℚ̄, making the uniform Hodge test BISH
  for all such varieties. The WLPO cost is then an artefact of the
  analytic presentation, not an intrinsic feature.

  References:
  - Shiga, H.; Wolfart, J. (1995): Criteria for complex multiplication
    and transcendence properties of automorphic functions.
  - Wüstholz, G. (1989): Algebraische Punkte auf analytischen
    Untergruppen algebraischer Gruppen.
  - Cohen, P. (1996): Humbert surfaces and transcendence properties
    of automorphic functions.
-/

import Papers.P87_HodgeCost.CRMLevel

namespace P87

/-! ## Shiga-Wolfart theorem (axiomatised)

  For abelian varieties over ℚ̄, the period matrix arithmetic is
  characterised by the CM property.
-/

/-- Abstract type representing an abelian variety defined over ℚ̄. -/
axiom AbelianVarietyOverQbar : Type

/-- Whether the normalised period matrix has algebraic entries. -/
axiom period_entries_algebraic : AbelianVarietyOverQbar → Prop

/-- Whether the variety has complex multiplication. -/
axiom has_CM : AbelianVarietyOverQbar → Prop

/-- The Shiga-Wolfart theorem: over ℚ̄, algebraic periods ↔ CM type.

  Forward (CM → algebraic periods): The Shimura-Taniyama formula
  constrains the period matrix to lie in a CM field extension of ℚ.

  Reverse (algebraic periods → CM): If all period entries are algebraic,
  Wüstholz's analytic subgroup theorem forces the abelian variety to
  have CM. This is because non-CM period matrices necessarily have
  transcendental entries (the periods satisfy no algebraic relations
  beyond those forced by the endomorphism ring). -/
axiom shiga_wolfart (A : AbelianVarietyOverQbar) :
    period_entries_algebraic A ↔ has_CM A

/-! ## Consequences for the CRM analysis -/

/-- Over ℚ̄, CM is necessary for algebraic period entries. -/
theorem cm_necessary_for_algebraic_periods (A : AbelianVarietyOverQbar)
    (h : period_entries_algebraic A) : has_CM A :=
  (shiga_wolfart A).mp h

/-- Over ℚ̄, CM is sufficient for algebraic period entries. -/
theorem cm_sufficient_for_algebraic_periods (A : AbelianVarietyOverQbar)
    (h : has_CM A) : period_entries_algebraic A :=
  (shiga_wolfart A).mpr h

/-! ## Connection to Mumford-Tate conjecture (stated as a remark)

  The Mumford-Tate conjecture asserts that for abelian varieties over ℚ̄,
  the Mumford-Tate group (analytic, determined by Hodge structure) equals
  the ℓ-adic monodromy group (algebraic, computable from Galois action).

  If true, Route 2 (known MT group → BISH) is always available:
  compute G_ℓ algebraically, read off the Hodge classes.

  We state this as a conditional: if MT = G_ℓ, then the uniform Hodge
  test is BISH for varieties over ℚ̄.
-/

/-- The Mumford-Tate group of A (analytic invariant). -/
axiom MT_group : AbelianVarietyOverQbar → Type

/-- The ℓ-adic monodromy group of A (algebraic invariant). -/
axiom ell_adic_group : AbelianVarietyOverQbar → Type

/-- The Mumford-Tate conjecture for A: MT(A) = G_ℓ(A). -/
axiom MT_equals_Gell : AbelianVarietyOverQbar → Prop

/-- Whether the Hodge classes of A are computable from G_ℓ. -/
axiom hodge_classes_computable_from_Gell : AbelianVarietyOverQbar → Prop

/-- If the MT conjecture holds for A, the Hodge classes are computable
    from the algebraic ℓ-adic data, making the Hodge test BISH. -/
axiom mt_conjecture_gives_computability (A : AbelianVarietyOverQbar) :
    MT_equals_Gell A → hodge_classes_computable_from_Gell A

end P87
