/-
  Paper 87: The Omniscience Cost of the Hodge Condition
  Theorem A: CM Metadata → BISH

  When an abelian variety is equipped with CM type (K, Φ), the Hodge decomposition
  is algebraically determined: the period matrix has algebraic entries
  (Shiga-Wolfart 1995), and the Hodge projections reduce to K-linear algebra
  over ℚ. Testing whether a ℚ̄-number equals zero is decidable (polynomial GCD),
  hence BISH.

  When the Mumford-Tate group is known (including the generic case MT = Sp_{2g}),
  the Hodge classes are determined group-theoretically. For generic varieties,
  the only Hodge classes are Lefschetz classes — testing membership in the
  Lefschetz ring is combinatorial, hence BISH.

  References:
  - Shiga-Wolfart (1995): algebraic periods ↔ CM
  - Shimura (1971): CM period matrices and the Shimura-Taniyama formula
  - Moonen-Zarhin (1999): Hodge classes on generic abelian varieties = Lefschetz
  - Papers 79, 84-85: computational demonstrations of CM decidability
-/

import Papers.P87_HodgeCost.CRMLevel

namespace P87

open CRMLevel

/-! ## Algebraic metadata: what makes the Hodge test BISH-decidable

  There are two independent routes to BISH-decidability:

  Route 1 (CM type): The CM type (K, Φ) algebraises the period matrix.
    Period entries become algebraic numbers. Hodge projections are exact
    K-linear algebra. Zero-testing over ℚ̄ is decidable.

  Route 2 (Known MT group): If the Mumford-Tate group G is known, the
    Hodge classes are the G-invariants of ∧^{2p} H¹. Computing invariants
    of a known algebraic group acting on a known rational vector space
    is linear algebra over ℚ, hence BISH.

    Special case: for generic varieties, MT = Sp_{2g}, and the invariants
    are exactly the Lefschetz classes. Testing "is α a polynomial in the
    polarisation class?" is combinatorial.

  Route 3 (absent): No algebraic metadata. The period matrix is presented
    as Cauchy sequences. Testing projections requires real-number equality,
    hence WLPO (Theorem B in HodgeTest.lean).
-/

/-- The available algebraic metadata for a Hodge test. -/
inductive MetadataState : Type where
  | CM_Known       : MetadataState   -- CM type provided
  | MT_Known       : MetadataState   -- Mumford-Tate group known (includes generic)
  | Bare_Analytic  : MetadataState   -- Only Cauchy sequence data
  deriving DecidableEq, Repr

open MetadataState

/-! ## Axiomatised cost values

  Following the Paper 72 pattern: opaque constants + equality axioms.
  Each route to decidability is axiomatised with its CRM cost.
-/

/-- The CRM cost of the Hodge test when CM type is provided.
    Mathematical content: Shiga-Wolfart gives algebraic periods;
    K-linear algebra over ℚ is BISH. -/
axiom cm_hodge_cost : CRMLevel

/-- CM metadata reduces the Hodge test to algebraic arithmetic. -/
axiom cm_hodge_cost_eq : cm_hodge_cost = BISH

/-- The CRM cost of the Hodge test when the MT group is known.
    Mathematical content: Hodge classes = G-invariants of ∧^{2p} H¹;
    invariant computation is linear algebra over ℚ. -/
axiom mt_hodge_cost : CRMLevel

/-- Known MT group reduces the Hodge test to rational linear algebra. -/
axiom mt_hodge_cost_eq : mt_hodge_cost = BISH

/-- The CRM cost of the uniform Hodge test without algebraic metadata.
    Mathematical content: testing real-number equality requires WLPO
    (Bridges-Richman 1987). The embedding reduction (HodgeTest.lean)
    proves this is exact. -/
axiom bare_hodge_cost : CRMLevel

/-- Without metadata, the Hodge test requires WLPO. -/
axiom bare_hodge_cost_eq : bare_hodge_cost = WLPO

/-! ## Assembly function: metadata → cost -/

/-- The CRM cost of the Hodge test as a function of available metadata. -/
noncomputable def hodge_test_cost : MetadataState → CRMLevel
  | CM_Known      => cm_hodge_cost
  | MT_Known      => mt_hodge_cost
  | Bare_Analytic => bare_hodge_cost

/-! ## Theorem A: Algebraic metadata → BISH -/

/-- CM metadata gives BISH-decidability. -/
theorem cm_gives_bish : hodge_test_cost CM_Known = BISH := by
  unfold hodge_test_cost
  exact cm_hodge_cost_eq

/-- Known MT group gives BISH-decidability. -/
theorem mt_gives_bish : hodge_test_cost MT_Known = BISH := by
  unfold hodge_test_cost
  exact mt_hodge_cost_eq

/-- Bare analytic data gives WLPO cost. -/
theorem bare_gives_wlpo : hodge_test_cost Bare_Analytic = WLPO := by
  unfold hodge_test_cost
  exact bare_hodge_cost_eq

end P87
