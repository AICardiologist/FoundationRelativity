/-
  Paper 87: The Omniscience Cost of the Hodge Condition
  Theorem C: The DPT Biconditional

  hodge_test_cost(state) = BISH ↔ state ≠ Bare_Analytic

  This is the Paper 87 biconditional in the same family as:
  - Paper 72: cycle_search_cost = BISH ↔ height is positive-definite
  - Paper 73: morphism_cost = BISH ↔ radical is detachable
  - Paper 74: eigenvalue_cost = BISH ↔ spectrum is algebraic
  - Paper 87: hodge_test_cost = BISH ↔ algebraic metadata available

  The common pattern: BISH-decidability of a mathematical operation is
  equivalent to an algebraic structural condition. Without the condition,
  the cost rises to WLPO or LPO.
-/

import Papers.P87_HodgeCost.CMDecidable

namespace P87

open CRMLevel MetadataState

/-! ## The biconditional: cost = BISH iff metadata available -/

/-- Theorem C: The Hodge test costs BISH if and only if algebraic metadata
    (CM type or known MT group) is available. Without metadata, the cost
    rises to WLPO. -/
theorem hodge_test_biconditional (state : MetadataState) :
    hodge_test_cost state = BISH ↔ state ≠ Bare_Analytic := by
  cases state with
  | CM_Known =>
    constructor
    · intro _; exact MetadataState.noConfusion
    · intro _; exact cm_gives_bish
  | MT_Known =>
    constructor
    · intro _; exact MetadataState.noConfusion
    · intro _; exact mt_gives_bish
  | Bare_Analytic =>
    constructor
    · intro h
      -- h : hodge_test_cost Bare_Analytic = BISH
      -- But hodge_test_cost Bare_Analytic = WLPO
      rw [bare_gives_wlpo] at h
      -- h : WLPO = BISH, contradiction
      exact absurd h wlpo_ne_bish
    · intro h
      -- h : Bare_Analytic ≠ Bare_Analytic, contradiction
      exact absurd rfl h

/-! ## Alternative formulation: cost = BISH iff metadata is CM or MT -/

/-- The metadata provides algebraic information about Hodge classes. -/
def has_algebraic_metadata : MetadataState → Bool
  | CM_Known      => true
  | MT_Known      => true
  | Bare_Analytic => false

/-- Equivalent biconditional using the boolean predicate. -/
theorem hodge_test_biconditional' (state : MetadataState) :
    hodge_test_cost state = BISH ↔ has_algebraic_metadata state = true := by
  cases state <;> simp [hodge_test_cost, has_algebraic_metadata,
    cm_hodge_cost_eq, mt_hodge_cost_eq, bare_hodge_cost_eq, wlpo_ne_bish]

/-! ## The DPT descent table for the Hodge condition

  | Metadata available | CRM cost | Mechanism               | Reference        |
  |--------------------|----------|-------------------------|------------------|
  | CM type (K, Φ)     | BISH     | Algebraic periods       | Shiga-Wolfart    |
  | MT group known     | BISH     | Hodge = G-invariants    | Moonen-Zarhin    |
  | Bare analytic      | WLPO     | Real equality test      | Bridges-Richman  |
-/

/-- The full characterisation theorem, paralleling Paper 72's dpt_characterisation. -/
theorem hodge_condition_characterisation :
    (hodge_test_cost CM_Known = BISH)
    ∧ (hodge_test_cost MT_Known = BISH)
    ∧ (hodge_test_cost Bare_Analytic = WLPO) :=
  ⟨cm_gives_bish, mt_gives_bish, bare_gives_wlpo⟩

end P87
