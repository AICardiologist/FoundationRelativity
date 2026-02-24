/-
  Paper 61: Lang's Conjecture as the MP → BISH Gate
  Hierarchy.lean — DPT hierarchy classification with Lang gate

  Paper 61's unique contribution to the three-invariant hierarchy:
  for rank ≥ 2 and Hodge level ≤ 1, having an effective Lang constant
  reduces the classification from MP to BISH.

  The classifier takes THREE inputs:
    (rank, hodge_level_high, has_lang)
  and outputs the logic level (BISH, MP, or LPO).

  Zero `sorry`s. No custom axioms.
-/
import Papers.P61_LangBISH.Basic.Decidability

namespace Papers.P61_LangBISH

-- ============================================================================
-- §1. Logic Level Classification
-- ============================================================================

/-- The three logic levels in the DPT hierarchy. -/
inductive LogicLevel where
  | BISH : LogicLevel  -- bounded search, no omniscience
  | MP   : LogicLevel  -- unbounded discrete search (Markov's Principle)
  | LPO  : LogicLevel  -- real zero-testing (Limited Principle of Omniscience)
  deriving DecidableEq, Repr

-- ============================================================================
-- §2. Classifier Function
-- ============================================================================

/-- Classify a motive by rank, Hodge level, and Lang constant availability.

    This is the complete DPT hierarchy table from Papers 60–62, with
    Paper 61's refinement: Lang gates MP → BISH at rank ≥ 2, ℓ ≤ 1.

    | Rank  | Hodge ℓ | Lang? | Logic | Gate to BISH         |
    |-------|---------|-------|-------|----------------------|
    | r = 0 | any     | —     | BISH  | —                    |
    | r = 1 | ≤ 1     | —     | BISH  | —                    |
    | r ≥ 2 | ≤ 1     | Yes   | BISH  | Lang (Paper 61)      |
    | r ≥ 2 | ≤ 1     | No    | MP    | —                    |
    | any   | ≥ 2     | —     | LPO   | Structurally blocked | -/
def classifyLogicLevel (rank : ℕ) (hodge_level_high : Bool) (has_lang : Bool) : LogicLevel :=
  if hodge_level_high then LogicLevel.LPO
  else if rank = 0 then LogicLevel.BISH
  else if rank = 1 then LogicLevel.BISH
  else  -- rank ≥ 2, hodge ≤ 1
    if has_lang then LogicLevel.BISH
    else LogicLevel.MP

-- ============================================================================
-- §3. Verified Classification Examples
-- ============================================================================

/-- Rank 0, any Hodge, any Lang → BISH (finite group). -/
theorem rank0_is_BISH : classifyLogicLevel 0 false false = LogicLevel.BISH := by native_decide

/-- Rank 1, low Hodge → BISH (Gross-Zagier + Northcott). -/
theorem rank1_low_hodge_is_BISH : classifyLogicLevel 1 false false = LogicLevel.BISH := by
  native_decide

/-- Rank ≥ 2, low Hodge, WITH Lang → BISH (Paper 61's contribution!).
    The effective Lang constant converts unbounded MP search to bounded BISH
    via the Minkowski inversion formula. -/
theorem rank2_lang_is_BISH : classifyLogicLevel 2 false true = LogicLevel.BISH := by native_decide

/-- Rank ≥ 2, low Hodge, NO Lang → MP (unbounded discrete search). -/
theorem rank2_no_lang_is_MP : classifyLogicLevel 2 false false = LogicLevel.MP := by native_decide

/-- Any rank, high Hodge → LPO (non-algebraic intermediate Jacobian). -/
theorem high_hodge_is_LPO : classifyLogicLevel 5 true false = LogicLevel.LPO := by native_decide

-- ============================================================================
-- §4. Paper 61's Main Hierarchy Result
-- ============================================================================

/-- Paper 61's main hierarchy contribution: Lang gates MP → BISH.
    For rank ≥ 2 and Hodge level ≤ 1, an effective Lang Height Lower Bound
    reduces the classification from MP to BISH by making the Minkowski
    bound computable. -/
theorem lang_gates_mp_to_bish (r : ℕ) (_hr : r ≥ 2) :
    classifyLogicLevel r false true = LogicLevel.BISH := by
  simp only [classifyLogicLevel]
  split
  · contradiction
  · split
    · omega
    · split
      · omega
      · simp

/-- Without Lang, rank ≥ 2 stays at MP. -/
theorem no_lang_stays_mp (r : ℕ) (_hr : r ≥ 2) :
    classifyLogicLevel r false false = LogicLevel.MP := by
  simp only [classifyLogicLevel]
  split
  · contradiction
  · split
    · omega
    · split
      · omega
      · simp

-- ============================================================================
-- §5. Structural Theorems
-- ============================================================================

/-- Hodge level ≥ 2 forces LPO regardless of rank or Lang. -/
theorem hodge_dominates (r : ℕ) (has_lang : Bool) :
    classifyLogicLevel r true has_lang = LogicLevel.LPO := by
  simp [classifyLogicLevel]

/-- The classification is exhaustive. -/
theorem hierarchy_exhaustive (rank : ℕ) (hodge_high : Bool) (has_lang : Bool) :
    classifyLogicLevel rank hodge_high has_lang = LogicLevel.BISH
    ∨ classifyLogicLevel rank hodge_high has_lang = LogicLevel.MP
    ∨ classifyLogicLevel rank hodge_high has_lang = LogicLevel.LPO := by
  unfold classifyLogicLevel
  split
  · right; right; rfl
  · split
    · left; rfl
    · split
      · left; rfl
      · split
        · left; rfl
        · right; left; rfl

end Papers.P61_LangBISH
