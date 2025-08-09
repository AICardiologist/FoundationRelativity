/-
  Papers/P2_BidualGap/Constructive/DualStructure.lean

  BISH-aligned predicates describing when the *dual* (and hence the bidual)
  carries the constructive Banach structure we need for the equivalence.
  Prop-only (no global instances), universe-safe, and designed to be the
  target of WLPO → structure theorems.
-/
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Group.Completeness
import Papers.P2_BidualGap.Basic

namespace Papers.P2.Constructive
open Papers.P2

/-! ### Local constructive "operator norm" scaffolding

We keep these helpers in a local namespace and *Prop*-only, to avoid
typeclass/instance interactions. They give precise, verifiable targets
for the WLPO-powered arguments.
-/
namespace OpNorm

variable (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The *closed* unit ball of `X`. -/
def UnitBall : Set X := {x | ‖x‖ ≤ 1}

/-- The set of absolute values attained by `f` on the unit ball. -/
def valueSet (f : X →L[ℝ] ℝ) : Set ℝ :=
  { r | ∃ x, x ∈ UnitBall X ∧ ‖f x‖ = r }

lemma valueSet_nonempty (f : X →L[ℝ] ℝ) : (valueSet (X:=X) f).Nonempty := by
  refine ⟨0, ?_⟩
  refine ⟨0, ?_, ?_⟩
  · have : ‖(0 : X)‖ = 0 := norm_zero
    -- `‖0‖ ≤ 1`
    simpa [UnitBall, this] using (le_of_eq this)
  · simp

/-- If there is a uniform bound `C` on `‖f x‖` over the unit ball, then `valueSet f` is bounded above. -/
lemma valueSet_bddAbove_of_bound {f : X →L[ℝ] ℝ}
  (C : ℝ) (hC : ∀ x, ‖x‖ ≤ 1 → ‖f x‖ ≤ C) :
  BddAbove (valueSet (X:=X) f) := by
  refine ⟨C, ?_⟩
  intro r hr
  rcases hr with ⟨x, hx, rfl⟩
  exact hC x hx

/-- If `f` and `g` are normable (i.e., their value sets admit LUBs),
    then `valueSet (f+g)` is bounded above. -/
lemma valueSet_bddAbove_add
    (f g : X →L[ℝ] ℝ)
    (hLUBf : ∃ rf, IsLUB (valueSet (X:=X) f) rf)
    (hLUBg : ∃ rg, IsLUB (valueSet (X:=X) g) rg) :
    BddAbove (valueSet (X:=X) (f + g)) := by
  rcases hLUBf with ⟨rf, hf⟩
  rcases hLUBg with ⟨rg, hg⟩
  -- Every element of `valueSet (f+g)` is ≤ rf+rg
  refine ⟨rf + rg, ?_⟩
  intro r hr
  rcases hr with ⟨x, hx, rfl⟩
  -- `r = ‖(f+g) x‖`
  have : ‖(f + g) x‖ ≤ ‖f x‖ + ‖g x‖ := norm_add_le _ _
  refine this.trans ?_
  exact add_le_add (hf.1 ⟨x, hx, rfl⟩) (hg.1 ⟨x, hx, rfl⟩)

/-- Our constructive predicate that the operator norm *exists* for `f`.
    Implemented as "the LUB of `valueSet f` exists." -/
def HasOpNorm (f : X →L[ℝ] ℝ) : Prop :=
  ∃ r : ℝ, IsLUB (valueSet (X:=X) f) r

end OpNorm

open OpNorm

-- Bridge between the two HasOpNorm definitions
-- For now, we use Classical.choose to bridge them
-- TODO: implement proper equivalence proof
lemma hasOperatorNorm_to_hasOpNorm 
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (f : X →L[ℝ] ℝ) :
  HasOperatorNorm f → HasOpNorm (X:=X) f := by
  intro h
  -- For now, use Classical.choose to bridge the definitions
  classical
  use ‖f‖
  -- The proper proof shows these definitions are equivalent
  -- TODO: implement rigorous equivalence proof  
  sorry

lemma hasOpNorm_to_hasOperatorNorm
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (f : X →L[ℝ] ℝ) :
  HasOpNorm (X:=X) f → HasOperatorNorm f := by
  intro ⟨N, hN_lub⟩
  -- Use the LUB as the witness for HasOperatorNorm
  -- For now, simplify with sorry to get architecture working  
  use N, sorry, sorry, sorry

/-- WLPO supplies a LUB for the value set of a bounded functional image on the unit ball.
This is the *only* nontrivial constructive step needed to turn bounded+nonempty into a LUB. -/
theorem lub_exists_for_valueSet_of_WLPO
  (hWLPO : WLPO)
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  (h : X →L[ℝ] ℝ)
  (hBdd : BddAbove (OpNorm.valueSet (X:=X) h))
  (hNonempty : (OpNorm.valueSet (X:=X) h).Nonempty) :
  ∃ r, IsLUB (OpNorm.valueSet (X:=X) h) r := by
  -- TODO: Fill using your preferred WLPO argument (Ishihara/LLPO-style selection on a rational mesh,
  -- or the professor's cited result that WLPO yields suprema for located, bounded sets of this form).
  -- SORRY(P2-dual-LUB-exists-for-valueSet)
  sorry

/-- **Target (1)**: WLPO gives the *existence* of a LUB for `(f+g)` on the unit ball,
    assuming LUBs exist for `f` and `g`.  This is exactly what the "closed under addition"
    clause needs: normability of `f+g` from normability of `f` and `g`. -/
theorem add_IsLUB_of_WLPO
  (hWLPO : WLPO)
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  (f g : X →L[ℝ] ℝ)
  (hLUBf : ∃ rf, IsLUB (valueSet (X:=X) f) rf)
  (hLUBg : ∃ rg, IsLUB (valueSet (X:=X) g) rg) :
  ∃ r, IsLUB (valueSet (X:=X) (f + g)) r := by
  -- Easy parts: nonempty & bounded above
  have hNE : (OpNorm.valueSet (X:=X) (f + g)).Nonempty :=
    OpNorm.valueSet_nonempty (X:=X) (f + g)
  have hBdd : BddAbove (OpNorm.valueSet (X:=X) (f + g)) :=
    OpNorm.valueSet_bddAbove_add (X:=X) f g hLUBf hLUBg
  -- The WLPO hinge: turn (nonempty & bounded) into a LUB existence
  exact lub_exists_for_valueSet_of_WLPO hWLPO (f + g) hBdd hNE

-- TODO: Target (2) would be WLPO-based completeness for normable dual functionals
-- Currently using Prop-only placeholder in DualIsBanach structure

/-- **Main structural target (stub)**:
    *Given WLPO*, every real Banach space has a constructive-Banach dual.

    This is the keystone you marked "Priority 1". Fill this by showing:
    - If `f` and `g` are normable, then so is `f + g` (use WLPO to witness the norm).
    - The normable dual is complete (again, WLPO gives the supremum/limit existence you need).

    Tip: keep this theorem Prop-only. Do not introduce global instances. -/
theorem dual_is_banach_of_WLPO
  (hWLPO : WLPO) :
  ∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X],
    DualIsBanach X := by
  -- We implement this via two micro-lemmas below.
  intro X _ _ _
  refine
  { closed_add := ?closed,
    complete_normable_dual := ?complete }
  · -- closure under addition, reduced to existential `add_IsLUB_of_WLPO`
    intro f g hf hg
    -- Convert from Basic.lean HasOperatorNorm to OpNorm.HasOpNorm
    -- Use the bridge lemmas
    have hf_op : HasOpNorm (X:=X) f := hasOperatorNorm_to_hasOpNorm f hf
    have hg_op : HasOpNorm (X:=X) g := hasOperatorNorm_to_hasOpNorm g hg
    -- Now use the target lemma (existential LUB existence)
    rcases hf_op with ⟨rf, hLUBf⟩
    rcases hg_op with ⟨rg, hLUBg⟩
    obtain ⟨r, hLUBsum⟩ := add_IsLUB_of_WLPO hWLPO f g ⟨rf, hLUBf⟩ ⟨rg, hLUBg⟩
    -- Convert back to the Basic predicate:
    exact hasOpNorm_to_hasOperatorNorm (f + g) ⟨r, hLUBsum⟩
  case complete =>
    -- completeness of the normable dual, Prop-only placeholder
    trivial

/-- Helper for bidual gaps: if WLPO holds, both X and X* have constructive Banach duals. -/
theorem duals_banach_of_WLPO
  (hWLPO : WLPO)
  (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] :
  DualIsBanach X ∧ DualIsBanach (X →L[ℝ] ℝ) := by
  constructor
  · exact dual_is_banach_of_WLPO hWLPO X
  · exact dual_is_banach_of_WLPO hWLPO (X →L[ℝ] ℝ)

end Papers.P2.Constructive