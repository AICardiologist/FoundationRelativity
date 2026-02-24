/-
  Paper 71: The Weight 1 Boundary
  Defs.lean: Infrastructure, constructive principles, and CRM hierarchy

  Defines the logical classification framework for the GL₂ Langlands
  program and the decidability descent mechanism.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.BooleanAlgebra

noncomputable section
open Classical

-- ============================================================
-- Constructive Principles
-- ============================================================

/-- Weak Limited Principle of Omniscience (zero-test on ℝ). -/
def WLPO : Prop :=
  ∀ (x : ℝ), x = 0 ∨ x ≠ 0

/-- Limited Principle of Omniscience (binary sequence). -/
def LPO : Prop :=
  ∀ (a : ℕ → Bool), (∀ n, a n = false) ∨ (∃ n, a n = true)

-- ============================================================
-- CRM Classification Levels
-- ============================================================

/-- Constructive strength levels for the GL₂ program. -/
inductive CRMLevel where
  | BISH    : CRMLevel   -- Pure constructive
  | WLPO    : CRMLevel   -- Requires WLPO (one atom)
  | LPO     : CRMLevel   -- Requires LPO
  | CLASS   : CRMLevel   -- Full classical logic
  deriving DecidableEq, Repr

/-- Ordering: BISH < WLPO < LPO < CLASS -/
instance : LE CRMLevel where
  le a b := match a, b with
    | .BISH, _ => True
    | .WLPO, .BISH => False
    | .WLPO, _ => True
    | .LPO, .BISH => False
    | .LPO, .WLPO => False
    | .LPO, _ => True
    | .CLASS, .CLASS => True
    | .CLASS, _ => False

instance : DecidableRel (α := CRMLevel) (· ≤ ·) :=
  fun a b => match a, b with
    | .BISH, _ => isTrue trivial
    | .WLPO, .BISH => isFalse (fun h => h)
    | .WLPO, .WLPO => isTrue trivial
    | .WLPO, .LPO => isTrue trivial
    | .WLPO, .CLASS => isTrue trivial
    | .LPO, .BISH => isFalse (fun h => h)
    | .LPO, .WLPO => isFalse (fun h => h)
    | .LPO, .LPO => isTrue trivial
    | .LPO, .CLASS => isTrue trivial
    | .CLASS, .BISH => isFalse (fun h => h)
    | .CLASS, .WLPO => isFalse (fun h => h)
    | .CLASS, .LPO => isFalse (fun h => h)
    | .CLASS, .CLASS => isTrue trivial

/-- Join (least upper bound) of two CRM levels. -/
def CRMLevel.join : CRMLevel → CRMLevel → CRMLevel
  | .CLASS, _ => .CLASS
  | _, .CLASS => .CLASS
  | .LPO, _ => .LPO
  | _, .LPO => .LPO
  | .WLPO, _ => .WLPO
  | _, .WLPO => .WLPO
  | .BISH, .BISH => .BISH

-- ============================================================
-- Proof Components of FLT via GL₂ Langlands
-- ============================================================

/-- Components of the GL₂ Langlands program relevant to FLT. -/
inductive FLTComponent where
  | dihedralModularity         : FLTComponent  -- Hecke theta series
  | tetrahedralBaseChange      : FLTComponent  -- GL₂ trace formula, wt 1
  | octahedralDescent          : FLTComponent  -- GL₂ trace formula, wt 1
  | jlIcosahedralTransfer      : FLTComponent  -- JL at weight ≥ 2
  | jlLevelLowering            : FLTComponent  -- JL comparison, weight ≥ 2
  | twPatchingShimura          : FLTComponent  -- Taylor-Wiles on Shimura curve
  | galoisRepEtale             : FLTComponent  -- Eichler-Shimura-Carayol
  | levelRaising               : FLTComponent  -- Ihara, supersingular locus
  | weightReduction            : FLTComponent  -- Hasse invariant, θ
  | serreRecipe                : FLTComponent  -- Finite group theory
  | potentialModularity        : FLTComponent  -- Moret-Bailly
  deriving DecidableEq, Repr

-- ============================================================
-- Weight Classification
-- ============================================================

/-- Weight regime: weight 1 vs weight ≥ 2.
    The weight 1 / weight ≥ 2 boundary is the logical fault line. -/
inductive WeightRegime where
  | weight1    : WeightRegime   -- Analytic territory (WLPO)
  | weightGe2  : WeightRegime   -- Algebraic territory (BISH)
  | any        : WeightRegime   -- Weight-independent
  deriving DecidableEq, Repr

-- ============================================================
-- Paper 70 vs Paper 71 WLPO Sources
-- ============================================================

/-- The three WLPO sources identified in Paper 70. -/
inductive Paper70WLPOSource where
  | langlandsTunnell     : Paper70WLPOSource  -- Base change at weight 1
  | jlIcosahedral        : Paper70WLPOSource  -- JL transfer (icosahedral)
  | jlLevelLoweringOverF : Paper70WLPOSource  -- JL comparison over F
  deriving DecidableEq, Repr

/-- Paper 71 status of each Paper 70 WLPO source. -/
inductive EliminationStatus where
  | irreducible : EliminationStatus  -- Cannot be eliminated
  | eliminated  : EliminationStatus  -- Reduced to BISH
  deriving DecidableEq, Repr

end
