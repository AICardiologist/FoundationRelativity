import Mathlib.Tactic

/-!
# Paper 107: CRM Hierarchy with WKL

Extended CRM lattice for the Condensed GAGA prediction.
Adds WKL (Weak König's Lemma) and the join node WKL_WLPO
as nodes in the partial order.

The lattice is a PARTIAL order, not a total order:
  - WKL and WLPO are incomparable (neither implies the other)
  - Their join WKL ∨ WLPO is strictly weaker than LPO
  - LPO ↔ WLPO + MP (Markov's Principle), and WKL ⊬ MP

Hasse diagram:
         CLASS
           |
          LPO
           |
       WKL_WLPO        ← join of two incomparable elements
         / \
       WKL   WLPO
         \   /
         LLPO
           |
         BISH

More precisely: BISH ≤ LLPO ≤ WKL ≤ WKL_WLPO ≤ LPO ≤ CLASS
               BISH ≤ LLPO ≤ WLPO ≤ WKL_WLPO ≤ LPO ≤ CLASS
               WKL ∦ WLPO (incomparable)
               WKL_WLPO < LPO (strict: WKL does not imply MP)

References:
  - Simpson (2009), Subsystems of Second Order Arithmetic, §IV.
  - Ishihara (2006), Reverse mathematics in Bishop's constructive math.
  - Bridges-Richman (1987), LPO ↔ WLPO + MP.
-/

namespace Paper107

/-- CRM logical levels.
    Note: This is NOT a total order. WKL and WLPO are incomparable.
    WKL_WLPO is their join, strictly below LPO. -/
inductive CRMLevel where
  | BISH      -- Bishop's constructive mathematics
  | LLPO      -- Lesser Limited Principle of Omniscience
  | WKL       -- Weak König's Lemma (infinite paths in computably bounded trees)
  | WLPO      -- Weak Limited Principle of Omniscience
  | WKL_WLPO  -- Join of WKL and WLPO; strictly weaker than LPO (lacks MP)
  | LPO       -- Limited Principle of Omniscience (= WLPO + MP)
  | CLASS     -- Full classical logic (LEM)
  deriving DecidableEq, Repr

/-- Partial order on CRM levels.
    WKL and WLPO are INCOMPARABLE: neither ≤ the other.
    Their join WKL_WLPO sits strictly between {WKL, WLPO} and LPO. -/
instance : LE CRMLevel where
  le a b := match a, b with
    | .BISH, _ => True
    | .LLPO, .BISH => False
    | .LLPO, _ => True
    -- WKL: above BISH and LLPO, below WKL_WLPO/LPO/CLASS, NOT below WLPO
    | .WKL, .BISH | .WKL, .LLPO | .WKL, .WLPO => False
    | .WKL, _ => True  -- WKL ≤ WKL, WKL_WLPO, LPO, CLASS
    -- WLPO: above BISH and LLPO, below WKL_WLPO/LPO/CLASS, NOT below WKL
    | .WLPO, .BISH | .WLPO, .LLPO | .WLPO, .WKL => False
    | .WLPO, _ => True  -- WLPO ≤ WLPO, WKL_WLPO, LPO, CLASS
    -- WKL_WLPO: above WKL and WLPO, below LPO and CLASS
    | .WKL_WLPO, .BISH | .WKL_WLPO, .LLPO
    | .WKL_WLPO, .WKL | .WKL_WLPO, .WLPO => False
    | .WKL_WLPO, _ => True  -- WKL_WLPO ≤ WKL_WLPO, LPO, CLASS
    | .LPO, .CLASS | .LPO, .LPO => True
    | .LPO, _ => False
    | .CLASS, .CLASS => True
    | .CLASS, _ => False

instance (a b : CRMLevel) : Decidable (a ≤ b) := by
  cases a <;> cases b <;> simp [LE.le] <;> exact inferInstance

/-- Join (least upper bound) in the CRM lattice.
    Key: WKL ∨ WLPO = WKL_WLPO < LPO (NOT LPO).
    LPO requires MP (Markov's Principle) beyond WKL + WLPO. -/
def CRMLevel.join : CRMLevel → CRMLevel → CRMLevel
  | .CLASS, _ | _, .CLASS => .CLASS
  | .LPO, _ | _, .LPO => .LPO
  | .WKL_WLPO, _ | _, .WKL_WLPO => .WKL_WLPO
  | .WLPO, .WKL | .WKL, .WLPO => .WKL_WLPO  -- incomparable → join at WKL_WLPO
  | .WLPO, _ | _, .WLPO => .WLPO
  | .WKL, _ | _, .WKL => .WKL
  | .LLPO, _ | _, .LLPO => .LLPO
  | .BISH, .BISH => .BISH

/-- Join of a list of CRM levels. -/
def CRMLevel.joinList : List CRMLevel → CRMLevel
  | [] => .BISH
  | [x] => x
  | x :: xs => x.join (joinList xs)

-- ═══ Hierarchy verification ═══

-- Chains that DO hold
theorem bish_le_llpo : CRMLevel.BISH ≤ CRMLevel.LLPO := trivial
theorem llpo_le_wkl : CRMLevel.LLPO ≤ CRMLevel.WKL := trivial
theorem llpo_le_wlpo : CRMLevel.LLPO ≤ CRMLevel.WLPO := trivial
theorem wkl_le_wkl_wlpo : CRMLevel.WKL ≤ CRMLevel.WKL_WLPO := trivial
theorem wlpo_le_wkl_wlpo : CRMLevel.WLPO ≤ CRMLevel.WKL_WLPO := trivial
theorem wkl_wlpo_le_lpo : CRMLevel.WKL_WLPO ≤ CRMLevel.LPO := trivial
theorem wkl_le_lpo : CRMLevel.WKL ≤ CRMLevel.LPO := trivial
theorem wlpo_le_lpo : CRMLevel.WLPO ≤ CRMLevel.LPO := trivial
theorem lpo_le_class : CRMLevel.LPO ≤ CRMLevel.CLASS := trivial

-- WKL and WLPO are INCOMPARABLE
theorem wkl_not_le_wlpo : ¬(CRMLevel.WKL ≤ CRMLevel.WLPO) := by
  simp [LE.le]

theorem wlpo_not_le_wkl : ¬(CRMLevel.WLPO ≤ CRMLevel.WKL) := by
  simp [LE.le]

-- WKL_WLPO is strictly below LPO (LPO requires MP beyond WKL + WLPO)
theorem wkl_wlpo_not_ge_lpo : ¬(CRMLevel.LPO ≤ CRMLevel.WKL_WLPO) := by
  simp [LE.le]

-- The corrected join: WKL ∨ WLPO = WKL_WLPO (NOT LPO)
theorem wkl_join_wlpo : CRMLevel.WKL.join CRMLevel.WLPO = CRMLevel.WKL_WLPO := by rfl

-- Condensed GAGA prediction: join of BISH, WLPO, WKL = WKL_WLPO < LPO
theorem condensed_gaga_cost :
    CRMLevel.joinList [.BISH, .WLPO, .WKL] = CRMLevel.WKL_WLPO := by rfl

-- The overall RH cost: (WKL_WLPO) ∨ LPO = LPO (Deligne dominates)
theorem condensed_rh_cost :
    CRMLevel.joinList [.WKL_WLPO, .LPO] = CRMLevel.LPO := by rfl

-- Deligne's extension is the unique maximum: it strictly exceeds condensed GAGA
theorem deligne_dominates_condensed_gaga :
    CRMLevel.WKL_WLPO ≤ CRMLevel.LPO ∧ ¬(CRMLevel.LPO ≤ CRMLevel.WKL_WLPO) :=
  ⟨trivial, by simp [LE.le]⟩

end Paper107
