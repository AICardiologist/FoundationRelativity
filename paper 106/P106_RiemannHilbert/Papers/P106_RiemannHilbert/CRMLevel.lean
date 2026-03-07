import Mathlib.Tactic

/-!
# Paper 106: CRM Hierarchy

The constructive hierarchy used throughout the CRM series.
BISH ⊂ BISH+LLPO ⊂ BISH+WLPO ⊂ BISH+LPO ⊂ CLASS

Note: MP (Markov's Principle) is orthogonal to the WLPO/LPO chain.
The external AI incorrectly placed WLPO extending MP; they are incomparable.
-/

namespace Paper106

/-- CRM logical levels, ordered by strength. -/
inductive CRMLevel where
  | BISH    -- Bishop's constructive mathematics
  | LLPO    -- Lesser Limited Principle of Omniscience
  | WLPO    -- Weak Limited Principle of Omniscience
  | LPO     -- Limited Principle of Omniscience
  | CLASS   -- Full classical logic (LEM)
  deriving DecidableEq, Repr

instance : LE CRMLevel where
  le a b := match a, b with
    | .BISH, _ => True
    | .LLPO, .BISH => False
    | .LLPO, _ => True
    | .WLPO, .BISH | .WLPO, .LLPO => False
    | .WLPO, _ => True
    | .LPO, .CLASS | .LPO, .LPO => True
    | .LPO, _ => False
    | .CLASS, .CLASS => True
    | .CLASS, _ => False

instance : Ord CRMLevel where
  compare a b := match a, b with
    | .BISH, .BISH => .eq
    | .BISH, _ => .lt
    | _, .BISH => .gt
    | .LLPO, .LLPO => .eq
    | .LLPO, _ => .lt
    | _, .LLPO => .gt
    | .WLPO, .WLPO => .eq
    | .WLPO, _ => .lt
    | _, .WLPO => .gt
    | .LPO, .LPO => .eq
    | .LPO, _ => .lt
    | _, .LPO => .gt
    | .CLASS, .CLASS => .eq

instance (a b : CRMLevel) : Decidable (a ≤ b) := by
  cases a <;> cases b <;> simp [LE.le] <;> exact inferInstance

/-- Join (least upper bound) in the CRM lattice. -/
def CRMLevel.join : CRMLevel → CRMLevel → CRMLevel
  | .CLASS, _ | _, .CLASS => .CLASS
  | .LPO, _ | _, .LPO => .LPO
  | .WLPO, _ | _, .WLPO => .WLPO
  | .LLPO, _ | _, .LLPO => .LLPO
  | .BISH, .BISH => .BISH

/-- Join of a list of CRM levels. -/
def CRMLevel.joinList : List CRMLevel → CRMLevel
  | [] => .BISH
  | [x] => x
  | x :: xs => x.join (joinList xs)

-- Verify hierarchy
theorem bish_le_llpo : CRMLevel.BISH ≤ CRMLevel.LLPO := trivial
theorem llpo_le_wlpo : CRMLevel.LLPO ≤ CRMLevel.WLPO := trivial
theorem wlpo_le_lpo : CRMLevel.WLPO ≤ CRMLevel.LPO := trivial
theorem lpo_le_class : CRMLevel.LPO ≤ CRMLevel.CLASS := trivial

end Paper106
