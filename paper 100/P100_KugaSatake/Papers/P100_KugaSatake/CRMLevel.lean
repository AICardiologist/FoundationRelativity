/-
  Paper 100: The Kuga-Satake Bifurcation — CRM Hierarchy
  Reused from Papers 72–99 (stable across the series).
-/

namespace P100

/-- The CRM logical strength hierarchy.
    BISH ⊂ BISH+MP ⊂ LLPO ⊂ WLPO ⊂ LPO ⊂ CLASS.
    This total order is the CRM level used for component classification. -/
inductive CRMLevel : Type where
  | BISH    : CRMLevel   -- Bishop's constructive mathematics
  | BISH_MP : CRMLevel   -- BISH + Markov's Principle
  | LLPO    : CRMLevel   -- Limited Lesser Principle of Omniscience
  | WLPO    : CRMLevel   -- Weak Limited Principle of Omniscience
  | LPO     : CRMLevel   -- Limited Principle of Omniscience
  | CLASS   : CRMLevel   -- Full classical logic
  deriving DecidableEq, Repr

open CRMLevel

/-- Numeric encoding for ordering. -/
def CRMLevel.toNat : CRMLevel → Nat
  | BISH    => 0
  | BISH_MP => 1
  | LLPO    => 2
  | WLPO    => 3
  | LPO     => 4
  | CLASS   => 5

instance : LE CRMLevel where
  le a b := a.toNat ≤ b.toNat

instance : LT CRMLevel where
  lt a b := a.toNat < b.toNat

instance (a b : CRMLevel) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toNat ≤ b.toNat))

instance (a b : CRMLevel) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toNat < b.toNat))

instance : BEq CRMLevel where
  beq a b := a.toNat == b.toNat

/-- Maximum of two CRM levels. -/
def CRMLevel.join (a b : CRMLevel) : CRMLevel :=
  if a.toNat ≥ b.toNat then a else b

/-- Maximum over a list of CRM levels. -/
def CRMLevel.joinList : List CRMLevel → CRMLevel
  | [] => BISH
  | [x] => x
  | x :: xs => x.join (joinList xs)

/-- CLASS is strictly above BISH. -/
theorem class_gt_bish : CLASS > BISH := by decide

/-- CLASS is strictly above WLPO. -/
theorem class_gt_wlpo : CLASS > WLPO := by decide

/-- BISH join CLASS = CLASS. -/
theorem bish_join_class : CRMLevel.join BISH CLASS = CLASS := by native_decide

end P100
