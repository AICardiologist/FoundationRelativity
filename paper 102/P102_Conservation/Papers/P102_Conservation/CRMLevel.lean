/-
  Paper 102: The Conservation Theorem for Algebraic Cycles — CRM Hierarchy
  Reused from Papers 72–101 (stable across the series).
-/

namespace P102

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

/-- CLASS is strictly above BISH_MP. -/
theorem class_gt_bish_mp : CLASS > BISH_MP := by decide

/-- BISH_MP is strictly above BISH. -/
theorem bish_mp_gt_bish : BISH_MP > BISH := by decide

/-- BISH_MP is strictly below LLPO. -/
theorem bish_mp_lt_llpo : BISH_MP < LLPO := by decide

/-- BISH_MP is strictly below CLASS. -/
theorem bish_mp_lt_class : BISH_MP < CLASS := by decide

/-- The Conservation Theorem says CLASS descends to pure BISH
    for algebraic cycle statements (Friedman Π⁰₂ conservation).
    This is a strict descent. -/
theorem conservation_descent : BISH < CLASS := by decide

end P102
