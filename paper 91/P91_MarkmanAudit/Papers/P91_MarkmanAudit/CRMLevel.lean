/-
  Paper 91: The Logical Cost of Unconditional Hodge
  CRM Hierarchy — reused from Papers 72–74, 87

  The constructive reverse mathematics hierarchy, ordered by logical strength.
  BISH < BISH_MP < LLPO < WLPO < LPO < CLASS
-/

namespace P91

/-- The CRM logical strength hierarchy. -/
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

/-- CLASS is the highest level. -/
theorem class_ge_all (l : CRMLevel) : l ≤ CLASS := by
  cases l <;> decide

/-- BISH is the lowest level. -/
theorem bish_le_all (l : CRMLevel) : BISH ≤ l := by
  cases l <;> decide

/-- WLPO is strictly above BISH. -/
theorem wlpo_gt_bish : WLPO > BISH := by decide

/-- CLASS is strictly above WLPO. -/
theorem class_gt_wlpo : CLASS > WLPO := by decide

/-- CLASS ≠ BISH. -/
theorem class_ne_bish : CLASS ≠ BISH := by decide

end P91
