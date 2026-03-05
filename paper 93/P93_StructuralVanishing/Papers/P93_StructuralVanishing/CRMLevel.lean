/-
  Paper 93: The Structural Vanishing Theorem — CRM Hierarchy
  Reused from Papers 72–92 (stable across the series)
-/

namespace P93

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

/-- CLASS is strictly above BISH. -/
theorem class_gt_bish : CLASS > BISH := by decide

/-- WLPO is strictly above BISH. -/
theorem wlpo_gt_bish : WLPO > BISH := by decide

end P93
