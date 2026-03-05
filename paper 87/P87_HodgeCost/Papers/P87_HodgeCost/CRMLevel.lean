/-
  Paper 87: The Omniscience Cost of the Hodge Condition
  CRM Hierarchy — reused from Papers 72–74

  The constructive reverse mathematics hierarchy, ordered by logical strength.
  BISH < BISH_MP < LLPO < WLPO < LPO < CLASS
-/

namespace P87

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

/-- WLPO is strictly above BISH. -/
theorem wlpo_gt_bish : WLPO > BISH := by decide

/-- LPO is strictly above BISH. -/
theorem lpo_gt_bish : LPO > BISH := by decide

/-- WLPO ≠ BISH. -/
theorem wlpo_ne_bish : WLPO ≠ BISH := by decide

/-- LPO ≠ BISH. -/
theorem lpo_ne_bish : LPO ≠ BISH := by decide

end P87
