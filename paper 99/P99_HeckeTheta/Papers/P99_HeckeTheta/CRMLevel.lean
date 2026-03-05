/-
  Paper 99: The Hecke Theta Series Squeeze — CRM Hierarchy
  Reused from Papers 72–98 (stable across the series).
  Includes WKL as an independent level for the FLT classification.
-/

namespace P99

/-- The CRM logical strength hierarchy.
    WKL (Weak König's Lemma) is incomparable with WLPO over BISH,
    but we encode it between LLPO and WLPO for the total order used
    in CRM level computations. The incomparability is noted in the paper. -/
inductive CRMLevel : Type where
  | BISH    : CRMLevel   -- Bishop's constructive mathematics
  | BISH_MP : CRMLevel   -- BISH + Markov's Principle
  | LLPO    : CRMLevel   -- Limited Lesser Principle of Omniscience
  | WKL     : CRMLevel   -- Weak König's Lemma (compactness)
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
  | WKL     => 3
  | WLPO    => 4
  | LPO     => 5
  | CLASS   => 6

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

/-- WKL is strictly above BISH. -/
theorem wkl_gt_bish : WKL > BISH := by decide

/-- WKL is strictly below CLASS. -/
theorem wkl_lt_class : WKL < CLASS := by decide

/-- WKL is strictly below LPO. -/
theorem wkl_lt_lpo : WKL < LPO := by decide

/-- BISH join WKL = WKL. -/
theorem bish_join_wkl : CRMLevel.join BISH WKL = WKL := by native_decide

/-- Maximum of BISH and WKL is WKL. -/
theorem max_bish_wkl : CRMLevel.joinList [BISH, BISH, BISH, WKL, BISH] = WKL := by
  native_decide

end P99
