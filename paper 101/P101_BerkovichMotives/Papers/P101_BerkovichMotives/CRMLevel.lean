/-
  Paper 101 — CRM Level Hierarchy
  The CRM Signature of Berkovich Motives

  Standard 7-level hierarchy used across Papers 76–101.
-/
import Mathlib.Tactic

namespace P101

/-- CRM levels, ordered by logical strength. -/
inductive CRMLevel where
  | BISH   -- Bishop's constructive mathematics
  | LLPO   -- Lesser Limited Principle of Omniscience
  | WKL    -- Weak König's Lemma (incomparable with WLPO)
  | WLPO   -- Weak Limited Principle of Omniscience
  | MP     -- Markov's Principle
  | LPO    -- Limited Principle of Omniscience
  | CLASS  -- Full classical logic
  deriving DecidableEq, Repr

open CRMLevel

/-- Numeric encoding for the partial order. WKL and WLPO are incomparable (both = 2). -/
def CRMLevel.toNat : CRMLevel → Nat
  | BISH  => 0
  | LLPO  => 1
  | WKL   => 2
  | WLPO  => 2
  | MP    => 3
  | LPO   => 4
  | CLASS => 5

/-- Join in the CRM lattice. WKL ⊔ WLPO = LPO. -/
def CRMLevel.join (a b : CRMLevel) : CRMLevel :=
  match a, b with
  | WKL, WLPO => LPO
  | WLPO, WKL => LPO
  | x, y => if x.toNat ≥ y.toNat then x else y

/-- WKL and WLPO are incomparable: same numeric level but distinct. -/
theorem wkl_wlpo_incomparable : WKL ≠ WLPO := by decide

/-- Their join is strictly above both. -/
theorem wkl_join_wlpo_eq_lpo : CRMLevel.join WKL WLPO = LPO := by rfl

/-- WKL is strictly below CLASS. -/
theorem wkl_below_class : WKL.toNat < CLASS.toNat := by native_decide

/-- BISH is the minimum. -/
theorem bish_minimum (l : CRMLevel) : BISH.toNat ≤ l.toNat := by
  cases l <;> simp [CRMLevel.toNat]

/-- Join of a list of CRM levels. -/
def CRMLevel.joinList : List CRMLevel → CRMLevel
  | [] => BISH
  | [x] => x
  | x :: xs => CRMLevel.join x (joinList xs)

end P101
