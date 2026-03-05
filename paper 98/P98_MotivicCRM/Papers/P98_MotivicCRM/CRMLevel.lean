/-
  Paper 98: The Motivic CRM Architecture — CRM Hierarchy

  The constructive reverse mathematics hierarchy as a decidable total order.
-/

import Mathlib.Order.Lattice

/-! ## The CRM Hierarchy -/

/-- The constructive reverse mathematics hierarchy.
    Ordered by logical strength: BISH < MP < LLPO < WKL < WLPO < LPO < CLASS.

    BISH   = Bishop's constructive mathematics (intuitionistic + dependent choice)
    MP     = Markov's principle (¬¬∃ → ∃)
    LLPO   = Lesser limited principle of omniscience
    WKL    = Weak König's lemma (every infinite finitely branching tree has a path)
    WLPO   = Weak limited principle of omniscience (∀x:ℝ, x=0 ∨ ¬(x=0))
    LPO    = Limited principle of omniscience (∀f:ℕ→{0,1}, (∀n, f(n)=0) ∨ (∃n, f(n)=1))
    CLASS  = Full classical logic (LEM for all propositions) -/
inductive CRMLevel where
  | BISH  : CRMLevel
  | MP    : CRMLevel
  | LLPO  : CRMLevel
  | WKL   : CRMLevel
  | WLPO  : CRMLevel
  | LPO   : CRMLevel
  | CLASS : CRMLevel
  deriving Repr, DecidableEq, BEq

namespace CRMLevel

/-- The CRM hierarchy forms a total order. -/
def toNat : CRMLevel → Nat
  | BISH  => 0
  | MP    => 1
  | LLPO  => 2
  | WKL   => 3
  | WLPO  => 4
  | LPO   => 5
  | CLASS => 6

instance : LE CRMLevel where
  le a b := a.toNat ≤ b.toNat

instance : LT CRMLevel where
  lt a b := a.toNat < b.toNat

instance : DecidableRel (α := CRMLevel) (· ≤ ·) :=
  fun a b => Nat.decLe a.toNat b.toNat

instance : DecidableRel (α := CRMLevel) (· < ·) :=
  fun a b => Nat.decLt a.toNat b.toNat

/-- The join (max) of two CRM levels. -/
def join (a b : CRMLevel) : CRMLevel :=
  if a.toNat ≥ b.toNat then a else b

theorem bish_le_all (σ : CRMLevel) : BISH ≤ σ := by
  cases σ <;> decide

theorem all_le_class (σ : CRMLevel) : σ ≤ CLASS := by
  cases σ <;> decide

theorem join_bish_left (σ : CRMLevel) : join BISH σ = σ := by
  cases σ <;> rfl

theorem join_bish_right (σ : CRMLevel) : join σ BISH = σ := by
  cases σ <;> rfl

theorem join_self (σ : CRMLevel) : join σ σ = σ := by
  cases σ <;> rfl

/-- Folding join over a list of BISH values yields BISH. -/
theorem foldl_join_bish (l : List CRMLevel) (h : ∀ x ∈ l, x = BISH) :
    l.foldl join BISH = BISH := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl]
    have hx : x = BISH := h x (.head ..)
    subst hx
    rw [join_bish_left]
    exact ih (fun y hy => h y (.tail _ hy))

end CRMLevel

/-- A CRM signature records the logical strength required by a mathematical
    object, construction, or theorem. -/
structure CRMSignature where
  level : CRMLevel
  /-- Brief justification for the classification -/
  witness : String
  deriving Repr
