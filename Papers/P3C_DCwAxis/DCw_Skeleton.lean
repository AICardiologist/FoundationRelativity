import Papers.P3C_DCwAxis.DCw_Frontier_Interface

/-!
  Paper 3C: Proof skeleton for DCω → Baire.
  
  This file provides the waypoints for the classical proof via dependent choice
  on cylinders. Only substantive proof steps use `sorry` (allowed in 3C).
-/

namespace Papers.P3C.DCw

abbrev Seq := Nat → Nat

structure Cyl where
  stem : List Nat
deriving Repr, Inhabited

/-- A sequence lies in a cylinder if it agrees with its stem on all positions. -/
def Cyl.mem (C : Cyl) (x : Seq) : Prop :=
  ∀ i : Fin C.stem.length, x i = C.stem.get i

/-- Dense-open placeholder on cylinders (to be replaced by topology later). -/
structure DenseOpen where
  hit   : Cyl → Prop
  dense : ∀ C : Cyl, ∃ C' : Cyl, C'.stem.length ≥ C.stem.length ∧ hit C'
  open_like : True  -- placeholder

/-- One refinement step: extend by one symbol and meet some U n. -/
def stepR (U : Nat → DenseOpen) (C C' : Cyl) : Prop :=
  ∃ n a, C'.stem = C.stem ++ [a] ∧ (U n).hit C'

/-- "F is a chain" for U: every step refines. -/
def isChain (U : Nat → DenseOpen) (F : Nat → Cyl) : Prop :=
  ∀ n, stepR U (F n) (F (n+1))

/-- For each stage n and cylinder C, you can refine C by one symbol hitting U n. -/
theorem step_exists (U : Nat → DenseOpen) :
  ∀ (C : Cyl) (n : Nat), ∃ (C' : Cyl),
    C'.stem.length = C.stem.length + 1 ∧ (U n).hit C' := by
  -- TODO(3C): derive from (U n).dense; pick an extension of length+1 and show it hits.
  intro C n; sorry

/-- Build an infinite chain of refinements via DCω. -/
theorem chain_of_DCω (hDC : DCω) (U : Nat → DenseOpen) (C0 : Cyl) :
  ∃ F : Nat → Cyl, F 0 = C0 ∧ isChain U F := by
  -- TODO(3C): standard DCω on the relation "extend by one and hit U n".
  sorry

/-- Placeholder limit of a chain (real version: diagonalize the stems). -/
def limit_of_chain (_ : Nat → Cyl) : Seq :=
  fun _ => 0

/-- The limit realizes every finite stem in the chain. -/
theorem limit_mem (U : Nat → DenseOpen) {F : Nat → Cyl}
    (h0 : True) (hchain : isChain U F) :
    ∀ n, (F n).mem (limit_of_chain F) := by
  -- TODO(3C): prove by stem compatibility along the chain.
  intro n; sorry

end Papers.P3C.DCw