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

namespace Cyl
  /-- Extend a cylinder by one symbol. -/
  def extend (C : Cyl) (a : Nat) : Cyl := ⟨C.stem ++ [a]⟩

  @[simp] theorem extend_stem (C : Cyl) (a : Nat) :
      (C.extend a).stem = C.stem ++ [a] := rfl

  @[simp] theorem extend_length (C : Cyl) (a : Nat) :
      (C.extend a).stem.length = C.stem.length + 1 := by simp

end Cyl

/-- A sequence lies in a cylinder if it agrees with its stem on all positions. -/
def Cyl.mem (C : Cyl) (x : Seq) : Prop :=
  ∀ i : Fin C.stem.length, x i = C.stem.get i

/-- Dense-open placeholder on cylinders (to be replaced by topology later). -/
structure DenseOpen where
  hit   : Cyl → Prop
  dense : ∀ C : Cyl, ∃ C' : Cyl, C'.stem.length ≥ C.stem.length ∧ hit C'
  open_like : True  -- placeholder

/-- Stage-indexed refinement: at stage `n`, extend by one symbol and meet `U n`. -/
def stepRAt (U : Nat → DenseOpen) (n : Nat) (C C' : Cyl) : Prop :=
  ∃ a, C'.stem = C.stem ++ [a] ∧ (U n).hit C'

/-- "F is an indexed chain": the (n+1)-th cylinder refines the n-th meeting `U n`. -/
def isChainAt (U : Nat → DenseOpen) (F : Nat → Cyl) : Prop :=
  ∀ n, stepRAt U n (F n) (F (n+1))

/-- For each stage `n` and cylinder `C`, refine by one symbol hitting `U n`. -/
theorem step_exists (U : Nat → DenseOpen) :
  ∀ (C : Cyl) (n : Nat), ∃ (C' : Cyl),
    ∃ a, C'.stem = C.stem ++ [a] ∧ (U n).hit C' := by
  -- TODO(3C): derive from (U n).dense, then pick an exact one-symbol extension.
  intro C n; sorry

/-- DCω state for the construction: stage counter paired with a cylinder. -/
structure State where
  n : Nat
  C : Cyl

/-- The DCω relation: go from `(n,C)` to `(n+1,C')` forcing `stepRAt U n C C'`. -/
def R (U : Nat → DenseOpen) (s s' : State) : Prop :=
  s'.n = s.n + 1 ∧ stepRAt U s.n s.C s'.C

/-- Totality of `R` from any state, delegated to `step_exists`. -/
theorem R_total (U : Nat → DenseOpen) :
  ∀ s : State, ∃ s' : State, R U s s' := by
  intro s
  -- Use `step_exists` at stage `s.n`
  rcases step_exists U s.C s.n with ⟨C', a, hEq, hHit⟩
  refine ⟨⟨s.n + 1, C'⟩, ?_⟩
  exact ⟨rfl, ⟨a, hEq, hHit⟩⟩

/-- Build an infinite indexed chain of refinements via DCω. -/
theorem chain_of_DCω (hDC : DCω) (U : Nat → DenseOpen) (C0 : Cyl) :
  ∃ F : Nat → Cyl, F 0 = C0 ∧ isChainAt U F := by
  /-
  Use DCω on the state `State := Nat × Cyl` with relation
    R (n,C) (n',C') :↔ n' = n+1 ∧ stepRAt U n C C'.
  Totality of `R` at every state follows from `step_exists`.
  Then set `F n := (f n).2` for the DCω witness `f : Nat → State`.
  -/
  sorry

/-- Placeholder limit of a chain (real version: diagonalize the stems). -/
def limit_of_chain (_ : Nat → Cyl) : Seq :=
  fun _ => 0

/-- The limit realizes every finite stem in the chain. -/
theorem limit_mem (U : Nat → DenseOpen) {F : Nat → Cyl}
    (h0 : True) (hchain : isChainAt U F) :
    ∀ n, (F n).mem (limit_of_chain F) := by
  -- TODO(3C): prove by stem compatibility along the chain.
  intro n; sorry

-- Helper lemmas for finishing the proof later

theorem step_length_succ {U : Nat → DenseOpen} {n : Nat} {C C' : Cyl} :
  stepRAt U n C C' → C'.stem.length = C.stem.length + 1 := by
  intro h; rcases h with ⟨a, hEq, _⟩; simp [hEq]

theorem step_prefix {C C' : Cyl} {a : Nat} :
  C'.stem = C.stem ++ [a] → C'.stem.take C.stem.length = C.stem := by
  intro h; simp [h]

@[simp] theorem mem_nil (x : Seq) : (⟨[]⟩ : Cyl).mem x := by
  intro i; exact Fin.elim0 i

end Papers.P3C.DCw