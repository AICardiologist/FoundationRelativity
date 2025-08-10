/-
Papers/P2_BidualGap/Basics/FiniteCesaroTests.lean

Pin-safe smoke tests for the finite Cesàro averaging API.
These compile-time checks help catch future import/API drift.
-/
import Papers.P2_BidualGap.Basics.FiniteCesaro

open Papers.P2.Basics.FiniteCesaro

-- Quick "compile proves stability" checks; no heavy imports, no tactics required.

/-- Test avg_const with concrete value -/
example {n : ℕ} [NeZero n] : avg (fun _ : Fin n => (5 : ℝ)) = 5 := 
  avg_const (n := n) (5 : ℝ)

/-- Test avg_abs_bound inequality -/
example {n : ℕ} [NeZero n] (x : Fin n → ℝ) : |avg x| ≤ avg (fun i => |x i|) :=
  avg_abs_bound (n := n) x

/-- Test avg_zero simp lemma -/
example {n : ℕ} [NeZero n] : avg (fun _ : Fin n => (0 : ℝ)) = 0 :=
  avg_zero (n := n)

/-- Test oneVec calibration -/
example {n : ℕ} [NeZero n] : avg (oneVec : Fin n → ℝ) = 1 :=
  avg_oneVec (n := n)

/-- Test blueprint alias stability -/
example {n : ℕ} [NeZero n] (x : Fin n → ℝ) : |avg x| ≤ (1 / (n : ℝ)) * (Finset.sum (Finset.univ) (fun i => |x i|)) :=
  fn_basics_norm (n := n) x

/-- Test vanishing on sum = 0 -/
example {n : ℕ} [NeZero n] {x : Fin n → ℝ} (h : Finset.sum (Finset.univ) (fun i => x i) = 0) : avg x = 0 :=
  fn_basics_vanishing (n := n) h