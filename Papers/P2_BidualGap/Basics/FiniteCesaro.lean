/-
Papers/P2_BidualGap/Basics/FiniteCesaro.lean

Paper §2: finite‑dimensional surrogates
(a) norm bound for the averaging functional (via ℓ¹ on Fin n)
(b) vanishing on the zero‑sum subspace
(c) calibration at 1ₙ

Design: stick to `Fin n → ℝ`, `Finset.sum`, and abs/triangle inequality.
No CLMs, no `∑` binder, no fragile imports.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas

namespace Papers.P2.Basics.FiniteCesaro

-- Triangle inequality for finite sums (file-local helper)
private lemma abs_sum_le_sum_abs'
    {n : ℕ} (s : Finset (Fin n)) (f : Fin n → ℝ) :
    |Finset.sum s f| ≤ Finset.sum s (fun i => |f i|) := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha ih
    have h1 : |f a + Finset.sum s f| ≤ |f a| + |Finset.sum s f| := by
      simpa using abs_add (f a) (Finset.sum s f)
    have h2 : |Finset.sum s f| ≤ Finset.sum s (fun i => |f i|) := ih
    have h3 : |f a| + |Finset.sum s f|
              ≤ |f a| + Finset.sum s (fun i => |f i|) :=
      add_le_add_left h2 _
    have : |f a + Finset.sum s f|
           ≤ |f a| + Finset.sum s (fun i => |f i|) := le_trans h1 h3
    simpa [Finset.sum_insert, ha, add_comm, add_left_comm, add_assoc] using this

variable {n : ℕ} [NeZero n]

-- average on Fin n (function style, not `s.sum`)
noncomputable def avg (x : Fin n → ℝ) : ℝ := (Finset.sum (Finset.univ) (fun i => x i)) / (n : ℝ)

-- all‑ones vector
def oneVec : Fin n → ℝ := fun _ => 1

-- Helper: n > 0 as a real number (used throughout for division safety)
private lemma n_pos_real : 0 < (n : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)

/-- (a) Triangle‑inequality bound: `|avg x| ≤ (1/(n:ℝ)) * ∑ i, |x i|`. -/
lemma avg_l1_bound (x : Fin n → ℝ) :
    |avg x| ≤ (1 / (n : ℝ)) * (Finset.sum (Finset.univ) (fun i => |x i|)) := by
  classical
  have hn : 0 < (n : ℝ) := n_pos_real
  -- `|avg| = |sum| / n = |sum| * (1/n)`
  have h0 : |avg x|
          = |Finset.sum (Finset.univ) (fun i => x i)| * (1 / (n : ℝ)) := by
    have : |(Finset.sum (Finset.univ) (fun i => x i)) / (n : ℝ)|
         = |Finset.sum (Finset.univ) (fun i => x i)| / (n : ℝ) := by
      simp [abs_div, abs_of_pos hn]
    simpa [avg, this, div_eq_mul_inv, mul_comm]
  -- triangle on sums, then multiply both sides by (1/n) ≥ 0
  have tri : |Finset.sum (Finset.univ) (fun i => x i)|
           ≤  Finset.sum (Finset.univ) (fun i => |x i|) :=
    abs_sum_le_sum_abs' (Finset.univ) (fun i => x i)
  have : |Finset.sum (Finset.univ) (fun i => x i)| * (1 / (n : ℝ))
       ≤  Finset.sum (Finset.univ) (fun i => |x i|) * (1 / (n : ℝ)) :=
    mul_le_mul_of_nonneg_right tri (by 
      rw [one_div]
      exact inv_nonneg.mpr (le_of_lt hn))
  simpa [h0, mul_comm, mul_left_comm, mul_assoc]

/-- (b) Vanishing on `sum = 0`. -/
lemma avg_vanish_of_sum_zero {x : Fin n → ℝ}
    (h : Finset.sum (Finset.univ) (fun i => x i) = 0) : avg x = 0 := by
  have : (n : ℝ) ≠ 0 := ne_of_gt n_pos_real
  simp [avg, h]

/-- A convenient rephrase of `avg_l1_bound`: the absolute average is bounded
    by the average of absolute values. -/
lemma avg_abs_bound (x : Fin n → ℝ) : |avg x| ≤ avg (fun i => |x i|) := by
  simpa [avg, div_eq_mul_inv, mul_comm] using (avg_l1_bound (n := n) x)

/-- **Generalized calibration**: Average of a constant vector is the constant. -/
@[simp] lemma avg_const (c : ℝ) : avg (fun _ : Fin n => c) = c := by
  classical
  have hn0 : (n : ℝ) ≠ 0 := (ne_of_gt n_pos_real)
  have hsum :
      Finset.sum (Finset.univ) (fun _ : Fin n => c) = (n : ℝ) * c := by
    -- ∑ const = card • const; on ℝ this simplifies to (n : ℝ) * c
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  -- ((n:ℝ) * c) / (n:ℝ) = c
  simp [avg, hsum, hn0]

/-- (c) Calibration at `1ₙ`: `avg 1 = 1`. -/
@[simp] lemma avg_oneVec : avg (oneVec : Fin n → ℝ) = 1 := by
  -- oneVec = fun _ => 1, so this is avg_const with c = 1
  exact avg_const 1

/-- Zero vector has zero average. -/
@[simp] lemma avg_zero : avg (fun _ : Fin n => (0 : ℝ)) = 0 := 
  avg_const 0

/-! ## Stable Blueprint Aliases -/

/-- **[Paper Thm 2.1a]** Alias: Triangle inequality bound. -/
lemma fn_basics_norm (x : Fin n → ℝ) : |avg x| ≤ (1 / (n : ℝ)) * (Finset.sum (Finset.univ) (fun i => |x i|)) := avg_l1_bound x

/-- **[Paper Thm 2.1b]** Alias: Vanishing on sum = 0. -/
lemma fn_basics_vanishing {x : Fin n → ℝ} (h : Finset.sum (Finset.univ) (fun i => x i) = 0) : avg x = 0 := avg_vanish_of_sum_zero h

/-- **[Paper Thm 2.1c]** Alias: Calibration at 1ₙ. -/
lemma fn_basics_calibration : avg (oneVec : Fin n → ℝ) = 1 := avg_oneVec

end Papers.P2.Basics.FiniteCesaro