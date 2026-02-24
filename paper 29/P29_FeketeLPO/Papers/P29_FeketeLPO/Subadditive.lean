/-
  Paper 29: Fekete's Subadditive Lemma ↔ LPO
  Subadditive.lean — mockFreeEnergy is subadditive and bounded below

  Key results:
    1. mockFreeEnergy_subadditive: F(m+n) ≤ F(m) + F(n)
    2. mockFreeEnergy_div_bdd_below: F(n)/n ≥ -1

  The subadditivity proof uses:
    - indicator is monotone: x_m ≤ x_(m+n) and x_n ≤ x_(m+n)
    - Therefore -m·x_(m+n) ≤ -m·x_m and -n·x_(m+n) ≤ -n·x_n
    - linarith closes the combined inequality

  All proofs are BISH-valid. No case splits on Bool needed for subadditivity —
  the monotonicity of indicator does all the work.
-/
import Papers.P29_FeketeLPO.Indicator

noncomputable section
namespace Papers.P29

-- ========================================================================
-- Subadditivity
-- ========================================================================

/-- Key monotonicity fact: indicator at m ≤ indicator at m+n. -/
lemma indicator_le_add_left (α : ℕ → Bool) (m n : ℕ) :
    indicator α m ≤ indicator α (m + n) :=
  indicator_mono α (Nat.le_add_right m n)

/-- Key monotonicity fact: indicator at n ≤ indicator at m+n. -/
lemma indicator_le_add_right (α : ℕ → Bool) (m n : ℕ) :
    indicator α n ≤ indicator α (m + n) :=
  indicator_mono α (Nat.le_add_left n m)

/-- **mockFreeEnergy is subadditive: F(m+n) ≤ F(m) + F(n).**

    Proof: F(m+n) = -(m+n)·x_{m+n} = -m·x_{m+n} - n·x_{m+n}.
    Since x is monotone, x_m ≤ x_{m+n} and x_n ≤ x_{m+n}.
    Since m, n ≥ 0: -m·x_{m+n} ≤ -m·x_m and -n·x_{m+n} ≤ -n·x_n.
    Add: -(m+n)·x_{m+n} ≤ -m·x_m - n·x_n = F(m) + F(n). -/
theorem mockFreeEnergy_subadditive (α : ℕ → Bool) (m n : ℕ) :
    mockFreeEnergy α (m + n) ≤ mockFreeEnergy α m + mockFreeEnergy α n := by
  unfold mockFreeEnergy
  have hm_nn : (0 : ℝ) ≤ ↑m := Nat.cast_nonneg m
  have hn_nn : (0 : ℝ) ≤ ↑n := Nat.cast_nonneg n
  have h_xm : indicator α m ≤ indicator α (m + n) := indicator_le_add_left α m n
  have h_xn : indicator α n ≤ indicator α (m + n) := indicator_le_add_right α m n
  push_cast
  nlinarith

-- ========================================================================
-- Bounded below
-- ========================================================================

/-- **F(n)/n is bounded below by -1.**

    Proof: F(n)/n = -x_n, and x_n ∈ {0, 1}, so -x_n ≥ -1. -/
theorem mockFreeEnergy_div_bdd_below (α : ℕ → Bool) (n : ℕ) (hn : 0 < n) :
    -1 ≤ mockFreeEnergy α n / ↑n := by
  unfold mockFreeEnergy
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  rw [neg_mul, neg_div, neg_le_neg_iff]
  rw [mul_div_cancel_left₀ (indicator α n) (ne_of_gt hn_pos)]
  exact indicator_le_one α n

/-- **F(n)/n equals -x_n for n > 0.** Convenient rewrite. -/
lemma mockFreeEnergy_div (α : ℕ → Bool) (n : ℕ) (hn : 0 < n) :
    mockFreeEnergy α n / ↑n = -(indicator α n) := by
  unfold mockFreeEnergy
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  rw [neg_mul, neg_div]
  exact neg_inj.mpr (mul_div_cancel_left₀ (indicator α n) (ne_of_gt hn_pos))

-- ========================================================================
-- Edge case: F(0) = 0
-- ========================================================================

/-- F(0) = 0. -/
@[simp]
lemma mockFreeEnergy_zero (α : ℕ → Bool) : mockFreeEnergy α 0 = 0 := by
  simp [mockFreeEnergy]

-- ========================================================================
-- Limit values
-- ========================================================================

/-- If α ≡ false, then F(n)/n = 0 for all n > 0. -/
lemma mockFreeEnergy_div_all_false (α : ℕ → Bool) (h : ∀ n, α n = false)
    (n : ℕ) (hn : 0 < n) : mockFreeEnergy α n / ↑n = 0 := by
  rw [mockFreeEnergy_div α n hn, indicator_of_all_false α h n, neg_zero]

/-- If ∃ k, α(k) = true, then F(n)/n = -1 for all n > k+1.
    (Actually for n > k, since indicator uses strict <.) -/
lemma mockFreeEnergy_div_exists_true (α : ℕ → Bool) {k : ℕ} (hk : α k = true)
    {n : ℕ} (hn : k + 1 < n) : mockFreeEnergy α n / ↑n = -1 := by
  have hn_pos : 0 < n := by omega
  rw [mockFreeEnergy_div α n hn_pos]
  have : k < n := by omega
  rw [indicator_of_exists_true α hk this]

end Papers.P29
end
