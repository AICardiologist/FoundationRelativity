/-
  Paper 44: The Measurement Problem Dissolved
  Defs/BinaryEncoding.lean — Binary sequence encoding into reals

  The standard constructive encoding: given f : ℕ → Bool,
    r_f = Σₙ f(n) · 2^{-(n+1)}
  satisfies: r_f = 0 ↔ ∀ n, f n = false.

  Also provides the running maximum (runMax) from Paper 8.
-/
import Papers.P44_MeasurementDissolved.Defs.Principles
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section
namespace Papers.P44

open Real

-- ========================================================================
-- Running maximum of a binary sequence
-- ========================================================================

/-- Running maximum of a binary sequence α.
    runMax α n = max(α(0), α(1), ..., α(n)).
    In Bool: false < true, so this is true iff ∃ k ≤ n, α(k) = true.
    Identical to Papers.P8.runMax. -/
def runMax (α : ℕ → Bool) : ℕ → Bool
  | 0 => α 0
  | n + 1 => α (n + 1) || runMax α n

/-- runMax is monotone: once true, stays true. -/
theorem runMax_mono (α : ℕ → Bool) (n : ℕ) :
    runMax α n = true → runMax α (n + 1) = true := by
  intro h
  simp [runMax, h]

/-- runMax witnesses existence. -/
theorem runMax_witness (α : ℕ → Bool) (n : ℕ) :
    runMax α n = true → ∃ k, k ≤ n ∧ α k = true := by
  induction n with
  | zero =>
    intro h
    exact ⟨0, le_refl 0, h⟩
  | succ n ih =>
    intro h
    simp [runMax] at h
    rcases h with h₁ | h₂
    · exact ⟨n + 1, le_refl _, h₁⟩
    · obtain ⟨k, hk, hak⟩ := ih h₂
      exact ⟨k, Nat.le_succ_of_le hk, hak⟩

/-- If all entries are false, runMax is always false. -/
theorem runMax_of_all_false (α : ℕ → Bool) :
    (∀ n, α n = false) → ∀ n, runMax α n = false := by
  intro h n
  induction n with
  | zero => exact h 0
  | succ n ih => simp [runMax, h (n + 1), ih]

-- ========================================================================
-- Binary encoding into reals
-- ========================================================================

/-- Convert a Bool to a real number: true ↦ 1, false ↦ 0. -/
def boolToReal (b : Bool) : ℝ := if b then 1 else 0

@[simp] theorem boolToReal_true : boolToReal true = 1 := rfl
@[simp] theorem boolToReal_false : boolToReal false = 0 := rfl

theorem boolToReal_nonneg (b : Bool) : 0 ≤ boolToReal b := by
  cases b <;> simp [boolToReal]

theorem boolToReal_le_one (b : Bool) : boolToReal b ≤ 1 := by
  cases b <;> simp [boolToReal]

/-- The standard binary encoding: r_f = Σₙ f(n) · 2^{-(n+1)}.
    This encodes a binary sequence into a real in [0, 1]. -/
noncomputable def binaryEncoding (f : ℕ → Bool) : ℝ :=
  ∑' n, boolToReal (f n) * (2 : ℝ)⁻¹ ^ (n + 1)

/-- Each term of the binary encoding is non-negative. -/
theorem binaryEncoding_term_nonneg (f : ℕ → Bool) (n : ℕ) :
    0 ≤ boolToReal (f n) * (2 : ℝ)⁻¹ ^ (n + 1) :=
  mul_nonneg (boolToReal_nonneg _) (pow_nonneg (by positivity) _)

/-- The geometric series (2⁻¹)^(n+1) is summable. -/
theorem summable_half_pow_succ :
    Summable (fun n : ℕ => (2 : ℝ)⁻¹ ^ (n + 1)) := by
  have h : Summable (fun n : ℕ => (2 : ℝ)⁻¹ ^ n) :=
    summable_geometric_of_lt_one (by positivity) (by norm_num)
  exact h.comp_injective (fun a b hab => by omega)

/-- The binary encoding series is summable (dominated by geometric series). -/
theorem binaryEncoding_summable (f : ℕ → Bool) :
    Summable (fun n => boolToReal (f n) * (2 : ℝ)⁻¹ ^ (n + 1)) := by
  apply Summable.of_nonneg_of_le
  · intro n; exact binaryEncoding_term_nonneg f n
  · intro n
    exact mul_le_mul_of_nonneg_right (boolToReal_le_one _) (pow_nonneg (by positivity) _)
  · simpa using summable_half_pow_succ

/-- The binary encoding is non-negative. -/
theorem binaryEncoding_nonneg (f : ℕ → Bool) : 0 ≤ binaryEncoding f :=
  tsum_nonneg (fun n => binaryEncoding_term_nonneg f n)

/-- If all entries are false, the encoding is zero. -/
theorem binaryEncoding_eq_zero_of_all_false (f : ℕ → Bool)
    (h : ∀ n, f n = false) : binaryEncoding f = 0 := by
  simp only [binaryEncoding]
  have : (fun n => boolToReal (f n) * (2 : ℝ)⁻¹ ^ (n + 1)) = fun _ => (0 : ℝ) := by
    ext n; simp [h n, boolToReal]
  rw [this, tsum_zero]

/-- If some entry is true, the encoding is positive. -/
theorem binaryEncoding_pos_of_exists_true (f : ℕ → Bool)
    (h : ∃ n, f n = true) : 0 < binaryEncoding f := by
  obtain ⟨k, hk⟩ := h
  have hterm : 0 < boolToReal (f k) * (2 : ℝ)⁻¹ ^ (k + 1) := by
    simp only [hk, boolToReal_true, one_mul]
    positivity
  calc 0 < boolToReal (f k) * (2 : ℝ)⁻¹ ^ (k + 1) := hterm
    _ ≤ ∑' n, boolToReal (f n) * (2 : ℝ)⁻¹ ^ (n + 1) :=
        (binaryEncoding_summable f).le_tsum k (fun n _hn => binaryEncoding_term_nonneg f n)

/-- The encoding is zero if and only if all entries are false. -/
theorem binaryEncoding_eq_zero_iff (f : ℕ → Bool) :
    binaryEncoding f = 0 ↔ ∀ n, f n = false := by
  constructor
  · intro h n
    by_contra hc
    push_neg at hc
    simp only [Bool.not_eq_false] at hc
    have := binaryEncoding_pos_of_exists_true f ⟨n, hc⟩
    linarith
  · exact binaryEncoding_eq_zero_of_all_false f

end Papers.P44
end
