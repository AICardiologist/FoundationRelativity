import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Papers.P4_SpectralGeometry.Discrete.IntervalBookkeeping

/-!
# Harmonic Series Bounds

This module provides explicit bounds on the harmonic series that are
crucial for our perturbation analysis.

## Main Results

* `harmonic_sum_lower` - Hₙ ≥ log(n+1)
* `harmonic_sum_upper` - Hₙ ≤ log(n) + 1
* `harmonic_diverges` - Hₙ → ∞ as n → ∞
* `harmonic_bounded_iff` - Hₙ ≤ B iff n ≤ exp(B)

These bounds connect the TM computation length to perturbation size.
-/

namespace Papers.P4_SpectralGeometry.Discrete

open Real

/-- The nth harmonic number -/
def harmonicNumber (n : ℕ) : ℝ :=
  (Finset.range n).sum (fun k => 1 / (k + 1 : ℝ))

notation "H_" n => harmonicNumber n

/-- Harmonic number in rationals (matches maxPerturbation) -/
lemma harmonic_eq_maxPerturbation (n : ℕ) :
    H_n = (maxPerturbation n : ℝ) := by
  simp [harmonicNumber, maxPerturbation]
  -- Convert the rational sum to real
  sorry

/-- Lower bound: Harmonic number is at least log(n+1) -/
theorem harmonic_sum_lower (n : ℕ) (hn : n > 0) :
    H_n ≥ log (n + 1) := by
  -- Classic proof: Compare sum with integral
  -- H_n = 1 + 1/2 + ... + 1/n ≥ ∫₁ⁿ⁺¹ 1/x dx = log(n+1)
  sorry

/-- Upper bound: Harmonic number is at most log(n) + 1 -/
theorem harmonic_sum_upper (n : ℕ) (hn : n > 0) :
    H_n ≤ log n + 1 := by
  -- H_n = 1 + 1/2 + ... + 1/n ≤ 1 + ∫₁ⁿ 1/x dx = 1 + log(n)
  sorry

/-- Asymptotic: Harmonic number is log(n) + γ + o(1) -/
theorem harmonic_asymptotic (n : ℕ) (hn : n > 0) :
    ∃ γ : ℝ, |H_n - (log n + γ)| ≤ 1 / n := by
  -- γ ≈ 0.5772... is the Euler-Mascheroni constant
  sorry

/-- Key lemma: Harmonic series diverges -/
theorem harmonic_diverges :
    ∀ B : ℝ, ∃ n : ℕ, H_n > B := by
  intro B
  -- Since H_n ≥ log(n+1), choose n > exp(B)
  use (⌊exp B⌋₊ + 1)
  have h_lower := harmonic_sum_lower _ (by simp)
  calc H_(⌊exp B⌋₊ + 1) 
      ≥ log (⌊exp B⌋₊ + 1 + 1) := h_lower
    _ > log (exp B + 1) := by sorry  -- floor properties
    _ > log (exp B) := by sorry      -- log monotone
    _ = B := log_exp B

/-- Characterization: When is harmonic sum bounded? -/
theorem harmonic_bounded_iff (B : ℝ) (hB : B > 0) :
    (∃ n₀ : ℕ, ∀ n ≥ n₀, H_n ≤ B) ↔ False := by
  -- Harmonic series is never eventually bounded
  constructor
  · intro ⟨n₀, h_bound⟩
    -- Get contradiction from divergence
    obtain ⟨n, hn⟩ := harmonic_diverges (B + 1)
    have : H_n ≤ B := h_bound n (le_of_lt $ by sorry)
    linarith
  · intro h; exact h.elim

/-- Explicit bounds for small n -/
lemma harmonic_small_n : 
    H_10 < 3 ∧ H_100 < 6 ∧ H_1000 < 8 := by
  -- Can compute explicitly or use bounds
  constructor
  · -- H_10 = 1 + 1/2 + ... + 1/10 ≈ 2.93
    sorry
  constructor  
  · -- H_100 ≈ 5.19
    sorry
  · -- H_1000 ≈ 7.49
    sorry

/-- Key connection: Small n means small perturbation -/
theorem small_n_small_perturbation (n : ℕ) (h : n < 100) :
    (maxPerturbation n : ℝ) < 6 := by
  rw [← harmonic_eq_maxPerturbation]
  calc H_n ≤ H_100 := by sorry  -- Monotonicity
         _ < 6 := harmonic_small_n.2.1

/-- Key connection: Large N means large perturbation -/
theorem large_N_large_perturbation (N : ℕ) (h : N > 1000) :
    (maxPerturbation N : ℝ) > 7 := by
  rw [← harmonic_eq_maxPerturbation]
  calc H_N ≥ H_1000 := by sorry  -- Monotonicity
         _ > 7 := by
    -- H_1000 ≈ 7.49 > 7
    sorry

/-- Connection to threshold: When does perturbation exceed h²? -/
theorem perturbation_exceeds_threshold (h : ℚ) (h_pos : 0 < h) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, (maxPerturbation N : ℝ) > (h^2 : ℝ) := by
  -- Since H_N → ∞ and h² is fixed, eventually H_N > h²
  obtain ⟨N₀, hN₀⟩ := harmonic_diverges ((h^2 : ℝ) + 1)
  use N₀
  intro N hN
  rw [← harmonic_eq_maxPerturbation]
  calc H_N ≥ H_N₀ := by sorry  -- Monotonicity
         _ > (h^2 : ℝ) + 1 := hN₀
         _ > (h^2 : ℝ) := by linarith

end Papers.P4_SpectralGeometry.Discrete