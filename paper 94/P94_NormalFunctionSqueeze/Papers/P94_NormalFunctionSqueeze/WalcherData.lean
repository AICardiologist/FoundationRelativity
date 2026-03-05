import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
  WalcherData.lean — Verified coefficients of Walcher's normal function

  The domainwall tension T(z) for the real Lagrangian on the mirror quintic
  satisfies the inhomogeneous Picard-Fuchs equation:
    L · T(z) = (15/8) · √z
  where L = θ⁴ - 5z(5θ+1)(5θ+2)(5θ+3)(5θ+4) in CDGP coordinate z = (5ψ)⁻⁵.

  Writing T = √z · Σ bₙ zⁿ, the recurrence is:
    b₀ = 30
    bₙ = 5 · b_{n-1} · (5n-3/2)(5n-1/2)(5n+1/2)(5n+3/2) / (n+1/2)⁴

  References:
    [W07] Walcher, Comm. Math. Phys. 276 (2007) 671–689, arXiv:hep-th/0605162
    [MW09] Morrison-Walcher, Adv. Theor. Math. Phys. 13 (2009) 553–598
-/

namespace P94

-- ═══════════════════════════════════════════════════════════════
-- §1. Source term: δ(z) = (15/8)√z, algebraic relation δ² = (225/64)z
-- ═══════════════════════════════════════════════════════════════

noncomputable def walcher_source_coeff : ℚ := 15 / 8

/-- The source coefficient squared equals 225/64. -/
theorem source_coeff_sq : walcher_source_coeff ^ 2 = 225 / 64 := by
  unfold walcher_source_coeff; norm_num

/-- The source coefficient is nonzero. -/
theorem source_coeff_ne_zero : walcher_source_coeff ≠ 0 := by
  unfold walcher_source_coeff; norm_num

-- ═══════════════════════════════════════════════════════════════
-- §2. Normal function expansion coefficients b_n
-- ═══════════════════════════════════════════════════════════════

noncomputable def b_0 : ℚ := 30
noncomputable def b_1 : ℚ := (50050 : ℚ) / 3
noncomputable def b_2 : ℚ := (104110006 : ℚ) / 5
noncomputable def b_3 : ℚ := (1701899016246 : ℚ) / 49
noncomputable def b_4 : ℚ := (89087374782324490 : ℚ) / 1323
noncomputable def b_5 : ℚ := (155891861979632032150 : ℚ) / 1089

/-- Leading order: b₀ · (1/2)⁴ = 15/8 (Walcher's n₁ = 30 disk count). -/
theorem leading_order : b_0 * ((1 : ℚ) / 2) ^ 4 = 15 / 8 := by
  unfold b_0; norm_num

/-- The leading coefficient is 30. -/
theorem b_0_val : b_0 = 30 := by unfold b_0; norm_num

-- ═══════════════════════════════════════════════════════════════
-- §3. Recurrence verification: bₙ · (n+1/2)⁴ = 5·b_{n-1}·∏ₖ(5n+k)
-- ═══════════════════════════════════════════════════════════════

/-- Recurrence at n = 1: b_1 · ((3)/2)⁴ = 5 · b_0 · ∏ -/
theorem recurrence_1 :
    b_1 * ((81 : ℚ) / 16) = b_0 * ((45045 : ℚ) / 16) := by
  unfold b_1 b_0; norm_num

/-- Recurrence at n = 2: b_2 · ((5)/2)⁴ = 5 · b_1 · ∏ -/
theorem recurrence_2 :
    b_2 * ((625 : ℚ) / 16) = b_1 * ((780045 : ℚ) / 16) := by
  unfold b_2 b_1; norm_num

/-- Recurrence at n = 3: b_3 · ((7)/2)⁴ = 5 · b_2 · ∏ -/
theorem recurrence_3 :
    b_3 * ((2401 : ℚ) / 16) = b_2 * ((4005045 : ℚ) / 16) := by
  unfold b_3 b_2; norm_num

/-- Recurrence at n = 4: b_4 · ((9)/2)⁴ = 5 · b_3 · ∏ -/
theorem recurrence_4 :
    b_4 * ((6561 : ℚ) / 16) = b_3 * ((12720045 : ℚ) / 16) := by
  unfold b_4 b_3; norm_num

/-- Recurrence at n = 5: b_5 · ((11)/2)⁴ = 5 · b_4 · ∏ -/
theorem recurrence_5 :
    b_5 * ((14641 : ℚ) / 16) = b_4 * ((31125045 : ℚ) / 16) := by
  unfold b_5 b_4; norm_num

-- ═══════════════════════════════════════════════════════════════
-- §4. Non-triviality: all coefficients are nonzero
-- ═══════════════════════════════════════════════════════════════

theorem b_0_ne_zero : b_0 ≠ 0 := by unfold b_0; norm_num
theorem b_1_ne_zero : b_1 ≠ 0 := by unfold b_1; norm_num
theorem b_2_ne_zero : b_2 ≠ 0 := by unfold b_2; norm_num
theorem b_3_ne_zero : b_3 ≠ 0 := by unfold b_3; norm_num
theorem b_4_ne_zero : b_4 ≠ 0 := by unfold b_4; norm_num
theorem b_5_ne_zero : b_5 ≠ 0 := by unfold b_5; norm_num

-- ═══════════════════════════════════════════════════════════════
-- §5. Formal recurrence and induction proof: b_n ≠ 0 for all n
-- ═══════════════════════════════════════════════════════════════

/-! The Walcher recurrence in cleared-denominator form (all integers):

  b₀ = 30
  b_{n+1} = 5 · bₙ · (10n+7)(10n+9)(10n+11)(10n+13) / (2n+3)⁴

  The denominator (2n+3)⁴ is always nonzero (2n+3 ≥ 3 for n ∈ ℕ).
  All numerator factors 10n+7, 10n+9, 10n+11, 10n+13 are ≥ 7 > 0.
  Hence the recurrence multiplier is positive, so b_n ≠ 0 propagates
  by induction from b₀ = 30. -/

/-- The Walcher recurrence multiplier for index n+1:
    R(n) = 5 · (10n+7)(10n+9)(10n+11)(10n+13) / (2n+3)⁴ -/
noncomputable def walcher_multiplier (n : ℕ) : ℚ :=
  5 * ((10 * (n : ℚ) + 7) * (10 * n + 9) * (10 * n + 11) * (10 * n + 13)) /
  ((2 * (n : ℚ) + 3) ^ 4)

/-- The Walcher sequence defined by the recurrence. -/
noncomputable def walcher_b : ℕ → ℚ
  | 0     => 30
  | n + 1 => walcher_b n * walcher_multiplier n

/-- The base case agrees with b_0. -/
theorem walcher_b_zero : walcher_b 0 = 30 := rfl

/-- The denominator (2n+3)⁴ is positive for all n. -/
theorem denom_pos (n : ℕ) : (0 : ℚ) < (2 * (n : ℚ) + 3) ^ 4 := by positivity

/-- The denominator (2n+3)⁴ is nonzero for all n. -/
theorem denom_ne_zero (n : ℕ) : (2 * (n : ℚ) + 3) ^ 4 ≠ 0 :=
  ne_of_gt (denom_pos n)

/-- The numerator product (10n+7)(10n+9)(10n+11)(10n+13) is positive for all n. -/
theorem numer_pos (n : ℕ) :
    (0 : ℚ) < (10 * (n : ℚ) + 7) * (10 * n + 9) * (10 * n + 11) * (10 * n + 13) := by
  positivity

/-- The recurrence multiplier is nonzero for all n. -/
theorem walcher_multiplier_ne_zero (n : ℕ) : walcher_multiplier n ≠ 0 := by
  unfold walcher_multiplier
  apply div_ne_zero
  · apply mul_ne_zero
    · norm_num
    · exact ne_of_gt (numer_pos n)
  · exact denom_ne_zero n

/-- **b_n ≠ 0 for all n ≥ 0**, by induction on the Walcher recurrence.
    Base: b₀ = 30 ≠ 0. Step: b_{n+1} = b_n · R(n) with R(n) ≠ 0. -/
theorem walcher_b_ne_zero : ∀ n : ℕ, walcher_b n ≠ 0
  | 0     => by simp [walcher_b]
  | n + 1 => by
    simp only [walcher_b]
    exact mul_ne_zero (walcher_b_ne_zero n) (walcher_multiplier_ne_zero n)

/-- Consistency: walcher_b 0 = b_0. -/
theorem walcher_b_eq_b0 : walcher_b 0 = b_0 := by
  unfold walcher_b b_0; norm_num

/-- Consistency: walcher_b 1 = b_1. -/
theorem walcher_b_eq_b1 : walcher_b 1 = b_1 := by
  simp only [walcher_b, walcher_multiplier]
  unfold b_1; norm_num

-- ═══════════════════════════════════════════════════════════════
-- §6. Connection to enumerative geometry
-- ═══════════════════════════════════════════════════════════════

/-- Walcher's disk count: 30 holomorphic disks of minimal area
    ending on the real Lagrangian RP³ ⊂ X₅. -/
theorem walcher_disk_count : b_0 = 30 := by unfold b_0; norm_num

end P94
