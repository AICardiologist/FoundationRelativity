/-
Papers/P13_EventHorizon/Basic.lean
Core definitions for Paper 13: The Event Horizon as a Logical Boundary.

Defines LPO, BMC, the Schwarzschild factor f(M,r), the Interior domain
predicate, and the running maximum of a binary sequence.

All definitions are self-contained (no cross-imports from other paper bundles).
LPO and BMC definitions match Paper 8; f matches Paper 5.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

universe u

namespace Papers.P13

open Real

-- ========================================================================
-- Logical principles (same as Paper 8)
-- ========================================================================

/-- Limited Principle of Omniscience.
    For any binary sequence, either all terms are false or there exists a true term.
    Equivalent to Bounded Monotone Convergence over BISH [Bridges–Vîță 2006]. -/
def LPO : Prop :=
  ∀ (α : ℕ → Bool), (∀ n, α n = false) ∨ (∃ n, α n = true)

/-- Bounded Monotone Convergence: every bounded non-decreasing sequence
    of reals has a limit. Equivalent to LPO over BISH [Bridges–Vîță 2006]. -/
def BMC : Prop :=
  ∀ (a : ℕ → ℝ) (M : ℝ),
    Monotone a →
    (∀ n, a n ≤ M) →
    ∃ L : ℝ, ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → |a N - L| < ε

/-- LPO implies BMC. Established in Paper 8 (citing Bridges–Vîță 2006, Theorem 2.1.5). -/
axiom bmc_of_lpo : LPO → BMC

/-- BMC implies LPO. Proved in Paper 8 via the free energy encoding technique. -/
axiom lpo_of_bmc : BMC → LPO

/-- LPO ↔ BMC. Combining both directions (Paper 8, Theorem 5.1). -/
theorem lpo_iff_bmc : LPO ↔ BMC :=
  ⟨bmc_of_lpo, lpo_of_bmc⟩

-- ========================================================================
-- Schwarzschild factor (same as Paper 5)
-- ========================================================================

/-- The fundamental Schwarzschild factor f(M, r) = 1 - 2M/r.
    Positive in the exterior (r > 2M), zero at the horizon (r = 2M),
    negative in the interior (0 < r < 2M). -/
noncomputable def f (M r : ℝ) : ℝ := 1 - 2 * M / r

-- ========================================================================
-- Interior domain (NEW — mirrors P5's Exterior)
-- ========================================================================

/-- Interior domain: 0 < r < 2M, M > 0.
    This is the region inside the event horizon where r is a timelike coordinate. -/
structure Interior (M r : ℝ) : Prop where
  mass_pos : M > 0
  r_pos : r > 0
  r_inside : r < 2 * M

/-- In the interior, r is nonzero. -/
theorem Interior.r_ne_zero {M r : ℝ} (h : Interior M r) : r ≠ 0 :=
  ne_of_gt h.r_pos

/-- In the interior, 2M > 0. -/
theorem Interior.two_M_pos {M r : ℝ} (h : Interior M r) : 0 < 2 * M :=
  mul_pos two_pos h.mass_pos

/-- The Schwarzschild factor is strictly negative in the interior.
    This is the signature flip: r becomes timelike, t becomes spacelike. -/
theorem f_neg_interior {M r : ℝ} (h : Interior M r) : f M r < 0 := by
  unfold f
  have hr_pos := h.r_pos
  have h_lt : r < 2 * M := h.r_inside
  -- We need: 1 - 2M/r < 0, i.e., 1 < 2M/r, i.e., r < 2M (which we have)
  have : 1 < 2 * M / r := by
    rw [lt_div_iff₀ hr_pos]
    linarith
  linarith

/-- The factor 2M/r - 1 is positive in the interior. -/
theorem two_M_over_r_sub_one_pos {M r : ℝ} (h : Interior M r) : 0 < 2 * M / r - 1 := by
  have := f_neg_interior h
  unfold f at this
  linarith

-- ========================================================================
-- Running maximum of a binary sequence (same as Paper 8)
-- ========================================================================

/-- Running maximum of a binary sequence α.
    runMax α n = max(α(0), α(1), ..., α(n)).
    In Bool: false < true, so this is true iff ∃ k ≤ n, α(k) = true. -/
def runMax (α : ℕ → Bool) : ℕ → Bool
  | 0 => α 0
  | n + 1 => α (n + 1) || runMax α n

/-- runMax is monotone: once true, stays true. -/
theorem runMax_mono (α : ℕ → Bool) (n : ℕ) (h : runMax α n = true) :
    runMax α (n + 1) = true := by
  simp [runMax, h]

/-- If runMax α n = false, then all α(k) = false for k ≤ n. -/
theorem all_false_of_runMax_false (α : ℕ → Bool) (n : ℕ) (h : runMax α n = false) :
    ∀ k, k ≤ n → α k = false := by
  induction n with
  | zero =>
    intro k hk
    interval_cases k
    exact h
  | succ n ih =>
    simp [runMax, Bool.or_eq_false_iff] at h
    intro k hk
    rcases Nat.eq_or_lt_of_le hk with rfl | hlt
    · exact h.1
    · exact ih h.2 k (Nat.lt_succ_iff.mp hlt)

/-- If runMax α n = true, there exists k ≤ n with α(k) = true. -/
theorem runMax_witness (α : ℕ → Bool) {n : ℕ} (h : runMax α n = true) :
    ∃ k, k ≤ n ∧ α k = true := by
  induction n with
  | zero => exact ⟨0, le_refl 0, h⟩
  | succ n ih =>
    simp [runMax] at h
    rcases h with h1 | h2
    · exact ⟨n + 1, le_refl _, h1⟩
    · obtain ⟨k, hk, hαk⟩ := ih h2
      exact ⟨k, Nat.le_succ_of_le hk, hαk⟩

/-- If ∀ n, α n = false, then ∀ n, runMax α n = false. -/
theorem runMax_all_false (α : ℕ → Bool) (h : ∀ n, α n = false) :
    ∀ n, runMax α n = false := by
  intro n
  induction n with
  | zero => exact h 0
  | succ n ih => simp [runMax, h (n + 1), ih]

/-- If ∃ n₀, α n₀ = true, then for all n ≥ n₀, runMax α n = true. -/
theorem runMax_eventually_true (α : ℕ → Bool) {n₀ : ℕ} (h : α n₀ = true)
    {n : ℕ} (hn : n₀ ≤ n) : runMax α n = true := by
  induction n with
  | zero =>
    interval_cases n₀
    exact h
  | succ n ih =>
    simp [runMax]
    rcases Nat.eq_or_lt_of_le hn with rfl | hlt
    · left; exact h
    · right; exact ih (Nat.lt_succ_iff.mp hlt)

/-- Helper: if not (∃ n, α n = true), then ∀ n, α n = false. -/
theorem bool_not_exists_implies_all_false (α : ℕ → Bool)
    (h : ¬∃ n, α n = true) : ∀ n, α n = false := by
  intro n
  by_contra hc
  push_neg at hc
  apply h
  exact ⟨n, Bool.eq_true_of_not_eq_false hc⟩

end Papers.P13
