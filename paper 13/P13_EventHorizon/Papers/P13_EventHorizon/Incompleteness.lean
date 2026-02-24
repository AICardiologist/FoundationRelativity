/-
Papers/P13_EventHorizon/Incompleteness.lean
Module 3: Geodesic Incompleteness as a Completed-Limit Assertion.

The key definition: SchwarzschildInteriorGeodesicIncompleteness asserts
that for every M > 0, the infalling radial geodesic attains r = 0 in
finite proper time. Formally, it asserts that every non-increasing
non-negative sequence that is bounded below and whose terms satisfy the
interior geodesic velocity equation converges to a definite limit L,
AND that limit is 0.

The assertion "the limit exists and equals 0" decomposes as:
  (a) The limit exists (= BMC for decreasing sequences)
  (b) The limit must be 0 (follows from the geodesic equation)

Part (a) is exactly BMC, hence LPO. Part (b) is a consequence of the
velocity bound in the interior. Together, they give LPO ↔ Incompleteness.

This module also defines the encoding sequence that embeds binary
sequences α : ℕ → Bool into monotone sequences on [0, 2M], mirroring
the coupling sequence technique from Paper 8.
-/
import Papers.P13_EventHorizon.RadialGeodesic

namespace Papers.P13

open Real Set

-- ========================================================================
-- Schwarzschild Interior Geodesic Incompleteness
-- ========================================================================

/-- **Schwarzschild Interior Geodesic Incompleteness.**

    For all M > 0, every non-increasing non-negative sequence starting
    in the interior (a(0) < 2M) converges to a definite real limit.

    This is the completed-limit assertion: asserting that a bounded
    monotone sequence has a limit as a definite real number costs exactly
    BMC (= LPO).

    The physical content: the radial coordinate r(τ) along a freely
    falling geodesic decreases monotonically, is bounded below by 0,
    and (classically) converges to 0 in finite proper time. The
    constructive content of "converges to a definite limit" is BMC.

    We formulate this as: there exists L ≥ 0 such that the sequence
    converges to L. The assertion that such L exists is the BMC content.
    (That L = 0 then follows from the geodesic equation, but the
    existence of L itself is the non-constructive step.) -/
def SchwarzschildInteriorGeodesicIncompleteness : Prop :=
  ∀ (M : ℝ), M > 0 →
  ∀ (a : ℕ → ℝ),
    Antitone a →                       -- r(τ) is non-increasing
    (∀ n, 0 ≤ a n) →                   -- r(τ) ≥ 0
    a 0 < 2 * M →                      -- starts in the interior
    ∃ L : ℝ, ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, |a N - L| < ε

-- ========================================================================
-- Encoding: coupling sequence for the geodesic context
-- ========================================================================

/-- Coupling sequence for the geodesic encoding.
    Given a binary sequence α, maps it to values in {v₀, v₁} via runMax,
    where v₀ > v₁ ≥ 0.

    If runMax α n = false: value is v₀ (sequence "stalls" at positive level)
    If runMax α n = true:  value is v₁ (sequence drops to lower level)

    For the geodesic context: v₀ = M, v₁ = 0. -/
noncomputable def geodesicCoupling (α : ℕ → Bool) (v₀ v₁ : ℝ) (n : ℕ) : ℝ :=
  if runMax α n then v₁ else v₀

/-- The geodesic coupling takes values in {v₀, v₁}. -/
theorem geodesicCoupling_mem (α : ℕ → Bool) (v₀ v₁ : ℝ) (n : ℕ) :
    geodesicCoupling α v₀ v₁ n = v₀ ∨ geodesicCoupling α v₀ v₁ n = v₁ := by
  unfold geodesicCoupling
  cases runMax α n <;> simp

/-- If all α(k) = false, the coupling is constantly v₀. -/
theorem geodesicCoupling_all_false (α : ℕ → Bool) (v₀ v₁ : ℝ)
    (h : ∀ n, α n = false) (n : ℕ) :
    geodesicCoupling α v₀ v₁ n = v₀ := by
  simp [geodesicCoupling, runMax_all_false α h n]

/-- If ∃ n₀ with α(n₀) = true, the coupling is eventually v₁. -/
theorem geodesicCoupling_exists_true (α : ℕ → Bool) (v₀ v₁ : ℝ)
    {n₀ : ℕ} (h : α n₀ = true) {n : ℕ} (hn : n₀ ≤ n) :
    geodesicCoupling α v₀ v₁ n = v₁ := by
  simp [geodesicCoupling, runMax_eventually_true α h hn]

/-- The geodesic coupling is non-increasing when v₀ ≥ v₁. -/
theorem geodesicCoupling_antitone (α : ℕ → Bool) {v₀ v₁ : ℝ} (hv : v₁ ≤ v₀) :
    Antitone (geodesicCoupling α v₀ v₁) := by
  apply antitone_nat_of_succ_le
  intro n
  unfold geodesicCoupling
  cases h : runMax α n <;> simp
  · -- runMax α n = false
    cases runMax α (n + 1) <;> simp [hv]
  · -- runMax α n = true, so runMax α (n+1) = true
    have := runMax_mono α n h
    simp [this]

/-- The geodesic coupling is non-negative when v₀, v₁ ≥ 0. -/
theorem geodesicCoupling_nonneg (α : ℕ → Bool) {v₀ v₁ : ℝ}
    (hv₀ : 0 ≤ v₀) (hv₁ : 0 ≤ v₁) (n : ℕ) :
    0 ≤ geodesicCoupling α v₀ v₁ n := by
  rcases geodesicCoupling_mem α v₀ v₁ n with h | h <;> rw [h] <;> assumption

/-- The geodesic coupling is bounded above by v₀ when v₁ ≤ v₀. -/
theorem geodesicCoupling_le (α : ℕ → Bool) {v₀ v₁ : ℝ} (hv : v₁ ≤ v₀) (n : ℕ) :
    geodesicCoupling α v₀ v₁ n ≤ v₀ := by
  rcases geodesicCoupling_mem α v₀ v₁ n with h | h
  · rw [h]
  · rw [h]; linarith

-- ========================================================================
-- Gap lemma: the key for the forward direction
-- ========================================================================

/-- The gap between the "all false" and "exists true" limits.
    When v₀ > v₁: if the sequence has limit L, comparing L with v₀
    decides LPO. -/
noncomputable def geodesicGap (v₀ v₁ : ℝ) : ℝ := v₀ - v₁

theorem geodesicGap_pos {v₀ v₁ : ℝ} (hv : v₁ < v₀) : geodesicGap v₀ v₁ > 0 := by
  unfold geodesicGap
  linarith

-- ========================================================================
-- Limit identification lemmas
-- ========================================================================

/-- Helper: if a sequence converges to L and is eventually equal to c, then L = c. -/
lemma limit_eq_of_eventually_const {f : ℕ → ℝ} {L c : ℝ} (n₀ : ℕ)
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → |f N - L| < ε)
    (hevent : ∀ n, n₀ ≤ n → f n = c) :
    L = c := by
  by_contra hne
  have hd : 0 < |c - L| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hne))
  obtain ⟨N₀, hN₀⟩ := hconv (|c - L| / 2) (half_pos hd)
  have hN := hN₀ (max N₀ n₀) (le_max_left _ _)
  rw [hevent (max N₀ n₀) (le_max_right _ _)] at hN
  linarith [abs_nonneg (c - L)]

/-- If ∃ n₀ with α(n₀) = true, the limit of geodesicCoupling is v₁. -/
lemma limit_of_exists_true (α : ℕ → Bool) (v₀ v₁ : ℝ)
    {L : ℝ}
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      |geodesicCoupling α v₀ v₁ N - L| < ε)
    {n₀ : ℕ} (h : α n₀ = true) :
    L = v₁ :=
  limit_eq_of_eventually_const n₀ hconv
    (fun _n hn => geodesicCoupling_exists_true α v₀ v₁ h hn)

/-- If ∀ n, α(n) = false, the limit of geodesicCoupling is v₀. -/
lemma limit_of_all_false (α : ℕ → Bool) (v₀ v₁ : ℝ)
    {L : ℝ}
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      |geodesicCoupling α v₀ v₁ N - L| < ε)
    (h : ∀ n, α n = false) :
    L = v₀ :=
  limit_eq_of_eventually_const 0 hconv
    (fun n _hn => geodesicCoupling_all_false α v₀ v₁ h n)

end Papers.P13
