/-
Papers/P9_Combinatorial_Ising/PartB_Backward.lean
Backward direction: BMC → LPO.

This is the main new content of Part B. The proof encodes an arbitrary
binary sequence α : ℕ → Bool into a free energy sequence F(n) = g(J(n)),
applies BMC to obtain a limit, and uses the limit to decide α.

The encoding uses:
  1. Running maximum m(n) = max(α(0),...,α(n))
  2. Coupling J(n) = if m(n) then J₁ else J₀ (with 0 < J₀ < J₁)
  3. Free energy F(n) = -log(2·cosh(β·J(n)))
  4. Gap δ = g(J₀) - g(J₁) > 0

Decision procedure:
  - Apply BMC to -F to get limit L_neg
  - Get N₁ from modulus with |(-F)(N₁) - L_neg| < δ/2
  - Case split on runMax α N₁ (decidable: it is a Bool)
  - If true: witness extraction
  - If false: contradiction argument

The free energy g(J) = -log(2·cosh(βJ)) is justified combinatorially via
the partition function identity Z_N(β,J) = (2·cosh(βJ))^N + (2·sinh(βJ))^N
(Lemma 5.0 in the paper). No transfer matrices.
-/
import Papers.P9_Combinatorial_Ising.PartB_EncodedSeq

namespace Papers.P9

open Real

-- ========================================================================
-- Helper: limit of eventually constant sequence
-- ========================================================================

/-- If a sequence converges to L and is eventually equal to c, then L = c. -/
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

-- ========================================================================
-- Helper: limit identification for the two cases
-- ========================================================================

/-- If ∃ n₀ with α(n₀) = true, the limit of -encodedSeq is -g(J₁). -/
lemma neg_limit_of_exists_true (α : ℕ → Bool) {β J₀ J₁ : ℝ}
    {L_neg : ℝ}
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      |(fun n => -encodedSeq α β J₀ J₁ n) N - L_neg| < ε)
    {n₀ : ℕ} (h : α n₀ = true) :
    L_neg = -freeEnergyAtCoupling β J₁ :=
  limit_eq_of_eventually_const n₀ hconv
    (fun n hn => by simp [encodedSeq_of_exists_true α β J₀ J₁ h hn])

/-- If α ≡ false, the limit of -encodedSeq is -g(J₀). -/
lemma neg_limit_of_all_false (α : ℕ → Bool) (β J₀ J₁ : ℝ)
    {L_neg : ℝ}
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      |(fun n => -encodedSeq α β J₀ J₁ n) N - L_neg| < ε)
    (h : ∀ n, α n = false) :
    L_neg = -freeEnergyAtCoupling β J₀ :=
  limit_eq_of_eventually_const 0 hconv
    (fun n _hn => by simp [encodedSeq_of_all_false α β J₀ J₁ h n])

-- ========================================================================
-- Helper: ¬∃ → ∀ false for Bool sequences
-- ========================================================================

/-- For Bool sequences: ¬(∃ n, α n = true) → ∀ n, α n = false.
    Constructively valid because α n ∈ {false, true} is decidable. -/
lemma bool_not_exists_implies_all_false {α : ℕ → Bool}
    (h : ¬∃ n, α n = true) : ∀ n, α n = false := by
  intro n
  cases hb : α n
  · rfl
  · exact absurd ⟨n, hb⟩ h

-- ========================================================================
-- The main theorem: BMC → LPO
-- ========================================================================

/-- **BMC implies LPO (Theorem 5.3).**

    The proof encodes an arbitrary binary sequence α into a free energy
    sequence F(n) = -log(2·cosh(β·J(n))), applies BMC to obtain a limit,
    and uses the limit to decide whether ∀n, α(n) = false or ∃n, α(n) = true.

    The free energy g(J) = -log(2·cosh(βJ)) is justified combinatorially:
    Z_N(β,J) = (2·cosh(βJ))^N + (2·sinh(βJ))^N via the parity sieve,
    so f_∞(β,J) = -log(2·cosh(βJ)). No transfer matrices.

    Parameters β = 1, J₀ = 1, J₁ = 2 are fixed. Any positive values with
    J₀ < J₁ would work.

    The decision procedure:
    1. Apply BMC to -F (non-decreasing, bounded) → get L_neg
    2. Get N₁ from modulus with |(-F)(N₁) - L_neg| < δ/2
    3. Case split on runMax α N₁ (Bool — definitionally decidable)
       - true: extract witness k ≤ N₁ with α k = true
       - false: prove α ≡ false by contradiction using the gap δ -/
theorem lpo_of_bmc (hBMC : BMC) : LPO := by
  intro α
  -- Fix parameters
  set β : ℝ := 1
  set J₀ : ℝ := 1
  set J₁ : ℝ := 2
  -- Key positivity and ordering facts
  have hβ : (0 : ℝ) < β := one_pos
  have hJ₀ : (0 : ℝ) < J₀ := one_pos
  have hJ_lt : J₀ < J₁ := by norm_num
  have hJ_le : J₀ ≤ J₁ := le_of_lt hJ_lt
  -- Build the encoded sequence
  set F := encodedSeq α β J₀ J₁ with hF_def
  -- Apply BMC to -F (non-decreasing and bounded)
  have hMono : Monotone (fun n => -F n) := neg_encodedSeq_mono α hβ hJ₀ hJ_le
  have hBdd : ∀ n, (fun n => -F n) n ≤ -freeEnergyAtCoupling β J₁ :=
    neg_encodedSeq_bounded α hβ hJ₀ hJ_le
  obtain ⟨L_neg, hL⟩ := hBMC (fun n => -F n) (-freeEnergyAtCoupling β J₁) hMono hBdd
  -- Compute the gap δ > 0
  set δ := freeEnergyAtCoupling β J₀ - freeEnergyAtCoupling β J₁ with hδ_def
  have hδ : 0 < δ := freeEnergy_gap_pos hβ hJ₀ hJ_lt
  -- Get N₁ from the convergence modulus with ε = δ/2
  obtain ⟨N₁, hN₁⟩ := hL (δ / 2) (half_pos hδ)
  have hN₁_self := hN₁ N₁ (le_refl _)
  -- Case split on runMax α N₁ (definitionally decidable: it is a Bool)
  cases hm : runMax α N₁
  · -- Case: runMax α N₁ = false
    -- Then F(N₁) = g(J₀), so (-F)(N₁) = -g(J₀)
    left
    -- Prove ∀ n, α n = false by contradiction
    apply bool_not_exists_implies_all_false
    intro ⟨n₀, hn₀⟩
    -- If ∃ n₀ with α n₀ = true, then L_neg = -g(J₁)
    have hL_val := neg_limit_of_exists_true α hL hn₀
    -- F(N₁) = g(J₀) since runMax = false
    have hFN₁ : F N₁ = freeEnergyAtCoupling β J₀ := by
      simp only [hF_def, encodedSeq, couplingSeq, hm, Bool.false_eq_true, ite_false]
    -- Now: |(-F)(N₁) - L_neg| = |-g(J₀) - (-g(J₁))| = |g(J₁) - g(J₀)| = δ
    -- but the modulus gives < δ/2, contradiction
    have habs : |(-F N₁) - L_neg| = δ := by
      rw [hFN₁, hL_val]
      simp only [neg_sub_neg]
      rw [abs_sub_comm]
      exact abs_of_pos hδ
    -- hN₁_self says |(fun n => -F n) N₁ - L_neg| < δ / 2
    -- which is |(-F N₁) - L_neg| < δ / 2
    have : |(-F N₁) - L_neg| < δ / 2 := hN₁_self
    linarith
  · -- Case: runMax α N₁ = true
    -- Extract witness: ∃ k ≤ N₁ with α k = true
    right
    obtain ⟨k, _, hk⟩ := runMax_witness α (show runMax α N₁ = true from hm)
    exact ⟨k, hk⟩

end Papers.P9
