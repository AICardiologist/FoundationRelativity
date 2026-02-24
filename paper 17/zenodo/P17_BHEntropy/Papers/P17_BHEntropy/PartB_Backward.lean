/-
Papers/P17_BHEntropy/PartB_Backward.lean
Backward direction: Entropy Convergence → LPO.

This is the core new content. The proof encodes an arbitrary binary sequence
α : ℕ → Bool into an entropy density sequence S_alpha, uses the convergence
hypothesis to obtain a limit, and uses the entropy density gap to decide α.

The encoding uses:
  1. Running maximum m(n) = max(α(0),...,α(n))
  2. Area A(n) = if m(n) then A_hi else A_lo (with A_lo < A_hi)
  3. Entropy density S(n) = entropy_density(A(n), γ, δ)
  4. Gap: entropy_density(A_hi) - entropy_density(A_lo) > gap > 0

Decision procedure:
  - Apply convergence hypothesis to get limit L
  - Get N₁ from modulus with |S(N₁) - L| < gap/2
  - Case split on runMax α N₁ (decidable: it is a Bool)
  - If true: witness extraction
  - If false: contradiction argument

Follows Paper 8's PartB_Backward.lean structure.
-/
import Papers.P17_BHEntropy.PartB_EncodedSeq

namespace Papers.P17

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

/-- If ∃ n₀ with α(n₀) = true, the limit of S_alpha is entropy_density A_hi. -/
lemma limit_of_exists_true (α : ℕ → Bool)
    {A_lo A_hi gamma delta : ℝ}
    {hA_lo : A_lo > 0} {hA_hi : A_hi > 0}
    {hg : gamma > 0} {hd : delta > 0}
    {L : ℝ}
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      |S_alpha α A_lo A_hi gamma delta hA_lo hA_hi hg hd N - L| < ε)
    {n₀ : ℕ} (h : α n₀ = true) :
    L = entropy_density A_hi gamma delta hA_hi hg hd :=
  limit_eq_of_eventually_const n₀ hconv
    (fun _n hn => S_alpha_of_exists_true α A_lo A_hi gamma delta hA_lo hA_hi hg hd h hn)

/-- If α ≡ false, the limit of S_alpha is entropy_density A_lo. -/
lemma limit_of_all_false (α : ℕ → Bool)
    (A_lo A_hi gamma delta : ℝ)
    (hA_lo : A_lo > 0) (hA_hi : A_hi > 0)
    (hg : gamma > 0) (hd : delta > 0)
    {L : ℝ}
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      |S_alpha α A_lo A_hi gamma delta hA_lo hA_hi hg hd N - L| < ε)
    (h : ∀ n, α n = false) :
    L = entropy_density A_lo gamma delta hA_lo hg hd :=
  limit_eq_of_eventually_const 0 hconv
    (fun n _hn => S_alpha_of_all_false α A_lo A_hi gamma delta hA_lo hA_hi hg hd h n)

-- ========================================================================
-- The main theorem: Entropy Convergence → LPO
-- ========================================================================

/-- **Entropy convergence implies LPO (Theorem 4.3).**

    The proof encodes an arbitrary binary sequence α into an entropy density
    sequence S_alpha(n), applies the convergence hypothesis to obtain a limit,
    and uses the entropy density gap to decide whether ∀n, α(n) = false or
    ∃n, α(n) = true.

    The decision procedure:
    1. Obtain A_lo, A_hi, gap from the entropy density gap lemma
    2. Apply convergence to S_alpha → get L
    3. Get N₁ from modulus with |S(N₁) - L| < gap/2
    4. Case split on runMax α N₁ (Bool — definitionally decidable)
       - true: extract witness k ≤ N₁ with α k = true
       - false: prove α ≡ false by contradiction using the gap δ -/
theorem entropy_convergence_implies_lpo
    (gamma : ℝ) (hg : gamma > 0)
    (delta : ℝ) (hd : delta > 0)
    {A_lo A_hi : ℝ} {hA_lo : A_lo > 0} {hA_hi : A_hi > 0}
    (h_conv : EntropyConvergence A_lo A_hi gamma delta hA_lo hA_hi hg hd)
    {gap : ℝ} (hgap : gap > 0)
    (h_density_gap :
      entropy_density A_hi gamma delta hA_hi hg hd -
        entropy_density A_lo gamma delta hA_lo hg hd > gap) :
    LPO := by
  intro α
  -- Build the encoded sequence
  set S := S_alpha α A_lo A_hi gamma delta hA_lo hA_hi hg hd with hS_def
  set s_lo := entropy_density A_lo gamma delta hA_lo hg hd
  set s_hi := entropy_density A_hi gamma delta hA_hi hg hd
  -- Apply convergence hypothesis to get limit L
  obtain ⟨L, hL⟩ := h_conv α
  -- Get N₁ from the convergence modulus with ε = gap/2
  obtain ⟨N₁, hN₁⟩ := hL (gap / 2) (half_pos hgap)
  have hN₁_self := hN₁ N₁ (le_refl _)
  -- Case split on runMax α N₁ (definitionally decidable: it is a Bool)
  cases hm : runMax α N₁
  · -- Case: runMax α N₁ = false
    -- Then S(N₁) = s_lo
    left
    -- Prove ∀ n, α n = false by contradiction
    apply bool_not_exists_implies_all_false
    intro ⟨n₀, hn₀⟩
    -- If ∃ n₀ with α(n₀) = true, then L = s_hi
    have hL_val := limit_of_exists_true α hL hn₀
    -- S(N₁) = s_lo since runMax = false
    have hSN₁ : S N₁ = s_lo := by
      show S_alpha α A_lo A_hi gamma delta hA_lo hA_hi hg hd N₁ = s_lo
      unfold S_alpha
      rw [hm]
    -- Now: |S(N₁) - L| = |s_lo - s_hi| = s_hi - s_lo > gap
    -- but the modulus gives < gap/2, contradiction
    have habs : |S N₁ - L| = s_hi - s_lo := by
      rw [hSN₁, hL_val]
      rw [abs_of_nonpos (by linarith : s_lo - s_hi ≤ 0)]
      ring
    linarith
  · -- Case: runMax α N₁ = true
    -- Extract witness: ∃ k ≤ N₁ with α k = true
    right
    obtain ⟨k, _, hk⟩ := runMax_witness α (show runMax α N₁ = true from hm)
    exact ⟨k, hk⟩

end Papers.P17
