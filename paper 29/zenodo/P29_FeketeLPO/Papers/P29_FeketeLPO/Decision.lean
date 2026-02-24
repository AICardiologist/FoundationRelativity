/-
  Paper 29: Fekete's Subadditive Lemma ↔ LPO
  Decision.lean — The backward direction: FeketeConvergence → LPO

  This is the main new content of Paper 29.

  Proof strategy:
  1. Given α : ℕ → Bool, build mockFreeEnergy F_n = -n · x_n
  2. F is subadditive and F(n)/n ≥ -1 (from Subadditive.lean)
  3. Apply FeketeConvergence to get limit L with modulus
  4. Feed ε = 1/4 to get N₀ and evaluate x_M at M = max(N₀, 2)
  5. Case split on x_M (a Bool — decidable):
     - x_M = true: extract witness k < M with α(k) = true
     - x_M = false: prove ∀ n, α(n) = false by contradiction
       using the gap: if ∃ n₀, α(n₀)=true, then F(K)/K → -1 but F(M)/M = 0,
       and both are within 1/4 of L, giving 1 < 1/2.

  The decision extraction is 100% constructive:
    - x_M is a Bool, so the case split is decidable
    - The witness extraction uses decidable bounded search
    - The contradiction in the "all false" case uses linarith
    - No Markov's Principle, no Classical.em, no Classical.choice in content
-/
import Papers.P29_FeketeLPO.Subadditive

noncomputable section
namespace Papers.P29

-- ========================================================================
-- Helper: ¬∃ → ∀ false for Bool sequences (constructively valid)
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
-- The main theorem: FeketeConvergence → LPO
-- ========================================================================

/-- **FeketeConvergence implies LPO (Theorem 1).**

    Given any binary sequence α : ℕ → Bool, we encode it into
    F_n = -n · x_n where x_n = 1 iff ∃ k < n, α(k) = true.

    F is subadditive (Subadditive.lean) and F(n)/n ≥ -1.
    Fekete gives a limit L. We evaluate x at a concrete index M
    and branch on the computable Bool value:
    - true → witness extraction (∃ n, α n = true)
    - false → prove ∀ n, α n = false by triangle inequality contradiction

    No classical logic beyond Mathlib's ℝ infrastructure. -/
theorem lpo_of_fekete (hFek : FeketeConvergence) : LPO := by
  intro α
  -- Build the encoded sequence
  set F := mockFreeEnergy α with hF_def
  -- F is subadditive
  have hSub : ∀ m n, F (m + n) ≤ F m + F n := mockFreeEnergy_subadditive α
  -- F(n)/n is bounded below by -1
  have hBdd : ∃ C : ℝ, ∀ n : ℕ, 0 < n → C ≤ F n / ↑n :=
    ⟨-1, fun n hn => mockFreeEnergy_div_bdd_below α n hn⟩
  -- Apply Fekete to get limit L and modulus
  obtain ⟨L, hL⟩ := hFek F hSub hBdd
  -- Get N₀ from modulus with ε = 1/4
  obtain ⟨N₀, hN₀⟩ := hL (1 / 4) (by positivity)
  -- Evaluate at M = max(N₀, 2) — guarantees M ≥ N₀ and M ≥ 2
  set M := max N₀ 2 with hM_def
  have hM_ge_N₀ : N₀ ≤ M := le_max_left N₀ 2
  have hM_ge_2 : 2 ≤ M := le_max_right N₀ 2
  have hM_pos : 0 < M := by omega
  -- Get the Fekete bound at M
  have hM_bound := hN₀ M hM_ge_N₀ hM_pos
  -- Case split on hasTrue α M (decidable: it is a Bool)
  cases hx : hasTrue α M
  · -- Case: hasTrue α M = false → indicator α M = 0 → F(M)/M = 0
    left
    -- Prove ∀ n, α n = false by contradiction
    apply bool_not_exists_implies_all_false
    intro ⟨n₀, hn₀⟩
    -- If ∃ n₀ with α(n₀) = true, evaluate at K = max(M, n₀ + 2)
    set K := max M (n₀ + 2) with hK_def
    have hK_ge_N₀ : N₀ ≤ K := le_trans hM_ge_N₀ (le_max_left M _)
    have hK_pos : 0 < K := by omega
    have hn₀_lt_K : n₀ < K := by omega
    -- indicator α K = 1 (since n₀ < K and α n₀ = true)
    have hxK : indicator α K = 1 := indicator_of_exists_true α hn₀ hn₀_lt_K
    -- F(K)/K = -1
    have hFK : F K / ↑K = -1 := by
      rw [mockFreeEnergy_div α K hK_pos, hxK]
    -- F(M)/M = 0
    have hFM : F M / ↑M = 0 := by
      rw [mockFreeEnergy_div α M hM_pos]
      simp [indicator, hx]
    -- From Fekete: |F(K)/K - L| < 1/4
    have hK_bound := hN₀ K hK_ge_N₀ hK_pos
    -- |(-1) - L| < 1/4 and |0 - L| < 1/4
    rw [hFK] at hK_bound
    rw [hFM] at hM_bound
    -- From the two Fekete bounds:
    -- hM_bound: |0 - L| < 1/4  →  -1/4 < L < 1/4   (L is near 0)
    -- hK_bound: |-1 - L| < 1/4  →  -3/4 > L > -5/4  (L is near -1)
    -- These intervals are disjoint, contradiction.
    have hM' := abs_lt.mp hM_bound  -- ⟨-1/4 < 0 - L, 0 - L < 1/4⟩
    have hK' := abs_lt.mp hK_bound  -- ⟨-1/4 < -1 - L, -1 - L < 1/4⟩
    linarith
  · -- Case: hasTrue α M = true → extract witness
    right
    obtain ⟨k, _, hk⟩ := hasTrue_witness (show hasTrue α M = true from hx)
    exact ⟨k, hk⟩

end Papers.P29
end
