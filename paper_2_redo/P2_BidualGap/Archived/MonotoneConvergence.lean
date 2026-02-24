/-
  Papers/P2_BidualGap/Constructive/MonotoneConvergence.lean
  
  The Monotone Convergence Theorem in constructive mathematics.
  This is essential for showing c₀ is located in ℓ∞.
-/

import Papers.P2_BidualGap.Constructive.CReal

namespace Papers.P2_BidualGap.Constructive

open CReal

/-- A sequence is monotone decreasing -/
def MonotoneDecreasing (f : ℕ → CReal) : Prop :=
  ∀ n, ¬lt (f n) (f (n + 1))

/-- A sequence is bounded below -/
def BoundedBelow (f : ℕ → CReal) (b : CReal) : Prop :=
  ∀ n, ¬lt (f n) b

/-- Explicit convergence modulus for monotone sequences -/
noncomputable def convergence_modulus (f : ℕ → ℚ) (b : ℚ) (ε : ℚ) (hε : 0 < ε) : ℕ :=
  Nat.find (by
    -- The sequence f n - b is decreasing and positive
    -- By Archimedean property, eventually f n - b < ε
    have : ∃ n, f n - b < ε := by
      -- Key insight: if f is monotone decreasing and bounded below by b,
      -- and if f 0 - b < N * ε for some N, then f N - b < ε
      have h1 : ∃ N : ℕ, (N : ℚ) * ε > f 0 - b := by
        by_cases h : f 0 - b ≤ 0
        · -- If f 0 ≤ b, then f n - b < ε for all n since ε > 0
          use 1
          linarith
        · -- If f 0 > b, use Archimedean property
          push_neg at h
          have : ∃ N : ℕ, (N : ℚ) > (f 0 - b) / ε := exists_nat_gt _
          obtain ⟨N, hN⟩ := this
          use N
          rw [mul_comm, ← div_lt_iff hε]
          exact hN
      obtain ⟨N, hN⟩ := h1
      use N
      -- Since f is decreasing: f 0 ≥ f 1 ≥ ... ≥ f N ≥ b
      -- We have f 0 - f N ≥ 0
      -- Also, for each step: f i - f (i+1) ≥ 0
      -- The total drop f 0 - f N is at least the sum of N drops
      -- But we need more structure on f to prove this constructively
      -- For now, we assume this property holds
      sorry -- TODO: Requires monotone decreasing structure
    exact this)

/-- The key lemma: monotone bounded sequences are Cauchy -/
theorem monotone_bounded_is_cauchy {f : ℕ → CReal} 
  (hdec : MonotoneDecreasing f) 
  (hbound : ∃ b, BoundedBelow f b) :
  ∀ k, ∃ N, ∀ n m, n ≥ N → m ≥ N → 
    ¬lt (one_div k) (dist (f n) (f m)) := by
  intro k
  obtain ⟨b, hb⟩ := hbound
  -- Use the explicit modulus
  let N := convergence_modulus (fun n => (f n).seq n) (b.seq 0) (1 / (k + 1 : ℚ)) (by norm_num)
  use N
  intro n m hn hm
  -- Since f is decreasing and n,m ≥ N, both are close to the limit
  sorry -- TODO: Complete using monotonicity

/-- Construct the limit of a Cauchy sequence of CReals -/
noncomputable def cauchy_limit (f : ℕ → CReal) 
  (hcauchy : ∀ k, ∃ N, ∀ n m, n ≥ N → m ≥ N → 
    ¬lt (one_div k) (dist (f n) (f m))) : CReal where
  -- Extract diagonal sequence with modulus
  seq := fun k => (f (Classical.choose (hcauchy k))).seq k
  mod := fun k => 
    let N := Classical.choose (hcauchy (2 * k))
    max N ((f N).mod k)
  is_cauchy := by
    intro n m k hn hm
    -- Use that f is Cauchy and each f(i) is a CReal
    sorry

/-- The Monotone Convergence Theorem (constructive version) -/
theorem monotone_convergence {f : ℕ → CReal} 
  (hdec : MonotoneDecreasing f)
  (hbound : ∃ b, BoundedBelow f b) :
  ∃ (limit : CReal), ∀ k, ∃ N, ∀ n, n ≥ N → 
    ¬lt (one_div k) (dist (f n) limit) := by
  -- Step 1: Show f is Cauchy
  have hcauchy := monotone_bounded_is_cauchy hdec hbound
  -- Step 2: Construct the limit
  use cauchy_limit f hcauchy
  -- Step 3: Show convergence
  intro k
  obtain ⟨N, hN⟩ := hcauchy (2 * k)
  use N
  intro n hn
  -- Use Cauchy property and construction of limit
  sorry

/-- Corollary: Decreasing sequences bounded below by 0 converge -/
theorem decreasing_positive_converges {f : ℕ → CReal}
  (hdec : MonotoneDecreasing f)
  (hpos : ∀ n, ¬lt (f n) zero) :
  ∃ (limit : CReal), ∀ k, ∃ N, ∀ n, n ≥ N → 
    ¬lt (one_div k) (dist (f n) limit) := by
  apply monotone_convergence hdec
  use zero
  exact hpos

/-- The limit superior as a constructive operation -/
noncomputable def limsup_aux (x : ℕ → CReal) (bound : CReal)
  (hbound : ∀ n, ¬lt bound (abs (x n))) : ℕ → CReal :=
  fun N => sorry -- sup_{n ≥ N} |x n| requires careful construction

/-- Limit superior exists for bounded sequences -/
theorem limsup_exists (x : ℕ → CReal) (bound : CReal)
  (hbound : ∀ n, ¬lt bound (abs (x n))) :
  ∃ (l : CReal), ∀ k, ∃ N, ∀ n, n ≥ N → 
    ¬lt (one_div k) (dist (limsup_aux x bound hbound n) l) := by
  -- The sequence of tail suprema is decreasing and bounded below by 0
  have hdec : MonotoneDecreasing (limsup_aux x bound hbound) := by
    sorry -- Tail suprema decrease
  have hpos : ∀ n, ¬lt (limsup_aux x bound hbound n) zero := by
    -- limsup_aux computes sup of absolute values, which are non-negative
    intro n
    -- The supremum of non-negative values is non-negative
    sorry -- TODO: Requires explicit construction of limsup_aux
  exact decreasing_positive_converges hdec hpos

/-- The limit superior as the limit of tail suprema -/
noncomputable def limsup (x : ℕ → CReal) (bound : CReal)
  (hbound : ∀ n, ¬lt bound (abs (x n))) : CReal :=
  Classical.choose (limsup_exists x bound hbound)

/-- Key property: x ∈ c₀ iff limsup |x_n| = 0 -/
theorem in_c_zero_iff_limsup_zero {x : ell_infty} :
  x ∈ c_zero ↔ equiv (limsup (fun n => abs (x.seq n)) x.bound x.is_bounded) zero := by
  constructor
  · intro hx
    -- If x → 0, then limsup = 0
    sorry
  · intro hlim
    -- If limsup = 0, then x → 0
    sorry

end Papers.P2_BidualGap.Constructive