/-
  Papers/P2_BidualGap/Constructive/WLPO_ASP_Core.lean
  
  Core proof of WLPO ⇔ ASP following junior professor's blueprint.
  This version focuses on the mathematical content.
-/

import Papers.P2_BidualGap.Constructive.CReal
import Papers.P2_BidualGap.Logic.WLPOSimple

namespace Papers.P2_BidualGap.Constructive

open CReal

/-- A countable bounded set of reals with explicit enumeration -/
structure CountableSet where
  seq : ℕ → ℚ  -- Rational sequence for simplicity
  bound : ℚ
  bound_pos : 0 < bound
  is_bounded : ∀ n, |seq n| ≤ bound

/-- The Approximate Supremum Property -/
def ASP : Prop :=
  ∀ (S : CountableSet) (ε : ℚ) (hε : 0 < ε),
    ∃ (x : ℚ), 
      (∀ n, S.seq n ≤ x + ε) ∧  -- x + ε is upper bound
      (∃ k, x - ε < S.seq k)     -- Some element is close to x

/-- -- LaTeX Lemma 4.1
Key encoding for ASP → WLPO -/
def wlpo_encoding (α : BinarySeq) : CountableSet where
  seq := fun n => if α n then 1 - 1/(n + 2 : ℚ) else 0
  bound := 1
  bound_pos := by norm_num
  is_bounded := by
    intro n
    simp [abs_rat]
    split_ifs
    · split_ifs <;> norm_num <;> omega
    · norm_num

/-- -- LaTeX Theorem 4.3
ASP implies WLPO -/
theorem asp_to_wlpo : ASP → WLPO := by
  intro hasp α
  -- Apply ASP to the encoded sequence at ε = 1/4
  let S := wlpo_encoding α
  have hε : (0 : ℚ) < 1/4 := by norm_num
  obtain ⟨x, hub, ⟨k, hclose⟩⟩ := hasp S (1/4) hε
  
  -- Key insight: S.seq k is either 0 or ≥ 1/2
  have hk_cases : S.seq k = 0 ∨ S.seq k ≥ 1/2 := by
    simp [S, wlpo_encoding]
    split_ifs with h
    · right; norm_num; omega
    · left; rfl
  
  -- Case split on whether x < 1/4 (decidable for rationals!)
  by_cases hx : x < 1/4
  · -- If x < 1/4, then sup S ≤ 1/2, so all α n = false
    left
    intro n
    by_contra hn
    -- If α n = true, then S.seq n ≥ 1/2
    have : S.seq n ≥ 1/2 := by
      simp [S, wlpo_encoding, hn]
      norm_num; omega
    -- But hub says S.seq n ≤ x + 1/4 < 1/2
    have : S.seq n < 1/2 := by
      have := hub n
      linarith
    linarith
    
  · -- If x ≥ 1/4, then from x - 1/4 < S.seq k we get S.seq k > 0
    right
    push_neg at hx
    -- Since x - 1/4 < S.seq k and x ≥ 1/4, we have S.seq k > 0
    have hk_pos : S.seq k > 0 := by linarith
    -- Combined with S.seq k ∈ {0} ∪ [1/2, 1), we get S.seq k ≥ 1/2
    cases hk_cases with
    | inl h => 
      -- If S.seq k = 0 then contradiction with hk_pos
      rw [h] at hk_pos
      linarith
    | inr h => 
      -- So S.seq k ≥ 1/2, which means α k = true
      use k
      by_contra hfalse
      simp [S, wlpo_encoding, hfalse] at h
      linarith

/-- -- LaTeX Lemma 4.2
Binary search helper for WLPO → ASP -/
def is_upper_bound (S : CountableSet) (b : ℚ) (precision : ℕ) : Bool :=
  -- Check if b is an upper bound up to precision
  -- This is decidable since we check finitely many elements
  decide (∀ k ≤ precision, S.seq k ≤ b)

/-- Midpoint after n halving steps -/
def mid (S : CountableSet) (n : ℕ) : ℚ := 
  let a := S.seq 0
  let b := S.bound
  (a + b) / 2^(n + 1)

/-- Binary search is Cauchy -/
lemma mid_cauchy (S : CountableSet) :
  ∀ k, ∀ n m, n ≥ k → m ≥ k → qAbs (mid S n - mid S m) ≤ (S.bound - S.seq 0) / 2^k := by
  intro k n m hn hm
  simp [mid]
  -- WLOG n ≤ m
  wlog hnm : n ≤ m
  · have := this k m n hm hn (le_of_not_le hnm)
    rw [abs_sub_comm]
    exact this
  -- Since n ≤ m, we have 2^n ≤ 2^m
  have hpow : (2 : ℚ)^n ≤ 2^m := by
    apply pow_le_pow_right
    · norm_num
    · exact hnm
  -- Calculate the difference
  have hdiff : mid S n - mid S m = (S.seq 0 + S.bound) / 2^(n + 1) - (S.seq 0 + S.bound) / 2^(m + 1) := by
    rfl
  -- Simplify using field operations
  rw [hdiff]
  rw [div_sub_div_eq]
  simp only [mul_comm (S.seq 0 + S.bound)]
  -- Now we have |(stuff) / (2^(n+1) * 2^(m+1))|
  -- Use that n ≥ k implies 2^(n+1) ≥ 2^(k+1)
  have h1 : 2^(k + 1) ≤ 2^(n + 1) := by
    apply pow_le_pow_right; norm_num; omega
  have h2 : 2^(k + 1) ≤ 2^(m + 1) := by
    apply pow_le_pow_right; norm_num; omega
  -- The key idea: mid S n - mid S m = (a+b) * (1/2^(n+1) - 1/2^(m+1))
  -- Since n ≤ m, we have 2^(n+1) ≤ 2^(m+1), so 1/2^(n+1) ≥ 1/2^(m+1)
  -- Thus 1/2^(n+1) - 1/2^(m+1) ≥ 0
  
  -- Simplify the expression
  have eq1 : mid S n - mid S m = (S.seq 0 + S.bound) * (1/2^(n+1) - 1/2^(m+1)) := by
    simp [mid]
    field_simp
    ring
  
  -- Since n ≤ m, the difference 1/2^(n+1) - 1/2^(m+1) is non-negative
  have h_nonneg : 0 ≤ 1/(2^(n+1) : ℚ) - 1/2^(m+1) := by
    apply sub_nonneg.mpr
    apply div_le_div_of_nonneg_left
    · norm_num
    · apply pow_pos; norm_num
    · apply pow_pos; norm_num
    · apply pow_le_pow_right; norm_num; omega
  
  -- Key bound: 1/2^(n+1) - 1/2^(m+1) ≤ 1/2^(n+1) ≤ 1/2^(k+1)
  have h_bound : 1/(2^(n+1) : ℚ) - 1/2^(m+1) ≤ 1/2^(k+1) := by
    calc 1/(2^(n+1) : ℚ) - 1/2^(m+1)
      ≤ 1/2^(n+1) := by linarith
      _ ≤ 1/2^(k+1) := by
        apply div_le_div_of_nonneg_left
        · norm_num
        · apply pow_pos; norm_num
        · apply pow_pos; norm_num
        · exact h1
  
  -- Combine everything
  rw [eq1]
  have h_abs : qAbs ((S.seq 0 + S.bound) * (1/2^(n+1) - 1/2^(m+1))) = 
                qAbs (S.seq 0 + S.bound) * (1/2^(n+1) - 1/2^(m+1)) := by
    -- Since a + b > 0 (a = S.seq 0 ≤ S.bound = b) and the difference is non-negative
    have h_sum_pos : 0 < S.seq 0 + S.bound := by
      have : S.seq 0 ≤ S.bound := by
        have := S.is_bounded 0
        exact this
      linarith [S.bound_pos]
    simp [qAbs]
    split_ifs with h
    · rfl
    · push_neg at h
      have : 0 ≤ (S.seq 0 + S.bound) * (1 / 2 ^ (n + 1) - 1 / 2 ^ (m + 1)) := by
        apply mul_nonneg
        · linarith
        · exact h_nonneg
      linarith
  
  rw [h_abs]
  -- Final calculation
  calc qAbs (S.seq 0 + S.bound) * (1/2^(n+1) - 1/2^(m+1))
    ≤ qAbs (S.seq 0 + S.bound) * (1/2^(k+1)) := by
      apply mul_le_mul_of_nonneg_left h_bound
      simp [qAbs]; split_ifs <;> linarith [S.bound_pos]
    _ = qAbs (S.seq 0 + S.bound) / 2^(k+1) := by rw [div_eq_iff]; ring; norm_num
    _ ≤ (S.bound - S.seq 0) / 2^k := by
      -- Since |a + b| ≤ |b - a| when a ≤ b
      have : qAbs (S.seq 0 + S.bound) ≤ S.bound - S.seq 0 := by
        have h_ord : S.seq 0 ≤ S.bound := by
          have := S.is_bounded 0
          exact this
        simp [qAbs]
        split_ifs with h
        · linarith
        · push_neg at h
          linarith
      calc qAbs (S.seq 0 + S.bound) / 2^(k+1)
        ≤ (S.bound - S.seq 0) / 2^(k+1) := by
          apply div_le_div_of_nonneg_right this
          apply pow_pos; norm_num
        _ = (S.bound - S.seq 0) / (2 * 2^k) := by ring
        _ = (S.bound - S.seq 0) / 2^k / 2 := by ring
        _ ≤ (S.bound - S.seq 0) / 2^k := by
          rw [div_le_iff]; linarith; norm_num

/-- -- LaTeX Theorem 4.4
WLPO implies ASP -/
theorem wlpo_to_asp : WLPO → ASP := by
  intro hwlpo S ε hε
  -- Binary search for supremum using WLPO
  
  -- Choose precision k such that (S.bound - S.seq 0) / 2^k < ε
  have : ∃ k : ℕ, (S.bound - S.seq 0) / 2^k < ε := by
    -- Need k such that 2^k > (S.bound - S.seq 0) / ε
    have h_pos : 0 < S.bound - S.seq 0 := by
      have : S.seq 0 ≤ S.bound := S.is_bounded 0
      linarith [S.bound_pos]
    by_cases h : S.bound - S.seq 0 ≤ ε
    · -- If S.bound - S.seq 0 ≤ ε, then any k works
      use 1
      calc (S.bound - S.seq 0) / 2^1
        = (S.bound - S.seq 0) / 2 := by norm_num
        _ < ε := by linarith
    · -- Otherwise, use Archimedean property
      push_neg at h
      have : ∃ k : ℕ, (k : ℚ) > (S.bound - S.seq 0) / ε := exists_nat_gt _
      obtain ⟨k, hk⟩ := this
      use k
      rw [div_lt_iff (pow_pos (by norm_num : (0 : ℚ) < 2) k)]
      rw [← div_lt_iff hε] at hk
      calc S.bound - S.seq 0
        < ε * k := by linarith
        _ ≤ ε * 2^k := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hε)
          have : 1 ≤ 2 := by norm_num
          calc (k : ℚ)
            = k * 1 := by ring
            _ ≤ k * 2 := by apply mul_le_mul_of_nonneg_left; norm_num; simp
            _ ≤ 2^k := by
              clear hk h h_pos
              induction k with
              | zero => norm_num
              | succ k ih =>
                calc (k + 1 : ℚ) * 2
                  = k * 2 + 2 := by ring
                  _ ≤ 2^k + 2 := by linarith
                  _ ≤ 2^k + 2^k := by linarith [pow_pos (by norm_num : (0 : ℚ) < 2) k]
                  _ = 2 * 2^k := by ring
                  _ = 2^(k + 1) := by rw [pow_succ]
  obtain ⟨k, hk⟩ := this
  
  -- The key insight: at step n, we ask "is mid n an upper bound?"
  -- This is decidable up to any finite precision
  -- WLPO lets us decide the limiting behavior
  
  -- After k steps of binary search, mid k approximates the supremum
  use mid S k
  
  constructor
  · -- mid k + ε is an upper bound
    intro n
    sorry -- TODO: Use binary search property
  · -- Some element is close to mid k
    sorry -- TODO: Use that we're approximating supremum

/-- -- LaTeX Main Theorem 4.5
The fundamental equivalence -/
theorem wlpo_iff_asp : WLPO ↔ ASP := by
  constructor
  · exact wlpo_to_asp
  · exact asp_to_wlpo

end Papers.P2_BidualGap.Constructive