/-
Papers/P8_LPO_IsingBound/PartB_RunMax.lean
Properties of the running maximum of a binary sequence.

Key results:
  - runMax is non-decreasing (Monotone in Bool's order)
  - runMax α n = false ↔ ∀ k ≤ n, α k = false
  - runMax α n = true  ↔ ∃ k, k ≤ n ∧ α k = true
  - If α ≡ false, runMax stays false
  - Once α has a true, runMax stays true
-/
import Papers.P8_LPO_IsingBound.PartB_Defs

namespace Papers.P8

-- ========================================================================
-- Monotonicity
-- ========================================================================

/-- runMax is non-decreasing: runMax α n ≤ runMax α (n+1). -/
lemma runMax_le_succ (α : ℕ → Bool) (n : ℕ) :
    runMax α n ≤ runMax α (n + 1) := by
  simp only [runMax]
  exact Bool.right_le_or _ _

/-- runMax is monotone (non-decreasing in Bool's order false ≤ true). -/
lemma runMax_mono (α : ℕ → Bool) : Monotone (runMax α) :=
  monotone_nat_of_le_succ (runMax_le_succ α)

-- ========================================================================
-- Characterization: false iff all previous terms false
-- ========================================================================

/-- runMax α n = false iff all α(k) for k ≤ n are false. -/
lemma runMax_false_iff (α : ℕ → Bool) (n : ℕ) :
    runMax α n = false ↔ ∀ k, k ≤ n → α k = false := by
  induction n with
  | zero =>
    simp only [runMax]
    constructor
    · intro h k hk
      have : k = 0 := by omega
      subst this; exact h
    · intro h; exact h 0 (le_refl 0)
  | succ n ih =>
    simp only [runMax, Bool.or_eq_false_iff]
    constructor
    · rintro ⟨ha, hr⟩
      rw [ih] at hr
      intro k hk
      by_cases hkn : k ≤ n
      · exact hr k hkn
      · have : k = n + 1 := by omega
        subst this; exact ha
    · intro h
      exact ⟨h (n + 1) (le_refl _), ih.mpr (fun k hk => h k (Nat.le_succ_of_le hk))⟩

-- ========================================================================
-- Characterization: true iff some previous term true
-- ========================================================================

/-- runMax α n = true iff ∃ k ≤ n with α k = true. -/
lemma runMax_true_iff (α : ℕ → Bool) (n : ℕ) :
    runMax α n = true ↔ ∃ k, k ≤ n ∧ α k = true := by
  constructor
  · -- If runMax is true, find a witness (contrapositive of false_iff)
    intro h
    by_contra h_neg
    simp only [not_exists, not_and] at h_neg
    have hfalse : runMax α n = false := (runMax_false_iff α n).mpr (fun k hk => by
      specialize h_neg k hk
      cases hb : α k
      · rfl
      · exact absurd hb h_neg)
    simp [hfalse] at h
  · -- If there's a witness, show runMax is true (contrapositive of false_iff)
    rintro ⟨k, hk, hak⟩
    by_contra h
    rw [Bool.not_eq_true] at h
    have := (runMax_false_iff α n).mp h k hk
    simp [this] at hak

-- ========================================================================
-- Derived properties
-- ========================================================================

/-- If all terms of α are false, runMax stays false. -/
lemma runMax_of_all_false (α : ℕ → Bool) (h : ∀ n, α n = false) (n : ℕ) :
    runMax α n = false :=
  (runMax_false_iff α n).mpr (fun k _ => h k)

/-- Once α has a true value at n₀, runMax is true for all n ≥ n₀. -/
lemma runMax_of_exists_true (α : ℕ → Bool) {n₀ : ℕ} (h : α n₀ = true)
    {n : ℕ} (hn : n₀ ≤ n) :
    runMax α n = true :=
  (runMax_true_iff α n).mpr ⟨n₀, hn, h⟩

/-- If runMax α n = true, extract a witness k ≤ n with α k = true. -/
lemma runMax_witness (α : ℕ → Bool) {n : ℕ} (h : runMax α n = true) :
    ∃ k, k ≤ n ∧ α k = true :=
  (runMax_true_iff α n).mp h

end Papers.P8
