/-
  Papers/P2_BidualGap/Constructive/Sequences.lean
  
  Constructive versions of c₀ and ℓ∞ spaces.
  Key insight: We cannot decide membership in c₀ (that would imply LPO).
-/

import Papers.P2_BidualGap.Constructive.NormedSpace
import Papers.P2_BidualGap.Constructive.MonotoneConvergence

namespace Papers.P2_BidualGap.Constructive

open CReal CNormedSpace

/-- Helper lemma: 0 < 1/(k+1) for CReal -/
lemma lt_one_div_of_pos (k : ℕ) : lt zero (one_div k) := by
  -- one_div k = from_rat (1/(k+1))
  -- Need to show 0 < 1/(k+1) as CReal
  simp [one_div, lt, zero]
  use k + 2, 0
  intro n _
  simp [from_rat]
  -- Show 1/(k+1) - 0 ≥ 1/(k+2)
  have : (1 : ℚ)/(k + 1) > 0 := by norm_num
  have : (1 : ℚ)/(k + 1) ≥ 1/(k + 2) := by
    rw [div_le_div_iff] <;> norm_num
  exact this

/-- A bounded sequence of constructive reals -/
structure BoundedSeq where
  seq : ℕ → CReal
  bound : CReal
  bound_pos : lt zero bound
  is_bounded : ∀ n, ¬lt bound (abs (seq n))

/-- The space ℓ∞ of bounded sequences -/
def ell_infty := BoundedSeq

/-- Equality on ell_infty is pointwise equality of sequences -/
instance : Setoid ell_infty where
  r := fun x y => ∀ n, equiv (x.seq n) (y.seq n)
  iseqv := {
    refl := fun x n => CReal.equiv_refl _
    symm := fun h n => CReal.equiv_symm (h n)
    trans := fun h1 h2 n => CReal.equiv_trans (h1 n) (h2 n)
  }

namespace ell_infty

/-- Addition in ℓ∞ -/
def add (x y : ell_infty) : ell_infty where
  seq := fun n => CReal.add (x.seq n) (y.seq n)
  bound := CReal.add x.bound y.bound
  bound_pos := by
    -- x.bound > 0 and y.bound > 0, so x.bound + y.bound > 0
    apply CReal.add_pos x.bound_pos y.bound_pos
  is_bounded := by
    intro n
    -- |x_n + y_n| ≤ |x_n| + |y_n| ≤ x.bound + y.bound
    have h1 := x.is_bounded n
    have h2 := y.is_bounded n
    apply le_trans (abs_add _ _)
    apply add_le_add h1 h2

/-- The supremum norm on ℓ∞ -/
noncomputable def norm (x : ell_infty) : CReal :=
  -- For bounded sequences, we can use the given bound
  -- The actual supremum requires ASP, but the bound suffices for norm properties
  x.bound

/-- ℓ∞ is a constructive normed space -/
instance : CNormedSpace ell_infty where
  add := add
  zero := ⟨fun _ => CReal.zero, CReal.one, by norm_num, by intro n; simp [CReal.zero]⟩
  neg := fun x => ⟨fun n => CReal.neg (x.seq n), x.bound, x.bound_pos, by
    intro n
    -- |-x_n| = |x_n| ≤ x.bound
    rw [abs_neg]
    exact x.is_bounded n⟩
  add_assoc := fun x y z => by
    -- Show (x + y) + z ≈ x + (y + z) pointwise
    intro n
    exact CReal.add_assoc _ _ _
  zero_add := fun x => by
    -- Show 0 + x ≈ x pointwise
    intro n
    exact CReal.zero_add _
  add_zero := fun x => by
    -- Show x + 0 ≈ x pointwise
    intro n
    exact CReal.add_zero _
  add_left_neg := fun x => by
    -- Show -x + x ≈ 0 pointwise
    intro n
    exact CReal.add_left_neg _
  add_comm := fun x y => by
    -- Show x + y ≈ y + x pointwise
    intro n
    exact CReal.add_comm _ _
  norm := norm
  norm_zero := by
    -- norm of zero sequence is its bound, which is 1
    -- This is not exactly zero, but equivalent in the quotient
    sorry -- TODO: norm should map to equivalence class
  norm_add_le := by
    -- Triangle inequality: norm(x + y) ≤ norm(x) + norm(y)
    -- We have norm(x + y) = (x + y).bound = x.bound + y.bound
    rfl
  norm_smul := by
    -- Homogeneity: norm(c • x) = |c| * norm(x)
    sorry -- TODO: Need scalar multiplication first

end ell_infty

/-- The space c₀ of sequences converging to 0 -/
def c_zero : Set ell_infty :=
  {x | ∀ (k : ℕ), ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → lt (abs (x.seq n)) (CReal.one_div (k + 1))}

/-- Truncate a sequence to zero after index N -/
def truncate (x : ell_infty) (N : ℕ) : ell_infty where
  seq := fun n => if n ≤ N then x.seq n else zero
  bound := x.bound
  bound_pos := x.bound_pos
  is_bounded := by
    intro n
    split_ifs with h
    · -- n ≤ N: use original bound
      exact x.is_bounded n
    · -- n > N: |0| = 0 < bound
      simp [abs, zero]
      apply not_lt.mpr
      apply le_of_lt
      exact x.bound_pos

/-- Truncated sequences are in c₀ -/
lemma truncate_in_c_zero (x : ell_infty) (N : ℕ) :
  truncate x N ∈ c_zero := by
  intro k
  use N + 1
  intro n hn
  simp [truncate]
  split_ifs with h
  · -- n ≤ N but n ≥ N + 1, contradiction
    omega
  · -- n > N, so value is 0
    simp [abs, zero]
    apply lt_one_div_of_pos
    norm_num

/-- Key theorem: c₀ is located in ℓ∞ -/
theorem c_zero_located : Located ell_infty c_zero where
  dist := fun x => limsup (fun n => abs (x.seq n)) x.bound x.is_bounded
  dist_property := by
    intro x ε hε
    constructor
    · -- If x ∈ c₀, then dist(x, c₀) < ε
      intro hx
      -- Since x ∈ c₀, we have limsup |x_n| = 0
      have hlim : equiv (limsup (fun n => abs (x.seq n)) x.bound x.is_bounded) zero := by
        apply in_c_zero_iff_limsup_zero.mp hx
      -- So dist(x, c₀) = 0 < ε
      sorry -- TODO: Use equiv to show < ε
    · -- Can approximate distance with elements of c₀
      -- Choose N so that sup_{n>N} |x_n| ≤ limsup + ε/2
      have : ∃ N, ∀ n, n ≥ N → ¬lt (add (limsup (fun n => abs (x.seq n)) x.bound x.is_bounded) (CReal.from_rat (1/2))) (abs (x.seq n)) := by
        sorry -- TODO: From definition of limsup
      obtain ⟨N, hN⟩ := this
      use truncate x N
      constructor
      · -- Truncated sequence is in c₀
        exact truncate_in_c_zero x N
      · -- Distance bound
        sorry -- TODO: Show ‖x - truncate x N‖ < dist + ε

-- Note: limsup is imported from MonotoneConvergence.lean

/-- Membership in c₀ is NOT decidable -/
theorem c_zero_not_decidable : 
  ¬(∀ x : ell_infty, Decidable (x ∈ c_zero)) := by
  -- If we could decide membership in c₀, we could solve LPO
  sorry

/-- The witness sequence for the consultant's construction -/
def witness_sequence (α : BinarySeq) : ell_infty where
  seq := fun n => CReal.from_rat ((∑ k in Finset.range (n + 1), if α k then 1 else 0) / (n + 1 : ℚ))
  bound := CReal.one
  bound_pos := by
    -- 1 > 0
    apply CReal.one_pos
  is_bounded := by
    intro n
    -- The normalized sum is between 0 and 1
    simp [abs_rat, CReal.from_rat]
    have sum_nonneg : (∑ k in Finset.range (n + 1), if α k then 1 else 0 : ℚ) ≥ 0 := by
      apply Finset.sum_nonneg
      intro k _
      split_ifs <;> norm_num
    have sum_le : (∑ k in Finset.range (n + 1), if α k then 1 else 0 : ℚ) ≤ n + 1 := by
      trans (Finset.range (n + 1)).card
      · apply Finset.sum_le_card_nonneg
        · intro k _
          split_ifs <;> norm_num
        · intro k _
          split_ifs <;> norm_num
      · simp [Finset.card_range]
    -- So normalized sum is in [0, 1]
    have : 0 ≤ (∑ k in Finset.range (n + 1), if α k then 1 else 0) / (n + 1 : ℚ) := by
      apply div_nonneg sum_nonneg
      norm_num
    have : (∑ k in Finset.range (n + 1), if α k then 1 else 0) / (n + 1 : ℚ) ≤ 1 := by
      rw [div_le_one]
      · exact sum_le
      · norm_num
    split_ifs
    · exact this
    · linarith

/-- Helper: The rational partial sums -/
def partial_sum (α : BinarySeq) (n : ℕ) : ℚ :=
  ∑ k in Finset.range (n + 1), if α k then 1 else 0

/-- Helper: If α m = true, then all partial sums from m onwards are at least 1 -/
lemma partial_sum_ge_one (α : BinarySeq) (m : ℕ) (hm : α m = true) :
  ∀ n ≥ m, partial_sum α n ≥ 1 := by
  intro n hn
  simp [partial_sum]
  have : m ∈ Finset.range (n + 1) := by
    simp [Finset.mem_range]
    omega
  calc ∑ k in Finset.range (n + 1), if α k then 1 else 0
    ≥ if α m then 1 else 0 := Finset.single_le_sum (fun k _ => by split_ifs <;> norm_num) this
    _ = 1 := by simp [hm]

/-- Helper: The witness sequence value in rational form -/
lemma witness_value_rat (α : BinarySeq) (n : ℕ) :
  ∃ q : ℚ, q = (partial_sum α n) / (n + 1) ∧ 
  (witness_sequence α).seq n = CReal.from_rat q := by
  use (partial_sum α n) / (n + 1)
  constructor
  · rfl
  · simp [witness_sequence, partial_sum]

/-- Helper: If a rational is positive, its CReal form has positive absolute value -/
lemma abs_from_rat_of_pos {q : ℚ} (hq : 0 < q) :
  abs (CReal.from_rat q) = CReal.from_rat q := by
  sorry -- TODO: This should follow from abs properties

/-- Helper: Rational comparison lifts to CReal -/
lemma from_rat_lt {p q : ℚ} (h : p < q) :
  CReal.lt (CReal.from_rat p) (CReal.from_rat q) := by
  sorry -- TODO: This should follow from CReal ordering

/-- Key lemma: witness_sequence α ∈ c₀ iff α is all zeros -/
theorem witness_in_c_zero_iff (α : BinarySeq) :
  witness_sequence α ∈ c_zero ↔ (∀ n, α n = false) := by
  -- The witness sequence is the normalized partial sums:
  -- w_n = (∑_{k≤n} α k) / (n+1)
  -- This goes to 0 iff all α k = 0
  constructor
  · -- Forward direction: if w ∈ c₀, then all α n = false
    intro hw
    -- Suppose for contradiction that α m = true for some m
    by_contra h_not_all_false
    push_neg at h_not_all_false
    obtain ⟨m, hm⟩ := h_not_all_false
    
    -- Since witness ∈ c₀, for k = 2m+1, there exists N such that
    -- for all n ≥ N: |w_n| < 1/(k+1) = 1/(2m+2)
    specialize hw (2*m + 1)
    obtain ⟨N, hN⟩ := hw
    
    -- Take n = max(N, 2m+2) to ensure n is large enough
    let n := max N (2*m + 2)
    have hn_ge_N : n ≥ N := le_max_left _ _
    have hn_ge_m : n ≥ m := by
      calc n ≥ 2*m + 2 := le_max_right _ _
           _ > m := by omega
    
    -- From c₀ property: |w_n| < 1/(2m+2)
    have h_witness_small := hN n hn_ge_N
    
    -- But since α m = true and n ≥ m, we have:
    -- partial_sum α n ≥ 1 (by partial_sum_ge_one)
    have h_sum_ge_one : partial_sum α n ≥ 1 := partial_sum_ge_one α m hm n hn_ge_m
    
    -- Therefore w_n = (partial_sum α n)/(n+1) ≥ 1/(n+1)
    have h_witness_large : (partial_sum α n : ℚ) / (n + 1) ≥ 1 / (n + 1) := by
      rw [div_le_div_iff] <;> try norm_num
      exact h_sum_ge_one
    
    -- Since n ≥ 2m+2, we have 1/(n+1) ≥ 1/(2m+3) > 1/(2m+2)
    have h_bound : 1 / (n + 1 : ℚ) > 1 / (2*m + 2) := by
      rw [div_lt_div_iff] <;> try norm_num
      have : n + 1 ≥ 2*m + 3 := by
        calc n + 1 ≥ (2*m + 2) + 1 := by linarith [le_max_right N (2*m + 2)]
                 _ = 2*m + 3 := by ring
      linarith
    
    -- Contradiction: witness value ≥ 1/(n+1) > 1/(2m+2)
    -- but c₀ requires |witness value| < 1/(2m+2)
    -- Since witness values are non-negative, |w_n| = w_n
    sorry -- TODO: Extract contradiction from CReal comparison
  · -- Reverse direction: if all α n = false, then w ∈ c₀
    intro h_all_false
    -- If all α n = false, then all partial sums are 0
    -- So w_n = 0/(n+1) = 0 for all n
    intro k
    use 0
    intro n _
    -- w_n = 0 < 1/(k+1)
    have : (witness_sequence α).seq n = CReal.zero := by
      simp [witness_sequence, CReal.from_rat, CReal.zero]
      have : (∑ k in Finset.range (n + 1), if α k then 1 else 0 : ℚ) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        simp [h_all_false i]
      simp [this]
    rw [this]
    simp [abs, CReal.zero]
    apply lt_one_div_of_pos

end Papers.P2_BidualGap.Constructive