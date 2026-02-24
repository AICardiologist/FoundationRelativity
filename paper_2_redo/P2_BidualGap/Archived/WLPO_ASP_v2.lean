/-!
  Papers/P2_BidualGap/Constructive/WLPO_ASP_v2.lean
  
  WLPO ⇔ ASP (LaTeX §4)
  
  Following junior professor's blueprint:
  * WLPO: Weak Limited Principle of Omniscience  
  * ASP: For any **countable** bounded set S : Set CReal and ε > 0,  
         we can find x ∈ S within ε of sup S.
  
  Key insight: Keep everything countable to avoid impredicativity.
-/

import Papers.P2_BidualGap.Constructive.CReal
import Papers.P2_BidualGap.Logic.WLPOSimple

namespace Papers.P2_BidualGap.Constructive

open CReal

/-- Enumeration wrapper for countable subsets of CReal -/
structure CCountableSet where
  elem : ℕ → CReal
  bounded : ∃ B : ℚ, ∀ n, |((elem n).seq 0)| ≤ B  -- Use first element as proxy
  nonempty : ∃ m, True  -- Trivial but convenient

/-- isApproxSup S ε x means x is within ε of sup S
    but only uses ≤ on rationals to stay constructive -/
def isApproxSup (S : CCountableSet) (ε : ℚ) (hε : (0 : ℚ) < ε) (x : ℚ) : Prop :=
  (∀ n, S.elem n ≤ from_rat (x + ε)) ∧          -- x + ε is an upper bound
  (∃ k, from_rat x ≤ add (S.elem k) (from_rat (ε / 2)))  -- Some element almost reaches x

/-- Approximate Supremum Property (ASP) formulated constructively -/
def ASP : Prop :=
  ∀ S : CCountableSet, ∀ ε : ℚ, (0 : ℚ) < ε →
    ∃ x : ℚ, isApproxSup S ε hε x

/-- Helper: Encode a WLPO sequence as a bounded rational sequence -/
def encode_wlpo_seq (α : BinarySeq) : ℕ → ℚ :=
  fun n => if α n then (1 : ℚ) - 1/(n + 2 : ℚ) else 0

/-- -- LaTeX Theorem 4.3
Direction 1: ASP → WLPO -/
theorem wlpo_of_asp (hASP : ASP) : WLPO := by
  intro α
  -- Encode α into a countable set Sα of CReals
  let s := encode_wlpo_seq α
  let Sα : CCountableSet := {
    elem := fun n => from_rat (s n)
    bounded := by
      use 1
      intro n
      simp [encode_wlpo_seq]
      split_ifs
      · norm_num
      · norm_num
    nonempty := ⟨0, trivial⟩
  }
  
  -- Apply ASP at ε = 1/4
  have hε : (0 : ℚ) < 1/4 := by norm_num
  obtain ⟨q, hq⟩ := hASP Sα (1/4) hε
  
  -- Extract witness index k from approximation property
  obtain ⟨k, hk⟩ := hq.2
  
  -- Key: s k is either 0 or ≥ 1/2
  have hs : s k = 0 ∨ s k ≥ 1/2 := by
    simp [s, encode_wlpo_seq]
    split_ifs with h
    · right
      have : 1 - 1/(k + 2 : ℚ) ≥ 1/2 := by
        rw [sub_ge_iff_le_add]
        norm_num
        omega
      exact this
    · left; rfl
  
  -- Case analysis using decidable order on ℚ
  cases hs with
  | inl hzero =>
    -- s k = 0, so q ≤ 0 + 1/8 = 1/8
    -- Therefore q + 1/4 ≤ 3/8 < 1/2
    -- No element of Sα can be ≥ 1/2, so all α n = false
    left
    intro n
    by_contra htrue
    -- If α n = true then s n ≥ 1/2
    have hsn : s n ≥ 1/2 := by
      simp [s, encode_wlpo_seq, htrue]
      norm_num
      omega
    -- But upper bound property says s n ≤ q + 1/4 ≤ 3/8
    have hub := hq.1 n
    -- This gives contradiction: 1/2 ≤ 3/8
    sorry -- TODO: Extract rational bound from CReal inequality
    
  | inr hpos =>
    -- s k ≥ 1/2, which means α k = true
    right
    use k
    -- Need to show α k = true from s k ≥ 1/2
    by_contra hfalse
    simp [s, encode_wlpo_seq, hfalse] at hpos
    norm_num at hpos

/-- Helper: Approximate a CReal by its nth rational approximant -/
def approx_at (x : CReal) (n : ℕ) : ℚ := x.seq (x.mod n)

/-- Helper for WLPO → ASP: Binary sequence encoding upper bound test -/
def upper_bound_test (S : CCountableSet) (b : ℚ) (m : ℕ) : Bool :=
  -- "Does there exist k ≤ m such that S.elem k > b - 1/(m+1)?"
  -- This is decidable since we only check finitely many k
  decide (∃ k ≤ m, approx_at (S.elem k) m > b - 1/(m + 1 : ℚ))

/-- -- LaTeX Theorem 4.4
Direction 2: WLPO → ASP -/
theorem asp_of_wlpo (hWLPO : WLPO) : ASP := by
  intro S ε hε
  -- Get rational bound from S.bounded
  obtain ⟨B₀, hB₀⟩ := S.bounded
  
  -- Construct binary sequence β
  let β : BinarySeq := fun m => upper_bound_test S B₀ m
  
  -- Apply WLPO to decide β
  cases hWLPO β with
  | inl hAllFalse =>
    -- All β m = false means sup S ≤ B₀
    -- Take x = B₀ - ε/2
    use B₀ - ε/2
    constructor
    · -- Upper bound property
      intro n
      sorry -- TODO: Show S.elem n ≤ B₀ - ε/2 + ε
    · -- Witness property
      obtain ⟨k, _⟩ := S.nonempty
      use k
      sorry -- TODO: Show approximation
      
  | inr ⟨m, hmtrue⟩ =>
    -- β m = true gives us a witness near B₀
    sorry -- TODO: Extract witness and construct supremum approximant

/-- -- LaTeX Main Bridge Theorem
The equivalence that enables everything -/
theorem wlpo_iff_asp : WLPO ↔ ASP := by
  constructor
  · exact asp_of_wlpo
  · exact wlpo_of_asp

end Papers.P2_BidualGap.Constructive