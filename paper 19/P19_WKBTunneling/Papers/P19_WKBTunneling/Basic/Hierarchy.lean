/-
Papers/P19_WKBTunneling/Basic/Hierarchy.lean
Proofs of the constructive hierarchy: BISH < LLPO < WLPO < LPO.

We prove the forward implications:
  LPO → WLPO → LLPO

The reverse implications do NOT hold over BISH (strict separations).
We do not prove the separations here — those are model-theoretic results
from the constructive analysis literature.
-/
import Papers.P19_WKBTunneling.Basic.LLPO

namespace Papers.P19

open Nat

-- ========================================================================
-- LPO → WLPO
-- ========================================================================

/-- LPO implies WLPO: if you can decide ∃n, α(n)=true, you can certainly
    decide its double negation. -/
theorem lpo_implies_wlpo : LPO → WLPO := by
  intro hLPO α
  rcases hLPO α with h_all | ⟨n, hn⟩
  · exact Or.inl h_all
  · right
    intro h_all
    exact absurd (h_all n) (by simp [hn])

-- ========================================================================
-- LPO → LLPO
-- ========================================================================

/-- LPO implies LLPO: if you can find any true entry, you can determine
    its parity. -/
theorem lpo_implies_llpo : LPO → LLPO := by
  intro hLPO α _hamo
  rcases hLPO α with h_all | ⟨n, hn⟩
  · -- All false: both conclusions hold
    exact Or.inl (fun k => h_all (2 * k))
  · -- Found a true at index n; determine its parity
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- n = 2*k (even): the true is at an even index
      -- So all odd-indexed must be false (by AtMostOne)
      right
      intro j
      by_contra h
      push_neg at h
      simp at h
      have : 2 * j + 1 = n := _hamo (2 * j + 1) n h hn
      omega
    · -- n = 2*k + 1 (odd): the true is at an odd index
      -- So all even-indexed must be false (by AtMostOne)
      left
      intro j
      by_contra h
      push_neg at h
      simp at h
      have : 2 * j = n := _hamo (2 * j) n h hn
      omega

-- ========================================================================
-- WLPO → LLPO
-- ========================================================================

/-- WLPO implies LLPO.
    Given α with AtMostOne, apply WLPO to the even subsequence β(n) = α(2n).
    - If ∀n, β(n) = false: all even-indexed are false (left disjunct of LLPO).
    - If ¬∀n, β(n) = false: some even-indexed entry is true, so by AtMostOne,
      all odd-indexed must be false (right disjunct of LLPO). -/
theorem wlpo_implies_llpo : WLPO → LLPO := by
  intro hWLPO α hamo
  -- Define the even subsequence
  let β : ℕ → Bool := fun n => α (2 * n)
  rcases hWLPO β with h_all | h_not_all
  · -- All even-indexed are false
    exact Or.inl h_all
  · -- Not all even-indexed are false → some even-indexed is true
    -- Therefore all odd-indexed must be false by AtMostOne
    right
    intro j
    by_contra h
    push_neg at h
    simp at h
    -- α(2j+1) = true. If any α(2k) were true, AtMostOne gives 2k = 2j+1 — impossible.
    apply h_not_all
    intro k
    by_contra hk
    push_neg at hk
    simp at hk
    -- α(2k) = true and α(2j+1) = true, AtMostOne gives 2k = 2j+1
    have := hamo (2 * k) (2 * j + 1) hk h
    omega

-- ========================================================================
-- Summary: the full chain
-- ========================================================================

/-- The full hierarchy: LPO → WLPO → LLPO.
    (The reverse implications do NOT hold over BISH.) -/
theorem lpo_implies_llpo' : LPO → LLPO :=
  fun h => wlpo_implies_llpo (lpo_implies_wlpo h)

end Papers.P19
