/-
  Paper 43: What the Ceiling Means
  Hierarchy/LPOImpliesMP.lean — Theorem 1: LPO strictly implies MP

  The BISH + LPO ceiling already contains MP.
  Any physical system whose calibration involves a thermodynamic
  limit (LPO) automatically has MP available.

  Full hierarchy:
    LPO → MP       (Theorem 1)
    LPO → WLPO     (standard)
    WLPO → LLPO    (standard)
    WLPO and MP are independent (model-theoretic)
-/
import Papers.P43_Actualisation.Defs.Principles

namespace Papers.P43

-- ========================================================================
-- Theorem 1: LPO ⟹ MP
-- ========================================================================

/-- Theorem 1. LPO strictly implies MP.
    Proof: Let α satisfy ¬(∀n, α(n) = false). By LPO:
    (∃n, α(n) = true) ∨ (∀n, α(n) = false).
    The second disjunct contradicts the hypothesis.
    Therefore the first holds. -/
theorem lpo_implies_mp : LPO → MarkovPrinciple := by
  intro hLPO α hne
  rcases hLPO α with hall | ⟨n, hn⟩
  · exact absurd hall hne
  · exact ⟨n, hn⟩

-- ========================================================================
-- Remaining hierarchy
-- ========================================================================

/-- LPO implies WLPO. -/
theorem lpo_implies_wlpo : LPO → WLPO := by
  intro hLPO α
  rcases hLPO α with h_all | ⟨n, hn⟩
  · exact Or.inl h_all
  · right
    intro h_all
    exact absurd (h_all n) (by simp [hn])

/-- WLPO implies LLPO. -/
theorem wlpo_implies_llpo : WLPO → LLPO := by
  intro hWLPO α hamo
  let β : ℕ → Bool := fun n => α (2 * n)
  rcases hWLPO β with h_all | h_not_all
  · exact Or.inl h_all
  · right
    intro j
    by_contra h
    push_neg at h
    simp at h
    apply h_not_all
    intro k
    by_contra hk
    push_neg at hk
    simp at hk
    have := hamo (2 * k) (2 * j + 1) hk h
    omega

/-- LPO implies LLPO (transitivity). -/
theorem lpo_implies_llpo : LPO → LLPO :=
  fun h => wlpo_implies_llpo (lpo_implies_wlpo h)

-- Strictness notes (model-theoretic, not formalized):
-- • MP does not imply LPO: the recursive model satisfies MP but not LPO.
-- • WLPO does not imply MP: there exist models of WLPO where MP fails.
-- • WLPO + MP = LPO (Ishihara 2006).
-- • LLPO is independent of MP (Bridges-Richman 1987).

end Papers.P43
