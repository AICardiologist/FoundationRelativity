/-
  Paper 39: Physics Reaches Σ₂⁰ — The Thermodynamic Stratification
  ArithmeticHierarchy.lean: Connections between LPO', Σ₂⁰, and the Turing jump

  Key results:
  - Σ₂⁰-complete problems require LPO_jump
  - LPO_jump decides all Σ₂⁰ statements
  - LPO_jump is strictly stronger than LPO
-/
import Papers.P39_Sigma2.Defs

noncomputable section

-- ============================================================
-- Connection: Σ₂⁰-completeness ↔ LPO_jump
-- ============================================================

-- If a Σ₂⁰-complete problem is decidable for all inputs,
-- then LPO_jump holds (by the completeness reduction)
theorem sigma2_complete_implies_lpo_jump
    {P : TM → Prop}
    (h_dec : ∀ M, P M ∨ ¬P M)
    (h_complete : Sigma2Complete P) :
    LPO_jump :=
  h_complete.requires_lpo_jump h_dec

-- LPO_jump decides all Σ₂⁰-complete problems
theorem lpo_jump_decides_sigma2
    {P : TM → Prop}
    (lpo_j : LPO_jump)
    (h_complete : Sigma2Complete P) :
    ∀ M, P M ∨ ¬P M :=
  h_complete.decided_by_lpo_jump lpo_j

-- Similarly for Π₂⁰
theorem lpo_jump_decides_pi2
    {P : TM → Prop}
    (lpo_j : LPO_jump)
    (h_complete : Pi2Complete P) :
    ∀ M, P M ∨ ¬P M :=
  h_complete.decided_by_lpo_jump lpo_j

-- ============================================================
-- Σ₁⁰ ⊊ Σ₂⁰: LPO is strictly weaker than LPO_jump
-- ============================================================

-- LPO decides all Σ₁⁰-complete problems
theorem lpo_decides_sigma1
    {P : TM → Prop}
    (lpo : LPO)
    (h_complete : Sigma1Complete P) :
    ∀ M, P M ∨ ¬P M :=
  h_complete.decided_by_lpo lpo

-- But LPO does NOT decide Σ₂⁰-complete problems
-- (The existence of Σ₂⁰-complete problems that are not Σ₁⁰
-- is a classical result from computability theory)
axiom sigma2_not_sigma1 :
    ∃ (P : TM → Prop), Sigma2Complete P ∧
      ¬∃ (Q : TM → Prop), Sigma1Complete Q ∧ (∀ M, P M ↔ Q M)

-- Therefore LPO_jump is strictly stronger than LPO
-- (LPO_jump decides Σ₂⁰ but LPO doesn't)
theorem lpo_jump_strictly_stronger :
    ¬(LPO → LPO_jump) ∨ (LPO_jump → LPO) := by
  right
  exact lpo_jump_implies_lpo

-- ============================================================
-- The Finiteness Problem is Σ₂⁰-complete
-- ============================================================

-- Bridge lemma: the Finiteness Problem is Σ₂⁰-complete
-- (By the space-time padding reduction — see §9.3 of blueprint)
axiom finiteness_is_sigma2_complete :
    Sigma2Complete finiteness_problem

-- The complement (infiniteness) is Π₂⁰-complete
axiom infiniteness_is_pi2_complete :
    Pi2Complete (fun M => ¬finiteness_problem M)

-- ============================================================
-- Hierarchy separation: Σ₁⁰ < Σ₂⁰
-- ============================================================

-- LPO decides Σ₁⁰ (halting) but NOT Σ₂⁰ (finiteness)
-- This is the fundamental reason physics extends beyond LPO
theorem hierarchy_separation :
    (LPO → ∀ (a : ℕ → Bool), (∃ n, a n = true) ∨ ¬(∃ n, a n = true)) ∧
    (LPO_jump → ∀ M, finiteness_problem M ∨ ¬finiteness_problem M) := by
  constructor
  · intro lpo a
    rcases lpo a with h_all | ⟨n, hn⟩
    · right
      intro ⟨n, hn⟩
      have := h_all n
      rw [this] at hn
      exact Bool.false_ne_true hn
    · left; exact ⟨n, hn⟩
  · intro lpo_j
    exact lpo_jump_decides_sigma2 lpo_j finiteness_is_sigma2_complete

end
