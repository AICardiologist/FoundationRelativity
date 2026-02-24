/-
  Paper 38: The Grandfather is LPO — Wang Tiling
  Ceiling.lean: Theorem 4 — The Σ₁⁰ Ceiling

  No physical undecidability result based on a computable many-one
  reduction from a Σ₁⁰-complete problem can exceed LPO.
  To exceed LPO, a construction would need to encode Σ₂⁰ or higher.
-/
import Papers.P38_WangTiling.Defs

noncomputable section

-- ============================================================
-- Theorem 4: The Σ₁⁰ Ceiling
-- ============================================================

/-- A Σ₁⁰ property: there exists n such that a BISH-decidable
    predicate holds. Encoded as: P(M) ↔ ∃n, φ(M,n) = true
    where φ is computable. -/
structure Sigma1Property where
  /-- The underlying property on TMs. -/
  prop : TM → Prop
  /-- The witness function (BISH-computable). -/
  witness : TM → ℕ → Bool
  /-- P(M) ↔ ∃n, witness(M,n) = true. -/
  equiv : ∀ (M : TM), prop M ↔ ∃ n, witness M n = true

/-- LPO decides any Σ₁⁰ property for each instance.

    Given a Σ₁⁰ property P with witness φ, and given LPO:
    1. For each M, apply LPO to the sequence n ↦ φ(M,n).
    2. Either ∃n, φ(M,n) = true → P(M), or ∀n, φ(M,n) = false → ¬P(M). -/
theorem lpo_decides_sigma1 (P : Sigma1Property) (lpo : LPO) :
    ∀ (M : TM), P.prop M ∨ ¬P.prop M := by
  intro M
  rcases lpo (P.witness M) with h_all | ⟨n, hn⟩
  · -- ∀n, witness(M,n) = false → ¬P(M)
    right
    intro hP
    have ⟨k, hk⟩ := (P.equiv M).mp hP
    have := h_all k
    rw [this] at hk
    exact Bool.false_ne_true hk
  · -- ∃n, witness(M,n) = true → P(M)
    left
    exact (P.equiv M).mpr ⟨n, hn⟩

/-- THEOREM 4 (Σ₁⁰ Ceiling): No Σ₁⁰-complete problem exceeds LPO.

    By definition, LPO = Σ₁⁰-LEM. Every Σ₁⁰ statement has the form
    ∃n, φ(n) = true with computable φ. LPO decides all such statements.
    Therefore no undecidability result based on a Σ₁⁰-complete reduction
    can require logical resources beyond LPO.

    To exceed LPO, one would need Σ₂⁰: ∃n ∀m ψ(n,m).
    The inner ∀m quantifier prevents LPO from collapsing the decision. -/
theorem sigma1_ceiling :
    ∀ (P : Sigma1Property), LPO → ∀ (M : TM), P.prop M ∨ ¬P.prop M :=
  fun P lpo => lpo_decides_sigma1 P lpo

-- The open question: can physics reach Σ₂⁰?
-- This is investigated in Paper 39.
-- axiom sigma2_physics_exists : False  -- DO NOT AXIOMATIZE

end
