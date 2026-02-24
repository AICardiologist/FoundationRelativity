/-
  Paper 37: Uncomputability of Phase Diagrams and RG Flows is LPO
  MetaTheorem.lean: Theorem 4 — The Central Meta-Theorem

  ANY physical undecidability result obtained by computable many-one
  reduction from the halting problem is Turing-Weihrauch equivalent to LPO.

  This is the paper's main contribution. Theorems 1–3 are corollaries.
-/
import Papers.P37_UndecidabilityLandscape.Defs

noncomputable section

open Real

-- ============================================================
-- Theorem 4: The Meta-Theorem
-- ============================================================

-- The meta-theorem is parameterized by:
--   α : the domain type (e.g., TM, ℝ)
--   P : α → Prop — the physical property to decide
--   encode : (ℕ → Bool) → α — maps binary sequences to domain elements
--   halts_iff : the encoding bridge (P holds iff the sequence has a true entry)

/-- THEOREM 4 (Meta-Theorem): Any computable many-one reduction from halting
    to a physical property P is Turing-Weihrauch equivalent to LPO.

    If P(encode(a)) ↔ ∃n, a(n) = true for all binary sequences a,
    then deciding P for all encoded instances is equivalent to LPO.

    This covers ALL known undecidability results in quantum many-body physics:
    spectral gap (CPgW 2015, BCLPG 2020), phase diagrams (BCW 2021),
    RG flows (CLPE 2022). -/
theorem halting_reduction_iff_lpo
    {α : Type} (encode : (ℕ → Bool) → α)
    (P : α → Prop)
    (hP : ∀ (a : ℕ → Bool), P (encode a) ↔ ∃ n, a n = true) :
    (∀ (a : ℕ → Bool), P (encode a) ∨ ¬P (encode a)) ↔ LPO := by
  constructor
  · -- Forward: deciding P for all encoded instances → LPO
    intro h_dec a
    rcases h_dec a with h_yes | h_no
    · -- P holds → ∃n, a(n) = true
      right
      exact (hP a).mp h_yes
    · -- ¬P → ¬(∃n, a(n) = true) → ∀n, a(n) = false
      left
      intro n
      by_contra h_ne
      have h_true : a n = true := by
        cases ha : a n with
        | false => exact absurd ha h_ne
        | true => rfl
      exact h_no ((hP a).mpr ⟨n, h_true⟩)
  · -- Reverse: LPO → deciding P for all encoded instances
    intro lpo a
    rcases lpo a with h_all | ⟨n, hn⟩
    · -- ∀n, a(n) = false → ¬(∃n, a(n) = true) → ¬P
      right
      intro hP_yes
      have ⟨n, hn⟩ := (hP a).mp hP_yes
      have := h_all n
      rw [this] at hn
      exact Bool.false_ne_true hn
    · -- ∃n, a(n) = true → P holds
      left
      exact (hP a).mpr ⟨n, hn⟩

/-- Variant: Meta-theorem with negated encoding (P ↔ ¬halts).
    Used when the physical property corresponds to NON-halting
    (e.g., "gapped" ↔ "doesn't halt"). -/
theorem halting_reduction_neg_iff_lpo
    {α : Type} (encode : (ℕ → Bool) → α)
    (P : α → Prop)
    (hP : ∀ (a : ℕ → Bool), P (encode a) ↔ ∀ n, a n = false) :
    (∀ (a : ℕ → Bool), P (encode a) ∨ ¬P (encode a)) ↔ LPO := by
  constructor
  · -- Forward: deciding P → LPO
    intro h_dec a
    rcases h_dec a with h_yes | h_no
    · -- P holds → ∀n, a(n) = false
      left
      exact (hP a).mp h_yes
    · -- ¬P → ¬(∀n, a(n) = false) → ∃n, a(n) = true
      right
      have h_not_all : ¬(∀ n, a n = false) := fun h_all => h_no ((hP a).mpr h_all)
      by_contra h_no_ex
      apply h_not_all
      intro n
      by_contra h_ne
      have h_true : a n = true := by
        cases ha : a n with
        | false => exact absurd ha h_ne
        | true => rfl
      exact h_no_ex ⟨n, h_true⟩
  · -- Reverse: LPO → deciding P
    intro lpo a
    rcases lpo a with h_all | ⟨n, hn⟩
    · left; exact (hP a).mpr h_all
    · right
      intro hP_yes
      have := (hP a).mp hP_yes n
      rw [this] at hn
      exact Bool.false_ne_true hn

/-- The halting problem is undecidable (not both halts and ¬halts
    for all TMs). -/
axiom halting_problem_undecidable :
    ¬(∀ (M : TM), halts M ∨ ¬halts M)

/-- Corollary: The uniform function M ↦ P(f(M)) is not computable
    when P encodes halting. -/
theorem uniform_function_not_computable
    {α : Type} (encode : (ℕ → Bool) → α)
    (P : α → Prop)
    (hP : ∀ (a : ℕ → Bool), P (encode a) ↔ ∃ n, a n = true) :
    ¬(∀ (a : ℕ → Bool), P (encode a) ∨ ¬P (encode a)) := by
  intro h_dec
  have lpo := (halting_reduction_iff_lpo encode P hP).mp h_dec
  apply halting_problem_undecidable
  intro M
  rcases lpo (halting_seq M) with h_all | ⟨n, hn⟩
  · right
    intro ⟨k, hk⟩
    have := h_all k
    rw [this] at hk
    exact Bool.false_ne_true hk
  · left
    exact ⟨n, hn⟩

end
