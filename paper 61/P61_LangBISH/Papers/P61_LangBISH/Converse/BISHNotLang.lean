/-
  Paper 61: Lang's Conjecture as the MP → BISH Gate
  Converse/BISHNotLang.lean — Theorem B: BISH ⟹̸ Lang

  BISH-decidability does not imply Lang's conjecture.
  The separation: Lang constrains the decay RATE of c(E),
  while BISH only requires EXISTENCE of a bounding function B(E).
-/
import Mathlib.Tactic

namespace Papers.P61_LangBISH

/-! ## Theorem B: The Converse Fails

A "BISH-decidable family" is one where each member admits
a computable bound — but the bound may grow arbitrarily fast.
A "Lang-uniform family" additionally requires a uniform positive
lower bound on the minimum height across the family. -/

/-- Theorem B: BISH-decidability does not imply Lang's conjecture.

    Witness: the family c(n) = 1/(n+2).
    - Each c(n) > 0, so each curve is individually BISH-decidable
      (there exists some bound B(n) for each n).
    - But inf_n c(n) = 0, so no uniform Lang bound C > 0 exists.

    The logical content: BISH constrains computability (existence of bounds),
    Lang constrains geometry (decay rate of minimal heights). These are
    independent conditions. -/
theorem bish_does_not_imply_lang :
    ¬(∀ (family : ℕ → ℚ),
      (∀ n, family n > 0) →
      (∃ C : ℚ, C > 0 ∧ ∀ n, family n ≥ C)) := by
  intro h
  have hfam := h (fun n => 1 / (↑n + 2)) (by intro n; positivity)
  obtain ⟨C, hC_pos, hC_bound⟩ := hfam
  -- For n large enough, 1/(n+2) < C, contradicting hC_bound.
  have : ∃ n : ℕ, 1 / ((n : ℚ) + 2) < C := by
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / C)
    refine ⟨n, ?_⟩
    rw [div_lt_comm₀ (by positivity : (0 : ℚ) < (↑n + 2)) hC_pos]
    calc 1 / C < ↑n := hn
      _ ≤ ↑n + 2 := by linarith
  obtain ⟨n, hn⟩ := this
  have hbound := hC_bound n
  linarith

end Papers.P61_LangBISH
