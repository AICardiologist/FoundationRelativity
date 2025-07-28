/-
Sprint 44 Day 4 starter file: the "bidual gap" lemma
showing that our Gödel operator has spectral gap ≥ ε > 0.
Math‑AI will fill the proofs tomorrow; we supply the statements
and type‑signatures now so downstream files can import them.
-/
import Papers.P1_GBC.Core

open Papers.P1_GBC Core

namespace Papers.P1_GBC

variable {g : ℕ}

/-- `gap ≥ ε` is the quantitative part of the Gödel–Banach story.  
    For now we expose it as a constant to unblock other work. -/
constant spectral_gap (ε : ℝ) :
  ε > 0 →
  ∃ gap, gap ≥ ε ∧
    ∀ λ ∈ spectrum (G (g:=g) : L2Space →L[ℂ] L2Space), |λ| ≥ gap ∨ λ = 1

end Papers.P1_GBC