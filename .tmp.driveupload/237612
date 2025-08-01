import Papers.P1_GBC.Core

open Papers.P1_GBC
namespace Papers.P1_GBC

/-- Quantitative spectral‑gap statement (proof arrives in Day‑4 drop). -/
axiom spectral_gap {g : ℕ} (ε : ℝ) :
  ε > 0 →
  ∃ gap, gap ≥ ε ∧
    ∀ (lam : ℂ), lam ∈ spectrum ℂ (G (g:=g)) →
      Complex.abs lam ≥ gap ∨ lam = 1

end Papers.P1_GBC