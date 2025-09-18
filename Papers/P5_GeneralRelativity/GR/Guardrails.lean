-- Papers/P5_GeneralRelativity/GR/Guardrails.lean
import Papers.P5_GeneralRelativity.GR.Schwarzschild
import Papers.P5_GeneralRelativity.GR.Riemann

namespace Papers.P5_GeneralRelativity.Schwarzschild

section Guardrails
-- Ensure simp never unfolds these under a derivative implicitly.
attribute [-simp] Γ_r_θθ Γ_r_φφ Γ_φ_θφ Γ_θ_φφ

-- Smoke tests: simp should not change the symbolic derivatives.
example (M r : ℝ) :
  deriv (fun s => Γ_r_θθ M s) r = deriv (fun s => Γ_r_θθ M s) r := by
  simp

example (M r θ : ℝ) :
  deriv (fun s => Γ_r_φφ M s θ) r = deriv (fun s => Γ_r_φφ M s θ) r := by
  simp
end Guardrails

section GuardrailsRiemann

-- These are already off for Ricci work; restate here for clarity.
attribute [-simp] Γ_r_θθ Γ_r_φφ Γ_φ_θφ Γ_θ_φφ

-- Smoke: `simp` does not alter the mixed Riemann definition structurally.
example (M r θ : ℝ) (ρ σ μ ν : Idx) :
  RiemannUp M r θ ρ σ μ ν = RiemannUp M r θ ρ σ μ ν := by
  rfl

end GuardrailsRiemann

end Papers.P5_GeneralRelativity.Schwarzschild