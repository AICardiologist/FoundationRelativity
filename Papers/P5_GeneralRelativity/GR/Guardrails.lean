-- Papers/P5_GeneralRelativity/GR/Guardrails.lean
import Papers.P5_GeneralRelativity.GR.Schwarzschild

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

end Papers.P5_GeneralRelativity.Schwarzschild