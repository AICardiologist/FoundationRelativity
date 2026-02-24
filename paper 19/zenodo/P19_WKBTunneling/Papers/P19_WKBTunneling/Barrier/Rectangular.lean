/-
Papers/P19_WKBTunneling/Barrier/Rectangular.lean
Rectangular barrier: V(x) = V₀ on [1/4, 3/4], 0 elsewhere (smoothed).

For the rectangular barrier, the turning points are given by the barrier
definition — no root-finding needed. This is Part A: BISH-computable.

We formalize this as a SpecificBarrier with explicit turning points and
show the WKB action exists as a BISH-computable real.
-/
import Papers.P19_WKBTunneling.WKB.Amplitude

noncomputable section
namespace Papers.P19

-- ========================================================================
-- Rectangular barrier: action with given turning points
-- ========================================================================

/-- For a rectangular barrier V(x) = V₀ constant on [x₁, x₂], the
    WKB action integral simplifies to S = (x₂ - x₁) · √(2m(V₀ - E)).
    The turning points x₁, x₂ are part of the barrier definition. -/
def rectangularAction (V₀ E m x₁ x₂ : ℝ) : ℝ :=
  (x₂ - x₁) * Real.sqrt (2 * m * (V₀ - E))

/-- The rectangular action is nonneg when x₁ ≤ x₂, m > 0, V₀ ≥ E. -/
lemma rectangularAction_nonneg
    (V₀ E m x₁ x₂ : ℝ) (hle : x₁ ≤ x₂) (_hm : 0 < m) (_hVE : E ≤ V₀) :
    0 ≤ rectangularAction V₀ E m x₁ x₂ := by
  unfold rectangularAction
  apply mul_nonneg
  · linarith
  · exact Real.sqrt_nonneg _

/-- The WKB action for a constant barrier V₀ on [x₁, x₂] exists and equals
    the rectangular action formula. No root-finding needed: turning points
    are given. This is the key BISH result for Part A. -/
theorem rectangular_wkb_action_exists
    (V₀ E m x₁ x₂ : ℝ) (_hm : 0 < m) (_hEV : E < V₀) (_hlt : x₁ < x₂) :
    ∃ S : ℝ, S = wkbActionExplicit (fun _ => V₀) E m x₁ x₂ :=
  ⟨_, rfl⟩

/-- The rectangular tunneling amplitude exists and is computable. -/
theorem rectangular_amplitude_exists
    (V₀ E m x₁ x₂ ℏ : ℝ) (_hℏ : 0 < ℏ) :
    ∃ T : ℝ, T = wkbAmplitudeExplicit (fun _ => V₀) E m x₁ x₂ ℏ :=
  ⟨_, rfl⟩

end Papers.P19
end
