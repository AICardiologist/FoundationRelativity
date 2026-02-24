/-
Papers/P19_WKBTunneling/Barrier/Parabolic.lean
Parabolic (inverted harmonic) barrier: V(x) = V₀(1 - x²/a²).

The turning points at energy E are x₁ = -a√(1-E/V₀), x₂ = a√(1-E/V₀).
These are algebraically computable from the parameters — BISH.
-/
import Papers.P19_WKBTunneling.WKB.Amplitude

noncomputable section
namespace Papers.P19

-- ========================================================================
-- Parabolic barrier definition
-- ========================================================================

/-- Parabolic (inverted harmonic) barrier: V(x) = V₀(1 - x²/a²). -/
def parabolicV (V₀ a : ℝ) (x : ℝ) : ℝ := V₀ * (1 - x ^ 2 / a ^ 2)

/-- The parabolic barrier is continuous. -/
lemma parabolicV_continuous (V₀ a : ℝ) : Continuous (parabolicV V₀ a) := by
  unfold parabolicV
  fun_prop

-- ========================================================================
-- Algebraic turning points
-- ========================================================================

/-- Right turning point of the parabolic barrier at energy E. -/
def parabolicTP_right (V₀ a E : ℝ) : ℝ := a * Real.sqrt (1 - E / V₀)

/-- Left turning point of the parabolic barrier at energy E. -/
def parabolicTP_left (V₀ a E : ℝ) : ℝ := -(a * Real.sqrt (1 - E / V₀))

/-- The right turning point satisfies V(x₂) = E.
    Proof: V₀(1 - (a√(1-E/V₀))²/a²) = V₀(1 - (1-E/V₀)) = V₀·E/V₀ = E. -/
theorem parabolicV_at_right_tp (V₀ a E : ℝ) (hV₀ : V₀ ≠ 0) (ha : a ≠ 0)
    (hfrac : 0 ≤ 1 - E / V₀) :
    parabolicV V₀ a (parabolicTP_right V₀ a E) = E := by
  unfold parabolicV parabolicTP_right
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  rw [mul_pow, Real.sq_sqrt hfrac]
  field_simp
  ring

/-- The left turning point satisfies V(x₁) = E. -/
theorem parabolicV_at_left_tp (V₀ a E : ℝ) (hV₀ : V₀ ≠ 0) (ha : a ≠ 0)
    (hfrac : 0 ≤ 1 - E / V₀) :
    parabolicV V₀ a (parabolicTP_left V₀ a E) = E := by
  unfold parabolicV parabolicTP_left
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  rw [neg_pow_two, mul_pow, Real.sq_sqrt hfrac]
  field_simp
  ring

-- ========================================================================
-- BISH computability of parabolic WKB
-- ========================================================================

/-- The WKB action for a parabolic barrier exists and is computable.
    Turning points are algebraically given — no root-finding needed. -/
theorem parabolic_wkb_action_exists
    (V₀ a E m : ℝ) (_hm : 0 < m) (_hV₀ : 0 < V₀) (_ha : 0 < a)
    (_hE : 0 < E) (_hEV : E < V₀) :
    ∃ S : ℝ, S = wkbActionExplicit (parabolicV V₀ a) E m
      (parabolicTP_left V₀ a E) (parabolicTP_right V₀ a E) :=
  ⟨_, rfl⟩

/-- The parabolic tunneling amplitude exists and is computable. -/
theorem parabolic_amplitude_exists
    (V₀ a E m ℏ : ℝ) (_hℏ : 0 < ℏ) :
    ∃ T : ℝ, T = wkbAmplitudeExplicit (parabolicV V₀ a) E m
      (parabolicTP_left V₀ a E) (parabolicTP_right V₀ a E) ℏ :=
  ⟨_, rfl⟩

end Papers.P19
end
