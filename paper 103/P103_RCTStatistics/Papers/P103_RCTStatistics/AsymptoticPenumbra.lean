/-
  AsymptoticPenumbra.lean — Part V

  MAIN THEOREM: The Asymptotic Penumbra characterisation.

  CRITICAL (v2): p_asymp = 1 - Φ(T) is a computable REAL, not rational.
  Φ is transcendental for algebraic arguments. Therefore:
    - Comparison p_asymp < α is NOT decidable by inferInstance
    - Witnessing strict inequality requires a rational separator
    - Guaranteeing termination of this search requires Markov's Principle
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Papers.P103_RCTStatistics.OmnisciencePrinciples
import Papers.P103_RCTStatistics.RealDecidability
import Papers.P103_RCTStatistics.StudentizedBerryEsseen

namespace P103

/-- A trial result packages the asymptotic p-value (a REAL, not rational,
    because it passes through the transcendental normal CDF) and the
    Studentized Berry-Esseen error bound. -/
structure TrialResult where
  p_asymp : ℝ                -- 1 - Φ(T), a computable but transcendental real
  studentBE_err : ℝ          -- Studentized Berry-Esseen error bound
  h_err_nonneg : studentBE_err ≥ 0
  err_rat_bound : ℚ          -- computable rational ≥ studentBE_err
  h_rat_bound : (err_rat_bound : ℝ) ≥ studentBE_err

/-- Classical significance: p_asymp < α.
    For real-valued p, this requires LPO to decide universally. -/
def classicallySignificant (tr : TrialResult) (α : ℝ) : Prop :=
  tr.p_asymp < α

/-- Constructive witnessing at BISH+MP: the entire error interval
    sits below α. Because p_asymp is real (transcendental), even this
    strengthened condition requires MP to verify. -/
def constructivelyWitnessed (tr : TrialResult) (α : ℝ) : Prop :=
  tr.p_asymp + tr.studentBE_err < α

/-- The Asymptotic Penumbra: classically significant but not
    constructively witnessed. -/
def inPenumbra (tr : TrialResult) (α : ℝ) : Prop :=
  classicallySignificant tr α ∧ ¬ constructivelyWitnessed tr α

/-- THEOREM A (Penumbra Characterisation):
    A trial result is in the penumbra iff the asymptotic p-value
    falls in the interval [α - ε, α), where ε is the Studentized
    Berry-Esseen error. -/
theorem penumbra_characterization (tr : TrialResult) (α : ℝ) :
    inPenumbra tr α ↔
    (tr.p_asymp < α ∧ α ≤ tr.p_asymp + tr.studentBE_err) := by
  unfold inPenumbra classicallySignificant constructivelyWitnessed
  constructor
  · intro ⟨hlt, hnotw⟩
    exact ⟨hlt, not_lt.mp hnotw⟩
  · intro ⟨hlt, hle⟩
    exact ⟨hlt, not_lt.mpr hle⟩

/-- THEOREM B (MP Requirement):
    Constructive witnessing of asymptotic significance requires
    Markov's Principle because p_asymp is transcendental.
    Documentary axiom for the MP application to rational approximation. -/
axiom constructive_witnessing_requires_MP :
  ∀ (p_real err_real : ℝ) (α_q : ℚ),
    MarkovPrinciple →
    ¬¬(p_real + err_real < ↑α_q) →
    ∃ (r : ℚ), p_real + err_real < ↑r ∧ ↑r < ↑α_q

/-- FALLBACK: When rational bounds suffice, pure BISH decides. -/
instance constructive_witnessing_via_rational_bounds
    (p_rat_upper err_rat_upper α_q : ℚ) :
    Decidable (p_rat_upper + err_rat_upper < α_q) :=
  inferInstance

/-- THEOREM B' (LPO for universal significance):
    Trichotomy for ALL reals requires LPO. -/
theorem classical_significance_requires_LPO :
    (∀ (p α : ℝ), p < α ∨ p = α ∨ p > α) → LPO :=
  trichotomy_implies_LPO_encoding

/-- THEOREM C (Subgroup Penalty):
    Below a computable minimum sample size, the Studentized
    Berry-Esseen error swallows α entirely, making it logically
    impossible to constructively witness ANY effect. -/
theorem subgroup_penalty (ρ_hat σ_hat : ℚ) (α : ℝ)
    (hσ : (σ_hat : ℝ) > 0) (hα : α > 0)
    (hρ : (ρ_hat : ℝ) > 0) :
    ∃ n_min : ℕ, ∀ (n : ℕ) (hn : n > 0), n < n_min →
    studentizedBEError ρ_hat σ_hat n hσ hn ≥ α := by
  -- n_min ≈ (C_s · ρ̂ / (σ̂³ · α))²; computable from data
  sorry

/-- Penumbra shrinks with sample size. -/
theorem penumbra_shrinks_with_n (ρ_hat σ_hat : ℚ) (n m : ℕ)
    (hσ : (σ_hat : ℝ) > 0) (hn : n > 0) (hm : m > 0) (hnm : n < m) :
    studentizedBEError ρ_hat σ_hat m hσ hm <
      studentizedBEError ρ_hat σ_hat n hσ hn := by
  unfold studentizedBEError
  sorry -- √m > √n when m > n; monotonicity of division

/-- Penumbra grows with skewness (heavier tails → wider penumbra). -/
theorem penumbra_grows_with_skewness (ρ₁ ρ₂ σ_hat : ℚ) (n : ℕ)
    (hσ : (σ_hat : ℝ) > 0) (hn : n > 0) (hρ : (ρ₁ : ℝ) < (ρ₂ : ℝ)) :
    studentizedBEError ρ₁ σ_hat n hσ hn <
      studentizedBEError ρ₂ σ_hat n hσ hn := by
  unfold studentizedBEError
  sorry -- Monotonicity of multiplication by positive constant

end P103
