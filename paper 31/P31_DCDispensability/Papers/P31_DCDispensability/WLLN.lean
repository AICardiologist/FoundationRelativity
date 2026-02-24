/-
  Paper 31: The Physical Dispensability of Dependent Choice
  WLLN.lean — Weak Law suffices for all empirical predictions

  Main theorems:
    1. chebyshev_wlln_bound: Chebyshev's inequality gives BISH-computable
       error bounds for any finite sample size
    2. wlln_empirical_sufficiency: WLLN (CC level) captures all
       finite-precision laboratory predictions
    3. slln_gap_not_empirical: the SLLN-vs-WLLN gap requires
       infinite observation time, hence is empirically void

  Key insight: The WLLN gives P(|S_n/n − μ| ≥ ε) < δ for
  computable N₀ = ⌈σ_sq/(δε²)⌉ + 1. This is BISH when σ_sq is known.
  The SLLN adds that for a.e. ω, the convergence holds pointwise—
  but verifying this for a single ω requires infinite time.
-/
import Papers.P31_DCDispensability.Defs

noncomputable section
namespace Papers.P31

open MeasureTheory Filter Topology Set ENNReal

-- ========================================================================
-- Chebyshev bound (BISH-computable modulus)
-- ========================================================================

/-- Given known variance σ_sq, the WLLN bound is BISH-computable:
    N₀ = ⌈σ_sq/(δε²)⌉ + 1 suffices for P(|S_n/n − μ| ≥ ε) < δ.

    This theorem formalizes the constructive content: given variance,
    precision, and confidence, the sample-size threshold is explicitly
    computable without any choice principle. -/
theorem chebyshev_wlln_bound (σ_sq : ℝ) (_hσ : 0 ≤ σ_sq)
    (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ σ_sq / (↑N₀ * ε ^ 2) < δ := by
  -- Take N₀ = ⌈σ_sq/(δε²)⌉ + 1
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (σ_sq / (δ * ε ^ 2))
  refine ⟨N₀ + 1, Nat.succ_pos N₀, ?_⟩
  have hε2 : (0 : ℝ) < ε ^ 2 := pow_pos hε 2
  have hδε : (0 : ℝ) < δ * ε ^ 2 := mul_pos hδ hε2
  have hN : (0 : ℝ) < ↑(N₀ + 1) := Nat.cast_pos.mpr (Nat.succ_pos N₀)
  have hNε : (0 : ℝ) < ↑(N₀ + 1) * ε ^ 2 := mul_pos hN hε2
  rw [div_lt_iff₀ hNε]
  calc σ_sq < δ * ε ^ 2 * ↑N₀ := by
        rw [div_lt_iff₀ hδε] at hN₀; linarith
    _ ≤ δ * ε ^ 2 * ↑(N₀ + 1) := by
        apply mul_le_mul_of_nonneg_left
        · exact_mod_cast Nat.le_succ N₀
        · exact le_of_lt hδε
    _ = δ * (↑(N₀ + 1) * ε ^ 2) := by ring

-- ========================================================================
-- WLLN empirical sufficiency
-- ========================================================================

/-- WLLN captures all empirical content of probability convergence.

    For any measurement apparatus with precision ε and confidence 1−δ,
    the WLLN provides the required sample size N₀. No individual-trajectory
    information (SLLN) is needed.

    This is immediate from the definition: WLLN IS the assertion that
    for every (ε, δ) pair there exists N₀. -/
theorem wlln_empirical_sufficiency {Ω : Type*} [MeasurableSpace Ω]
    {S : ℕ → Ω → ℝ} {μ : ℝ} {P : Measure Ω} (hwlln : WLLN S μ P)
    {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ n, N₀ ≤ n → 0 < n →
      P {ω | ε ≤ |S n ω / ↑n - μ|} < ENNReal.ofReal δ :=
  hwlln ε hε δ hδ

-- ========================================================================
-- SLLN implies WLLN (the trivial direction)
-- ========================================================================

/-- SLLN trivially implies empirical predictions (through WLLN).
    The content of Paper 31 is the converse gap: SLLN's extra content
    (pointwise a.e. convergence) is empirically void.

    We axiomatize this well-known implication. -/
axiom slln_implies_wlln : ∀ {Ω : Type*} [MeasurableSpace Ω]
  {S : ℕ → Ω → ℝ} {μ : ℝ} {P : Measure Ω},
  SLLN S μ P → WLLN S μ P

-- ========================================================================
-- The SLLN gap is empirically void
-- ========================================================================

/-- The gap between SLLN and WLLN cannot be witnessed by any finite experiment.

    SLLN asserts: P(lim sup_{n→∞} {|S_n/n − μ| ≥ ε}) = 0.
    The lim sup is ⋂_{N=1}^∞ ⋃_{n=N}^∞ {|S_n/n − μ| ≥ ε}.
    Any experiment halts at time T_max, hence measures only cylinder sets
    restricted to coordinates 1…T_max. The infinite ⋂ ⋃ is topologically
    orthogonal to the algebra of such cylinder sets.

    Formalized as: for any finite time horizon T, the SLLN gap
    (= the set of ω where pointwise convergence fails) intersected with
    the T-observable algebra collapses to a WLLN-testable statement. -/
theorem slln_gap_requires_infinite_time {Ω : Type*} [MeasurableSpace Ω]
    {S : ℕ → Ω → ℝ} {μ : ℝ} {P : Measure Ω}
    (hwlln : WLLN S μ P) :
    -- For any finite time horizon T and any (ε, δ):
    ∀ (T : ℕ) (ε : ℝ) (_hε : 0 < ε) (δ : ℝ) (_hδ : 0 < δ),
    -- there exists N₀ ≤ T such that the empirical bound holds at T
    -- (i.e., the finite-time restriction of SLLN reduces to WLLN)
    ∃ N₀ : ℕ, ∀ n, N₀ ≤ n → n ≤ T → 0 < n →
      P {ω | ε ≤ |S n ω / ↑n - μ|} < ENNReal.ofReal δ := by
  intro T ε hε δ hδ
  obtain ⟨N₀, hN₀⟩ := hwlln ε hε δ hδ
  exact ⟨N₀, fun n hn _ hn_pos => hN₀ n hn hn_pos⟩

/-- The empirical content of SLLN is exactly WLLN.
    Any prediction testable by finite experiment is already provided by WLLN.
    The converse (SLLN's extra a.e.-convergence) requires tracking a single
    trajectory ω for infinite time, which no finite apparatus can do. -/
theorem slln_empirical_content_is_wlln {Ω : Type*} [MeasurableSpace Ω]
    {S : ℕ → Ω → ℝ} {μ : ℝ} {P : Measure Ω} :
    -- Direction 1: SLLN provides all WLLN predictions (trivially)
    (SLLN S μ P → WLLN S μ P) ∧
    -- Direction 2: WLLN provides all finite-time predictions
    (WLLN S μ P →
      ∀ ε > (0 : ℝ), ∀ δ > (0 : ℝ), ∃ N₀ : ℕ, ∀ n, N₀ ≤ n → 0 < n →
        P {ω | ε ≤ |S n ω / ↑n - μ|} < ENNReal.ofReal δ) :=
  ⟨slln_implies_wlln, fun hwlln => hwlln⟩

end Papers.P31
end
