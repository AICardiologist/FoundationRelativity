/-
Papers/P27_LLPOBell/BellCorrelation.lean
Paper 27: The Logical Cost of Root-Finding
BellCorrelation.lean — Continuous Bell correlations, CHSH, singlet state

We model Bell correlations as continuous functions of measurement angles,
rather than using the matrix formalism from Paper 11. This is natural
for the IVT connection: the CHSH value is a continuous function of angles,
and finding optimal angles is a root-finding problem.

The singlet state provides the canonical example: E(θ_A, θ_B) = -cos(θ_A - θ_B),
with maximal CHSH violation 2√2 at the Tsirelson angles.
-/
import Papers.P27_LLPOBell.IVT
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace Papers.P27

noncomputable section

-- ========================================================================
-- Bell Correlation (continuous, bounded)
-- ========================================================================

/-- A Bell correlation function: the expected product of outcomes when
    Alice measures at angle θ_A and Bob at angle θ_B.

    For a two-qubit quantum state ρ with measurement directions in the
    xy-plane, E(θ_A, θ_B) is continuous and bounded by 1. -/
structure BellCorrelation where
  /-- The correlation function -/
  E : ℝ → ℝ → ℝ
  /-- Continuity in both angles -/
  E_continuous : Continuous (fun p : ℝ × ℝ => E p.1 p.2)
  /-- Correlations are bounded by 1 -/
  E_bound : ∀ θ₁ θ₂, |E θ₁ θ₂| ≤ 1

-- ========================================================================
-- CHSH Value
-- ========================================================================

/-- The CHSH combination for four measurement angles:
    S = E(a,b) + E(a,b') + E(a',b) - E(a',b')
    where a, a' are Alice's settings and b, b' are Bob's. -/
def chshValue (B : BellCorrelation) (a a' b b' : ℝ) : ℝ :=
  B.E a b + B.E a b' + B.E a' b - B.E a' b'

/-- The CHSH value is continuous in all four angles. -/
theorem chshValue_continuous (B : BellCorrelation) :
    Continuous (fun p : ℝ × ℝ × ℝ × ℝ =>
      chshValue B p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold chshValue
  have hE := B.E_continuous
  -- E(p.1, p.2.2.1) : a → b
  have h1 : Continuous (fun p : ℝ × ℝ × ℝ × ℝ => B.E p.1 p.2.2.1) :=
    hE.comp (continuous_fst.prodMk (continuous_fst.comp (continuous_snd.comp continuous_snd)))
  -- E(p.1, p.2.2.2) : a → b'
  have h2 : Continuous (fun p : ℝ × ℝ × ℝ × ℝ => B.E p.1 p.2.2.2) :=
    hE.comp (continuous_fst.prodMk (continuous_snd.comp (continuous_snd.comp continuous_snd)))
  -- E(p.2.1, p.2.2.1) : a' → b
  have h3 : Continuous (fun p : ℝ × ℝ × ℝ × ℝ => B.E p.2.1 p.2.2.1) :=
    hE.comp ((continuous_fst.comp continuous_snd).prodMk
      (continuous_fst.comp (continuous_snd.comp continuous_snd)))
  -- E(p.2.1, p.2.2.2) : a' → b'
  have h4 : Continuous (fun p : ℝ × ℝ × ℝ × ℝ => B.E p.2.1 p.2.2.2) :=
    hE.comp ((continuous_fst.comp continuous_snd).prodMk
      (continuous_snd.comp (continuous_snd.comp continuous_snd)))
  exact ((h1.add h2).add h3).sub h4

-- ========================================================================
-- CHSH as function of single angle (for IVT connection)
-- ========================================================================

/-- CHSH value as a function of Alice's first angle only,
    with the other three angles fixed. This is the key reduction:
    a 4D optimization reduces to a sequence of 1D root-finding problems. -/
def chshSlice (B : BellCorrelation) (a' b b' : ℝ) : ℝ → ℝ :=
  fun a => chshValue B a a' b b'

/-- The single-angle CHSH slice is continuous. -/
theorem chshSlice_continuous (B : BellCorrelation) (a' b b' : ℝ) :
    Continuous (chshSlice B a' b b') := by
  unfold chshSlice chshValue
  have hE := B.E_continuous
  -- E(a, b) as function of a only (b is const)
  have h1 : Continuous (fun a => B.E a b) :=
    hE.comp (continuous_id.prodMk continuous_const)
  -- E(a, b') as function of a only
  have h2 : Continuous (fun a => B.E a b') :=
    hE.comp (continuous_id.prodMk continuous_const)
  -- E(a', b) and E(a', b') are constants
  exact ((h1.add h2).add continuous_const).sub continuous_const

-- ========================================================================
-- Singlet Correlation
-- ========================================================================

/-- The quantum correlation for the Bell singlet state |ψ⁻⟩:
    E(θ_A, θ_B) = -cos(θ_A - θ_B).

    This is the standard spin-1/2 singlet correlation when measurements
    are parameterized by angles in the xy-plane. -/
def singletCorrelation (θ_A θ_B : ℝ) : ℝ :=
  -Real.cos (θ_A - θ_B)

/-- The singlet correlation is continuous in both angles. -/
theorem singletCorrelation_continuous :
    Continuous (fun p : ℝ × ℝ => singletCorrelation p.1 p.2) := by
  unfold singletCorrelation
  exact (Real.continuous_cos.comp (continuous_fst.sub continuous_snd)).neg

/-- The singlet correlation is bounded by 1. -/
theorem singletCorrelation_bound (θ₁ θ₂ : ℝ) :
    |singletCorrelation θ₁ θ₂| ≤ 1 := by
  unfold singletCorrelation
  rw [abs_neg]
  exact abs_le.mpr ⟨by linarith [Real.neg_one_le_cos (θ₁ - θ₂)],
                     Real.cos_le_one (θ₁ - θ₂)⟩

/-- The singlet state as a BellCorrelation. -/
def singletBell : BellCorrelation where
  E := singletCorrelation
  E_continuous := singletCorrelation_continuous
  E_bound := singletCorrelation_bound

-- ========================================================================
-- Classical CHSH Bound
-- ========================================================================

/-- Classical CHSH bound: any local hidden variable model satisfies |S| ≤ 2.

    This is a finite algebraic fact (BISH): for any assignment of ±1 values,
    |a₁b₁ + a₁b₂ + a₂b₁ - a₂b₂| = |a₁(b₁+b₂) + a₂(b₁-b₂)| ≤ 2.

    Paper 21 proved this for discrete assignments. Here we state it for
    the correlation formulation: if E arises from a local hidden variable
    model, then |S| ≤ 2 for all angle choices. -/
axiom classical_chsh_bound :
  ∀ (E_lhv : ℝ → ℝ → ℝ),
    -- E arises from averaging over hidden variable
    (∃ (Λ : Type) (_ : MeasurableSpace Λ) (μ : MeasureTheory.Measure Λ)
       (A : ℝ → Λ → ℝ) (Bf : ℝ → Λ → ℝ),
       MeasureTheory.IsProbabilityMeasure μ ∧
       (∀ a l, A a l = 1 ∨ A a l = -1) ∧
       (∀ b l, Bf b l = 1 ∨ Bf b l = -1) ∧
       (∀ a b, E_lhv a b = ∫ l, A a l * Bf b l ∂μ)) →
    ∀ a a' b b',
      |E_lhv a b + E_lhv a b' + E_lhv a' b - E_lhv a' b'| ≤ 2

-- ========================================================================
-- Quantum CHSH Violation (Tsirelson)
-- ========================================================================

/-- The quantum CHSH value: S_Q = 2√2 (Tsirelson bound), achieved by the
    singlet state at the optimal angles (0, π/4, π/8, 3π/8). -/
def S_quantum : ℝ := 2 * Real.sqrt 2

/-- S_quantum > 2 (the quantum violation exceeds the classical bound). -/
theorem S_quantum_gt_two : S_quantum > 2 := by
  unfold S_quantum
  have h2 : Real.sqrt 2 > 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_lt_sqrt (by linarith) (by linarith)
  linarith

/-- The singlet state achieves a CHSH violation > 2 at the Tsirelson angles.

    At angles a=0, a'=π/2, b=π/4, b'=-π/4:
      E(0,π/4)    = -cos(-π/4) = -√2/2
      E(0,-π/4)   = -cos(π/4)  = -√2/2
      E(π/2,π/4)  = -cos(π/4)  = -√2/2
      E(π/2,-π/4) = -cos(3π/4) = √2/2
    So S = -√2/2 + (-√2/2) + (-√2/2) - (√2/2) = -2√2 < -2.

    We state the absolute violation: |S| > 2. -/
axiom singlet_violates :
  ∃ a a' b b', |chshValue singletBell a a' b b'| > 2

-- ========================================================================
-- Singlet correlation values at specific angles
-- ========================================================================

/-- E(0, θ) = -cos(θ) for the singlet. -/
theorem singlet_E_zero (θ : ℝ) : singletBell.E 0 θ = -Real.cos θ := by
  simp [singletBell, singletCorrelation]

/-- A Bell correlation that violates CHSH is not a local hidden variable model. -/
theorem quantum_not_lhv (B : BellCorrelation) (a a' b b' : ℝ)
    (hv : |chshValue B a a' b b'| > 2) :
    ¬∃ (Λ : Type) (_ : MeasurableSpace Λ) (μ : MeasureTheory.Measure Λ)
       (A : ℝ → Λ → ℝ) (Bf : ℝ → Λ → ℝ),
       MeasureTheory.IsProbabilityMeasure μ ∧
       (∀ a₀ l, A a₀ l = 1 ∨ A a₀ l = -1) ∧
       (∀ b₀ l, Bf b₀ l = 1 ∨ Bf b₀ l = -1) ∧
       (∀ a₁ b₁, B.E a₁ b₁ = ∫ l, A a₁ l * Bf b₁ l ∂μ) := by
  intro ⟨Λ, _, μ, A, Bf, hprob, hA, hBf, hE⟩
  have hbound := classical_chsh_bound B.E ⟨Λ, _, μ, A, Bf, hprob, hA, hBf, hE⟩ a a' b b'
  -- hv : |chshValue B a a' b b'| > 2, which unfolds to |B.E a b + B.E a b' + B.E a' b - B.E a' b'| > 2
  unfold chshValue at hv
  linarith

end

end Papers.P27
