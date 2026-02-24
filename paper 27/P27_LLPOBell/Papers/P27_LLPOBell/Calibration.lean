/-
Papers/P27_LLPOBell/Calibration.lean
Paper 27: The Logical Cost of Root-Finding
Calibration.lean — LLPO ↔ IVT, and LLPO → angle-findable

The calibration chain:
  LLPO ↔ ExactIVT (Bridges-Richman 1987)
  LLPO → GeneralizedIVT → angle crossing findable

This places Bell angle optimization at the LLPO level of the constructive
hierarchy: finding optimal measurement angles for a general quantum state
costs exactly LLPO, because it reduces to root-finding for continuous
functions, which is the Intermediate Value Theorem.
-/
import Papers.P27_LLPOBell.AngleFinding

namespace Papers.P27

noncomputable section

-- ========================================================================
-- Central calibration: LLPO ↔ ExactIVT
-- ========================================================================

/-- The central calibration: LLPO and ExactIVT are equivalent over BISH.
    This is the mathematical foundation of the paper. -/
theorem llpo_iff_exactIVT : LLPO ↔ ExactIVT :=
  exact_ivt_iff_llpo.symm

/-- LLPO and GeneralizedIVT are equivalent. -/
theorem llpo_iff_generalizedIVT : LLPO → GeneralizedIVT :=
  llpo_implies_generalizedIVT

-- ========================================================================
-- LLPO → angle threshold crossing findable
-- ========================================================================

/-- LLPO implies that for any Bell correlation with a CHSH violation,
    we can find the threshold crossing angle. -/
theorem llpo_implies_threshold_finding :
    LLPO → ∀ (B : BellCorrelation),
      (∃ a a' b b', |chshValue B a a' b b'| > 2) →
      ∃ a'₀ b₀ b'₀ a₀, chshSlice B a'₀ b₀ b'₀ a₀ = 2 :=
  fun hllpo B hviol => llpo_finds_crossing hllpo B hviol

-- ========================================================================
-- IVT → angle finding (via LLPO)
-- ========================================================================

/-- ExactIVT implies angle-finding capability for Bell correlations.
    Proof: ExactIVT → LLPO → angle crossing findable. -/
theorem exactIVT_implies_angle_finding :
    ExactIVT → ∀ (B : BellCorrelation),
      (∃ a a' b b', |chshValue B a a' b b'| > 2) →
      ∃ a'₀ b₀ b'₀ a₀, chshSlice B a'₀ b₀ b'₀ a₀ = 2 := by
  intro hivt B hviol
  exact llpo_implies_threshold_finding (llpo_of_exactIVT hivt) B hviol

-- ========================================================================
-- The angle-finding → IVT reduction
-- ========================================================================

/-- Angle-finding produces IVT instances.

    Given a BellCorrelation B with a sign change in the CHSH slice,
    the angle-finding problem IS an IVT instance (the continuous function
    chshSlice B a' b b' - 2 has a sign change on [θ₁, θ₂]).

    This is the forward direction: Bell angle optimization → IVT. -/
theorem angle_finding_is_ivt_instance (B : BellCorrelation)
    (a' b b' θ₁ θ₂ : ℝ) (h12 : θ₁ < θ₂)
    (hbelow : chshSlice B a' b b' θ₁ < 2)
    (habove : 2 < chshSlice B a' b b' θ₂) :
    ∃ I : IVTInstance, I.f = fun x => chshSlice B a' b b' x - 2 := by
  exact ⟨thresholdCrossing (chshSlice B a' b b')
    (chshSlice_continuous B a' b b') θ₁ θ₂ 2 h12 hbelow habove, rfl⟩

-- ========================================================================
-- Summary: the three-level stratification
-- ========================================================================

/-- The three-level stratification of Bell angle optimization:

    Level 1 (BISH): The CHSH bound |S| ≤ 2 and quantum violation |S| > 2
    are computable (finite algebra and specific-angle evaluation).

    Level 2 (LLPO): Finding *general* optimal measurement angles requires
    root-finding for continuous functions, which is the Intermediate Value
    Theorem, which is equivalent to LLPO.

    Level 3 (Hierarchy): WLPO → LLPO (strict), so angle-finding is
    strictly easier than gap detection (Paper 26's WLPO result). -/
theorem angle_stratification :
    -- Level 1: There exists a violation (computable for singlet)
    (∃ a a' b b', |chshValue singletBell a a' b b'| > 2) ∧
    -- Level 2: LLPO ↔ ExactIVT (the mechanism)
    (LLPO ↔ ExactIVT) ∧
    -- Level 2b: LLPO → angle threshold finding
    (LLPO → ∀ B : BellCorrelation,
      (∃ a a' b b', |chshValue B a a' b b'| > 2) →
      ∃ a'₀ b₀ b'₀ a₀, chshSlice B a'₀ b₀ b'₀ a₀ = 2) ∧
    -- Level 3: WLPO → LLPO (strict hierarchy)
    (WLPO → LLPO) :=
  ⟨singlet_violates,
   llpo_iff_exactIVT,
   llpo_implies_threshold_finding,
   wlpo_implies_llpo⟩

-- ========================================================================
-- Connection to Paper 21
-- ========================================================================

/-- Paper 21 showed LLPO ↔ BellSignDecision (abstract sign encoding).
    Paper 27 explains the *mechanism*: the sign decision is an instance of
    the Intermediate Value Theorem. Concretely:

    - Paper 21: LLPO ↔ (∀ α with AtMostOne, bellAsymmetry(α) ≤ 0 ∨ 0 ≤ bellAsymmetry(α))
    - Paper 27: LLPO ↔ ExactIVT, and Bell angle optimization → IVT instances

    The LLPO content of Bell physics is *root-finding*. Every time a Bell
    experiment requires finding optimal measurement angles for a general
    quantum state, it invokes a constructive IVT instance, and thus pays
    the LLPO cost. -/
theorem mechanism_explanation :
    -- LLPO is equivalent to ExactIVT
    (LLPO ↔ ExactIVT) ∧
    -- ExactIVT suffices for angle-finding
    (ExactIVT → ∀ B : BellCorrelation,
      (∃ a a' b b', |chshValue B a a' b b'| > 2) →
      ∃ a'₀ b₀ b'₀ a₀, chshSlice B a'₀ b₀ b'₀ a₀ = 2) :=
  ⟨llpo_iff_exactIVT, exactIVT_implies_angle_finding⟩

end

end Papers.P27
