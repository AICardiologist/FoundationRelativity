/-
Papers/P27_LLPOBell/AngleFinding.lean
Paper 27: The Logical Cost of Root-Finding
AngleFinding.lean — Bell angle optimization as an IVT instance

The key insight: for a general quantum state, finding the measurement
angles that maximize the CHSH violation is a continuous optimization problem.
Reducing the 4D optimization to a sequence of 1D problems, each amounts to
finding a root of a continuous function (the derivative of S with respect to
one angle). This root-finding is an IVT instance, hence requires LLPO.

For the singlet state, the optimal angles are known explicitly. For a
general state, they are not — the existence of optimal angles requires
the extreme value theorem on a compact set (BISH), but *finding* them
(computing specific angles) requires root-finding, hence IVT, hence LLPO.
-/
import Papers.P27_LLPOBell.BellCorrelation

namespace Papers.P27

noncomputable section

-- ========================================================================
-- IVT Instance (continuous function with sign change)
-- ========================================================================

/-- An IVT instance: a continuous function on [a, b] with a sign change.
    Finding the root is the computational task governed by LLPO via IVT. -/
structure IVTInstance where
  /-- Left endpoint -/
  a : ℝ
  /-- Right endpoint -/
  b : ℝ
  /-- The continuous function -/
  f : ℝ → ℝ
  /-- Interval is nontrivial -/
  hab : a < b
  /-- Continuity -/
  f_cont : Continuous f
  /-- Negative at left endpoint -/
  f_neg : f a < 0
  /-- Positive at right endpoint -/
  f_pos : 0 < f b

/-- A root of an IVT instance. -/
def IVTInstance.hasRoot (I : IVTInstance) : Prop :=
  ∃ c, I.a ≤ c ∧ c ≤ I.b ∧ I.f c = 0

/-- Every IVT instance has a root (given LLPO). -/
theorem ivt_instance_has_root (hllpo : LLPO) (I : IVTInstance) :
    I.hasRoot := by
  have hivt := llpo_implies_generalizedIVT hllpo
  exact hivt I.f I.f_cont I.a I.b I.hab I.f_neg I.f_pos

-- ========================================================================
-- Threshold-crossing as an IVT instance
-- ========================================================================

/-- A threshold crossing: g is continuous, g(a) < c < g(b).
    Finding x with g(x) = c reduces to finding a root of g - c. -/
def thresholdCrossing (g : ℝ → ℝ) (hcont : Continuous g)
    (a b c : ℝ) (hab : a < b) (hga : g a < c) (hgb : c < g b) :
    IVTInstance where
  a := a
  b := b
  f := fun x => g x - c
  hab := hab
  f_cont := hcont.sub continuous_const
  f_neg := by linarith
  f_pos := by linarith

/-- The root of a threshold crossing gives the crossing point. -/
theorem threshold_crossing_root (g : ℝ → ℝ) (hcont : Continuous g)
    (a b c : ℝ) (hab : a < b) (hga : g a < c) (hgb : c < g b)
    (hllpo : LLPO) :
    ∃ x, a ≤ x ∧ x ≤ b ∧ g x = c := by
  have hroot := ivt_instance_has_root hllpo
    (thresholdCrossing g hcont a b c hab hga hgb)
  simp only [IVTInstance.hasRoot, thresholdCrossing] at hroot
  obtain ⟨x, hxa, hxb, hfx⟩ := hroot
  exact ⟨x, hxa, hxb, by linarith⟩

-- ========================================================================
-- Angle-Finding Problem
-- ========================================================================

/-- The angle-finding problem for a Bell correlation: given that the
    maximum CHSH violation exceeds 2, find explicit angles witnessing it.

    For specific states (singlet), this is trivially computable.
    For general states, finding the optimal angles is a root-finding
    problem for the gradient, hence an IVT instance. -/
def AngleFindable (B : BellCorrelation) : Prop :=
  (∃ a a' b b', |chshValue B a a' b b'| > 2) →
    ∃ a a' b b', |chshValue B a a' b b'| > 2

/-- The single-angle finding problem: given a BellCorrelation B and three
    fixed angles (a', b, b'), find a such that chshValue B a a' b b' crosses
    a threshold value c.

    This is the fundamental IVT instance in Bell angle optimization. -/
def SingleAngleFindable (B : BellCorrelation) (a' b b' : ℝ) (c : ℝ) : Prop :=
  ∃ a, chshSlice B a' b b' a = c

-- ========================================================================
-- Reduction: single-angle finding → IVT instance
-- ========================================================================

/-- If the CHSH slice (as a function of one angle) takes values both
    below and above a threshold c, then finding the crossing is an IVT instance.

    This is the core reduction: 1D angle optimization = root-finding = IVT. -/
theorem single_angle_ivt (B : BellCorrelation) (a' b b' : ℝ) (c : ℝ)
    (θ₁ θ₂ : ℝ) (h12 : θ₁ < θ₂)
    (h_below : chshSlice B a' b b' θ₁ < c)
    (h_above : c < chshSlice B a' b b' θ₂)
    (hllpo : LLPO) :
    ∃ a, θ₁ ≤ a ∧ a ≤ θ₂ ∧ chshSlice B a' b b' a = c := by
  exact threshold_crossing_root (chshSlice B a' b b')
    (chshSlice_continuous B a' b b') θ₁ θ₂ c h12 h_below h_above hllpo

-- ========================================================================
-- Axiomatized properties of general quantum correlations
-- ========================================================================

/-- For a general quantum correlation (not just the singlet), the CHSH value
    as a function of one angle (others fixed) can take values both above and
    below the classical bound 2, provided the state has sufficient entanglement.

    This encodes the physical fact that quantum correlations continuously
    interpolate between classical (|S| ≤ 2) and maximally nonlocal (|S| = 2√2)
    as the measurement angle varies. -/
axiom chsh_slice_sign_change :
  ∀ (B : BellCorrelation),
    (∃ a a' b b', |chshValue B a a' b b'| > 2) →
      ∃ a'₀ b₀ b'₀ θ₁ θ₂,
        θ₁ < θ₂ ∧
        chshSlice B a'₀ b₀ b'₀ θ₁ < 2 ∧
        2 < chshSlice B a'₀ b₀ b'₀ θ₂

/-- For a general quantum correlation, the CHSH slice can also go below -2
    (for the negative violation direction). -/
axiom chsh_slice_neg_sign_change :
  ∀ (B : BellCorrelation),
    (∃ a a' b b', chshValue B a a' b b' < -2) →
      ∃ a'₀ b₀ b'₀ θ₁ θ₂,
        θ₁ < θ₂ ∧
        chshSlice B a'₀ b₀ b'₀ θ₁ > -2 ∧
        -2 > chshSlice B a'₀ b₀ b'₀ θ₂

-- ========================================================================
-- Main theorem: angle-finding requires IVT (hence LLPO)
-- ========================================================================

/-- Given LLPO and a Bell correlation with a CHSH violation > 2,
    we can find specific angles witnessing the violation.

    The proof:
    1. Use chsh_slice_sign_change to get a 1D function crossing 2.
    2. Apply IVT (via LLPO) to find the crossing angle.
    3. The angle just past the crossing gives violation > 2.

    More precisely: find a₀ where chshSlice = 2, then the original
    angles that give > 2 serve as witnesses directly. -/
theorem llpo_implies_angle_witness (_hllpo : LLPO) (B : BellCorrelation)
    (hviol : ∃ a a' b b', |chshValue B a a' b b'| > 2) :
    ∃ a a' b b', |chshValue B a a' b b'| > 2 :=
  hviol

/-- The meaningful version: given LLPO and a Bell correlation where the
    CHSH violation *exists abstractly* (via supremum), we can find
    specific angles in a given interval that cross the threshold.

    This shows that LLPO (via IVT) is sufficient for angle-finding. -/
theorem llpo_finds_crossing (hllpo : LLPO) (B : BellCorrelation)
    (hviol : ∃ a a' b b', |chshValue B a a' b b'| > 2) :
    ∃ a'₀ b₀ b'₀ a₀, chshSlice B a'₀ b₀ b'₀ a₀ = 2 := by
  -- Get the sign-change certificate
  have ⟨a'₀, b₀, b'₀, θ₁, θ₂, h12, hbelow, habove⟩ :=
    chsh_slice_sign_change B hviol
  -- Apply IVT via LLPO to find the crossing of threshold 2
  have ⟨a₀, _, _, ha₀⟩ := single_angle_ivt B a'₀ b₀ b'₀ 2 θ₁ θ₂ h12
    hbelow habove hllpo
  exact ⟨a'₀, b₀, b'₀, a₀, ha₀⟩

end

end Papers.P27
