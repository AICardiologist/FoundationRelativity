/-
  Paper 28: Newton vs. Lagrange — Constructive Stratification of Classical Mechanics
  FTHalf.lean — The FT half: minimizer existence requires the Fan Theorem

  The Fan Theorem (= EVT_max, Berger 2005) is equivalent to EVT_min.
  Since the harmonic action is continuous on [0,1], EVT_min gives a
  minimizer. Conversely, universal minimizer existence on [0,1] implies
  EVT_min, which implies EVT_max = FanTheorem.

  This establishes: (∀ f continuous on [0,1], ∃ minimizer) ↔ FanTheorem.

  The equivalence proofs are re-derived inline from Paper 23's technique
  (apply EVT to −f).
-/
import Papers.P28_NewtonLagrange.Defs

namespace Papers.P28

noncomputable section

-- ========================================================================
-- EVT_max ↔ EVT_min (re-derived from Paper 23)
-- ========================================================================

/-- EVT_max implies EVT_min: apply the max theorem to −f.
    (Paper 23, Theorem evt_min_of_evt_max.) -/
theorem evt_min_of_evt_max (h : EVT_max) : EVT_min := by
  intro f hf
  obtain ⟨x, hx_mem, hx_max⟩ := h (fun t => -f t) (hf.neg)
  exact ⟨x, hx_mem, fun y hy => by linarith [hx_max y hy]⟩

/-- EVT_min implies EVT_max: apply the min theorem to −f.
    (Paper 23, Theorem evt_max_of_evt_min.) -/
theorem evt_max_of_evt_min (h : EVT_min) : EVT_max := by
  intro f hf
  obtain ⟨x, hx_mem, hx_min⟩ := h (fun t => -f t) (hf.neg)
  exact ⟨x, hx_mem, fun y hy => by linarith [hx_min y hy]⟩

/-- EVT_max and EVT_min are equivalent. -/
theorem evt_max_iff_evt_min : EVT_max ↔ EVT_min :=
  ⟨evt_min_of_evt_max, evt_max_of_evt_min⟩

-- ========================================================================
-- Continuity of the harmonic action
-- ========================================================================

/-- The harmonic action S(q) = m(q−A)² + m(B−q)² − (k/4)(A² + q²)
    is continuous as a function of q.
    This is immediate: it is a polynomial (quadratic) in q. -/
theorem harmonicAction2_continuous (p : HOParams) :
    Continuous (harmonicAction2 p) := by
  unfold harmonicAction2
  fun_prop

/-- Continuity restricted to [0,1]. -/
theorem harmonicAction2_continuousOn (p : HOParams) :
    ContinuousOn (harmonicAction2 p) (Set.Icc 0 1) :=
  (harmonicAction2_continuous p).continuousOn

-- ========================================================================
-- FT → minimizer exists
-- ========================================================================

/-- The Fan Theorem implies the harmonic action attains its minimum on [0,1].

    Proof chain: FanTheorem = EVT_max → EVT_min, then apply EVT_min to
    the harmonic action (which is continuous on [0,1]). -/
theorem minimizer_of_ft (p : HOParams) (hft : FanTheorem) :
    ∃ q ∈ Set.Icc (0 : ℝ) (1 : ℝ),
      ∀ q' ∈ Set.Icc (0 : ℝ) (1 : ℝ),
        harmonicAction2 p q ≤ harmonicAction2 p q' := by
  exact evt_min_of_evt_max hft (harmonicAction2 p) (harmonicAction2_continuousOn p)

-- ========================================================================
-- The full equivalence: universal minimizer ↔ FanTheorem
-- ========================================================================

/-- Universal minimizer existence on [0,1] is equivalent to the Fan Theorem.

    Forward: if every continuous f on [0,1] attains its minimum (= EVT_min),
    then EVT_max holds (apply to −f), hence FanTheorem holds.

    Backward: FanTheorem = EVT_max → EVT_min (apply to −f). -/
theorem minimizer_iff_ft :
    (∀ (f : ℝ → ℝ), ContinuousOn f (Set.Icc 0 1) →
      ∃ x ∈ Set.Icc (0 : ℝ) (1 : ℝ), ∀ y ∈ Set.Icc (0 : ℝ) (1 : ℝ), f x ≤ f y)
    ↔ FanTheorem :=
  ⟨fun h => evt_max_of_evt_min h, fun hft => evt_min_of_evt_max hft⟩

-- ========================================================================
-- Axiom audit (FT verification)
-- ========================================================================

-- FanTheorem is a hypothesis, not an axiom, so these should be clean.
-- harmonicAction2_continuous may show Classical.choice (Mathlib topology infra).
#print axioms evt_min_of_evt_max
#print axioms evt_max_of_evt_min
#print axioms harmonicAction2_continuous
#print axioms minimizer_of_ft
#print axioms minimizer_iff_ft

end

end Papers.P28
