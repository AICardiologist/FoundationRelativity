/-
  Paper 41: Axiom Calibration of the AdS/CFT Correspondence
  QESScaffolding.lean: Section 6 — The Quantum Extremal Surface

  The Engelhardt-Wall QES prescription:
    S(A) = min_γ [Area(γ)/4G_N + S_bulk(Σ_γ)] = min_γ S_gen(γ)

  Key structural result:
  • Surface existence (argmin) requires FanTheorem (compactness)
  • Observable entropy (infimum) is computable at BISH+LPO
  • FT is scaffolding: holography projects away the compactness cost
  • In the perturbative regime, the surface itself is BISH (Jacobi equation)
-/
import Papers.P41_AdSCFT.Defs

noncomputable section

-- ============================================================
-- QES Surface Existence: FanTheorem (Section 6.1)
-- ============================================================

/-- The direct method of calculus of variations extracts a convergent
    subsequence from a minimizing sequence — a compactness argument
    costing FanTheorem (or its infinite-dimensional analogues,
    Arzelà-Ascoli or Banach-Alaoglu). -/
theorem QES_existence_requires_FT (S : GenEntropy) :
    FanTheorem →
      ∃ x_star, ∀ x, S.gen_entropy x_star ≤ S.gen_entropy x :=
  gen_entropy_minimizer_ft S

-- ============================================================
-- QES Entropy: BISH+LPO (Section 6.2)
-- ============================================================

/-- The boundary CFT does not observe the bulk surface γ*.
    The holographic dictionary states that the boundary entropy is
    the infimum of S_gen. Constructive mathematics can compute the
    infimum of a bounded functional by evaluating on successive
    approximations and applying BMC (≡ LPO, Paper 29).

    FT builds the Platonic surface in the unobservable bulk.
    BISH computes the observable entropy on the boundary. -/
theorem QES_entropy_computable_LPO (S : GenEntropy) :
    LPO →
      ∃ (inf_val : ℝ),
        (∀ x, inf_val ≤ S.gen_entropy x) ∧
        (∀ ε, ε > 0 → ∃ x, S.gen_entropy x < inf_val + ε) :=
  gen_entropy_infimum_lpo S

-- ============================================================
-- The Separation: Infimum vs. Minimizer (Section 6.2)
-- ============================================================

/-- THE SCAFFOLDING META-THEOREM:
    The compactness cost of bulk geometric existence is scaffolding
    for the boundary-observable entropy.

    Part 1: The infimum (observable entropy) needs only LPO.
    Part 2: The minimizer (bulk surface) needs FanTheorem.
    Part 3: LPO alone does NOT give the minimizer.

    This is the holographic principle restated in constructive
    reverse mathematics: holography is the projection that
    eliminates FT. -/
theorem infimum_vs_minimizer :
    -- Part 1: Observable infimum computable with LPO
    (∀ (S : GenEntropy), LPO →
      ∃ (inf_val : ℝ),
        (∀ x, inf_val ≤ S.gen_entropy x) ∧
        (∀ ε, ε > 0 → ∃ x, S.gen_entropy x < inf_val + ε)) ∧
    -- Part 2: Minimizer (geometric surface) requires FanTheorem
    (∀ (S : GenEntropy), FanTheorem →
      ∃ x_star, ∀ x, S.gen_entropy x_star ≤ S.gen_entropy x) ∧
    -- Part 3: LPO alone is insufficient for the minimizer
    ¬(LPO → ∀ (S : GenEntropy),
        ∃ x_star, ∀ x, S.gen_entropy x_star ≤ S.gen_entropy x) :=
  ⟨fun S lpo => gen_entropy_infimum_lpo S lpo,
   fun S ft => gen_entropy_minimizer_ft S ft,
   minimizer_not_from_lpo⟩

-- ============================================================
-- Perturbative QES: BISH (Section 6.3)
-- ============================================================

/-- In the perturbative regime (small G_N corrections), the QES is
    obtained by perturbing the classical RT surface:
      γ_QES = γ_RT + G_N δγ
    The deformation δγ satisfies the Jacobi geodesic deviation equation,
    an ODE sourced by ∇S_bulk. By Picard-Lindelöf (BISH for Lipschitz ODEs),
    the perturbed surface is explicitly BISH-constructible.
    No compactness needed, no FT, not even LPO. -/
theorem QES_perturbative_bish (G_N : ℝ) (hG : G_N > 0) :
    ∃ (delta_gamma : ℝ → ℝ), BISHComputable delta_gamma :=
  QES_jacobi_ode_bish G_N hG

-- ============================================================
-- Summary: QES Calibration
-- ============================================================

/-- Complete QES calibration:
    • Surface existence: FT (scaffolding, projected away by holography)
    • Entropy value (perturbative): BISH
    • Entropy value (non-perturbative): LPO (via infimum/BMC) -/
theorem QES_calibration_summary (G_N : ℝ) (hG : G_N > 0) :
    -- Perturbative surface: BISH
    (∃ (δγ : ℝ → ℝ), BISHComputable δγ) ∧
    -- Observable entropy: LPO
    (∀ (S : GenEntropy), LPO →
      ∃ (inf_val : ℝ), ∀ x, inf_val ≤ S.gen_entropy x) ∧
    -- Surface existence: FT
    (∀ (S : GenEntropy), FanTheorem →
      ∃ x_star, ∀ x, S.gen_entropy x_star ≤ S.gen_entropy x) :=
  ⟨QES_jacobi_ode_bish G_N hG,
   fun S lpo => by
    obtain ⟨v, hv, _⟩ := gen_entropy_infimum_lpo S lpo
    exact ⟨v, hv⟩,
   fun S ft => gen_entropy_minimizer_ft S ft⟩

end
