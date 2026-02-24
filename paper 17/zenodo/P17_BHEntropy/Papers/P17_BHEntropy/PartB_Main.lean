/-
Papers/P17_BHEntropy/PartB_Main.lean
Assembly of the Entropy Convergence ↔ LPO equivalence (Theorem 4.4, Part B).

Main result:
  For the black hole entropy model based on LQG spin network state counting,
  the assertion that the entropy density S(A)/A converges to a completed real
  number as A → ∞ is equivalent to LPO (Limited Principle of Omniscience)
  over BISH.

Forward: LPO → BMC → convergence [Bridges–Vîță 2006] (axiomatized).
Backward: Convergence → LPO by encoding binary sequences into entropy
  density sequences and extracting decisions from the gap.

Combined with Part A:
  - Part A: the entropy count is BISH-computable (no omniscience)
  - Part B: the limit assertion costs exactly LPO
  - Together: LPO is genuine but dispensable for finite predictions

Axiom profile:
  entropy_convergence_implies_lpo: [propext, Quot.sound, Classical.choice,
    admissible_set_finite, entropy_density_gap]
  bh_entropy_lpo_equiv: additionally depends on [bmc_of_lpo]
-/
import Papers.P17_BHEntropy.PartB_Forward
import Papers.P17_BHEntropy.PartB_Backward

namespace Papers.P17

-- ========================================================================
-- The Equivalence Theorem
-- ========================================================================

/-- **Entropy convergence ↔ LPO (Theorem 4.4, Part B).**

    Over BISH, the assertion that the encoded entropy density sequence
    converges for all binary sequences α is equivalent to the Limited
    Principle of Omniscience.

    The equivalence uses specific gap-witness areas A_lo, A_hi from the
    entropy density gap lemma. LPO is equivalent to the convergence
    statement at these specific areas.

    Forward (LPO → convergence): via BMC [Bridges–Vîță 2006]. Axiomatized.
    Backward (convergence → LPO): by encoding binary sequences into
    entropy density sequences and extracting decisions from the gap.

    Combined with Part A (bh_entropy_computable), this establishes that
    the LPO cost of the thermodynamic-limit assertion is genuine (equivalent
    to a known omniscience principle) and dispensable (finite entropy
    computations require no omniscience). -/
theorem bh_entropy_lpo_equiv
    (gamma : ℝ) (hg : gamma > 0)
    (delta : ℝ) (hd : delta > 0) :
    ∃ (A_lo A_hi : ℝ) (hA_lo : A_lo > 0) (hA_hi : A_hi > 0),
      (LPO ↔ EntropyConvergence A_lo A_hi gamma delta hA_lo hA_hi hg hd) := by
  -- Obtain gap witnesses
  obtain ⟨A_lo, A_hi, gap, hA_lo, hA_hi, hlt, hgap, h_density_gap⟩ :=
    entropy_density_gap gamma hg delta hd
  refine ⟨A_lo, A_hi, hA_lo, hA_hi, ?_⟩
  constructor
  · -- Forward: LPO → convergence
    intro hLPO α
    have hBMC := bmc_of_lpo hLPO
    have h_le : entropy_density A_lo gamma delta hA_lo hg hd ≤
                entropy_density A_hi gamma delta hA_hi hg hd := by linarith
    exact hBMC
      (S_alpha α A_lo A_hi gamma delta hA_lo hA_hi hg hd)
      (entropy_density A_hi gamma delta hA_hi hg hd)
      (S_alpha_mono α h_le)
      (S_alpha_le_hi α h_le)
  · -- Backward: convergence → LPO
    intro h_conv
    exact entropy_convergence_implies_lpo gamma hg delta hd h_conv hgap h_density_gap

-- ========================================================================
-- Axiom audit
-- ========================================================================

-- The backward direction depends on the gap axiom:
#print axioms entropy_convergence_implies_lpo

-- The full equivalence depends on both axiomatized directions:
#print axioms bh_entropy_lpo_equiv

end Papers.P17
