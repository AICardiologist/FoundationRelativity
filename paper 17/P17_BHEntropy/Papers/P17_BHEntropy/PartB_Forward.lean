/-
Papers/P17_BHEntropy/PartB_Forward.lean
Forward direction: LPO → BMC → Entropy Convergence.

LPO → BMC is [Bridges–Vîță 2006, Theorem 2.1.5]. Axiomatized.

LPO → Entropy Convergence follows because:
1. S_alpha takes values in a two-element set {s_lo, s_hi}
2. S_alpha is non-decreasing (runMax is non-decreasing, s_lo ≤ s_hi by gap)
3. S_alpha is bounded (by max(s_lo, s_hi) = s_hi)
4. BMC applied to S_alpha gives convergence
-/
import Papers.P17_BHEntropy.PartB_EncodedSeq

namespace Papers.P17

/-- LPO implies Bounded Monotone Convergence.
    [Bridges–Vîță 2006, Theorem 2.1.5]. Axiomatized. -/
axiom bmc_of_lpo : LPO → BMC

/-- S_alpha is non-decreasing when entropy_density A_hi ≥ entropy_density A_lo. -/
lemma S_alpha_mono (α : ℕ → Bool) {A_lo A_hi gamma delta : ℝ}
    {hA_lo : A_lo > 0} {hA_hi : A_hi > 0}
    {hg : gamma > 0} {hd : delta > 0}
    (h_le : entropy_density A_lo gamma delta hA_lo hg hd ≤
            entropy_density A_hi gamma delta hA_hi hg hd) :
    Monotone (S_alpha α A_lo A_hi gamma delta hA_lo hA_hi hg hd) := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [S_alpha]
  cases h1 : runMax α n <;> cases h2 : runMax α (n + 1) <;> simp
  · exact h_le
  · exfalso
    have := runMax_le_succ α n
    rw [h1, h2] at this
    exact absurd this (by decide)

/-- S_alpha is bounded above by entropy_density A_hi. -/
lemma S_alpha_le_hi (α : ℕ → Bool) {A_lo A_hi gamma delta : ℝ}
    {hA_lo : A_lo > 0} {hA_hi : A_hi > 0}
    {hg : gamma > 0} {hd : delta > 0}
    (h_le : entropy_density A_lo gamma delta hA_lo hg hd ≤
            entropy_density A_hi gamma delta hA_hi hg hd) (n : ℕ) :
    S_alpha α A_lo A_hi gamma delta hA_lo hA_hi hg hd n ≤
      entropy_density A_hi gamma delta hA_hi hg hd := by
  simp only [S_alpha]
  cases runMax α n <;> simp
  exact h_le

/-- LPO implies entropy convergence for the encoded sequences. -/
theorem lpo_implies_entropy_convergence
    (hLPO : LPO)
    (gamma : ℝ) (hg : gamma > 0)
    (delta : ℝ) (hd : delta > 0) :
    ∃ (A_lo A_hi : ℝ) (hA_lo : A_lo > 0) (hA_hi : A_hi > 0),
    EntropyConvergence A_lo A_hi gamma delta hA_lo hA_hi hg hd := by
  obtain ⟨A_lo, A_hi, gap, hA_lo, hA_hi, _hlt, hgap, h_density_gap⟩ :=
    entropy_density_gap gamma hg delta hd
  refine ⟨A_lo, A_hi, hA_lo, hA_hi, ?_⟩
  intro α
  have hBMC := bmc_of_lpo hLPO
  have h_le : entropy_density A_lo gamma delta hA_lo hg hd ≤
              entropy_density A_hi gamma delta hA_hi hg hd := by linarith
  exact hBMC
    (S_alpha α A_lo A_hi gamma delta hA_lo hA_hi hg hd)
    (entropy_density A_hi gamma delta hA_hi hg hd)
    (S_alpha_mono α h_le)
    (S_alpha_le_hi α h_le)

end Papers.P17
