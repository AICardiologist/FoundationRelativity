/-
Papers/P2_BidualGap/Constructive/NormabilityFromWLPO.lean
WLPO-dependent normability results

This is the ONLY file where WLPO is used in the reverse direction construction.
All other files remain classical-clean with [propext, Classical.choice, Quot.sound] axioms only.
-/
import Mathlib.Tactic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Papers.P2_BidualGap.Basic

noncomputable section
namespace Papers.P2.Constructive
open Classical ZeroAtInfty

local notation "c₀" => C₀(ℕ, ℝ)

-- ========================================================================
-- WLPO-dependent normability for c₀
-- ========================================================================

/-- WLPO gives `DualIsBanach c₀` - this is where the reverse-math content lives.

The classical proof of DualIsBanach relies on operator norm minimization:
given bounded linear functionals f, g : c₀ →L[ℝ] ℝ, we need to show that f + g
has an operator norm witness (K, proof that K is minimal).

In classical mathematics, this uses:
1. The operator norm ‖f + g‖ = sup{|(f+g)(x)| : ‖x‖ ≤ 1}
2. Minimality: if K' < ‖f + g‖, then ∃x with ‖x‖ ≤ 1 and |(f+g)(x)| > K'

The constructive challenge is the minimality proof, which requires:
- Decidability of |(f+g)(x)| > K' for sequences x ∈ c₀  
- Constructive supremum arguments over the unit ball

WLPO (Weak Limited Principle of Omniscience) provides exactly the decidability needed:
WLPO: ∀(a : ℕ → ℝ), (∀n, a n = 0) ∨ (∃n, a n ≠ 0)

This allows constructive analysis of signs and bounds in the operator norm calculation.
-/
lemma dual_is_banach_c0_from_WLPO : WLPO → DualIsBanach c₀ := by
  intro hWLPO
  constructor
  · -- Prove HasOperatorNorm for sums: f + g has operator norm witness
    intros f g hf hg
    obtain ⟨Nf, hNf_pos, hNf_bound, hNf_min⟩ := hf
    obtain ⟨Ng, hNg_pos, hNg_bound, hNg_min⟩ := hg
    use Nf + Ng
    constructor
    · exact add_nonneg hNf_pos hNg_pos
    constructor
    · -- Upper bound: ‖(f + g) x‖ ≤ (Nf + Ng) * ‖x‖
      intro x
      calc ‖(f + g) x‖ 
        = ‖f x + g x‖ := by simp only [ContinuousLinearMap.add_apply]
        _ ≤ ‖f x‖ + ‖g x‖ := norm_add_le _ _
        _ ≤ Nf * ‖x‖ + Ng * ‖x‖ := add_le_add (hNf_bound x) (hNg_bound x)
        _ = (Nf + Ng) * ‖x‖ := by ring
    · -- Minimality: if K' < Nf + Ng, then ∃x with ‖(f+g) x‖ > K'
      intro K' hK'_lt
      -- This is where WLPO is essential:
      -- We need to constructively find x ∈ c₀ such that |(f+g)(x)| > K'
      -- The classical proof uses supremum properties and sign analysis
      -- WLPO enables the decidability needed for this constructive search
      
      -- Strategy: Use WLPO to analyze the sequence behavior constructively
      -- 1. Since Nf + Ng is minimal for f and g individually, we can construct
      --    sequences that approach these bounds
      -- 2. WLPO allows us to decide when we've found a good enough approximation
      -- 3. Combine these to get the desired bound for f + g
      
      sorry -- WLPO-dependent constructive supremum argument
      -- Implementation requires careful analysis of how WLPO enables
      -- the decidability needed for operator norm minimization
  · -- CompleteSpace property for dual space (this is typically automatic)
    trivial

/-- Same for the dual of c₀. -/
lemma dual_is_banach_c0_dual_from_WLPO : WLPO → DualIsBanach (c₀ →L[ℝ] ℝ) := by
  intro hWLPO
  constructor
  · -- Similar WLPO-dependent argument for the bidual space
    intros f g hf hg  
    obtain ⟨Nf, hNf_pos, hNf_bound, hNf_min⟩ := hf
    obtain ⟨Ng, hNg_pos, hNg_bound, hNg_min⟩ := hg
    use Nf + Ng
    constructor
    · exact add_nonneg hNf_pos hNg_pos
    constructor
    · intro x
      calc ‖(f + g) x‖ 
        = ‖f x + g x‖ := by simp only [ContinuousLinearMap.add_apply]
        _ ≤ ‖f x‖ + ‖g x‖ := norm_add_le _ _
        _ ≤ Nf * ‖x‖ + Ng * ‖x‖ := add_le_add (hNf_bound x) (hNg_bound x)
        _ = (Nf + Ng) * ‖x‖ := by ring
    · intro K' hK'_lt
      sorry -- WLPO-dependent minimality for bidual operators
  · trivial

-- ========================================================================
-- Export for other modules (axiom-clean interface)
-- ========================================================================

/-- Clean interface: other modules can use this without importing WLPO details. -/
theorem c0_dual_is_banach_of_wlpo (h : WLPO) : DualIsBanach c₀ ∧ DualIsBanach (c₀ →L[ℝ] ℝ) :=
  ⟨dual_is_banach_c0_from_WLPO h, dual_is_banach_c0_dual_from_WLPO h⟩

end Papers.P2.Constructive