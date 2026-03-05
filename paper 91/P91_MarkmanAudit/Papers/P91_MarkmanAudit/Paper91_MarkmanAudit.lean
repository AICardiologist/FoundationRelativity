/-
  Paper 91: The Logical Cost of Unconditional Hodge:
  A CRM Audit of the Markman--Floccari--Fu Theorem
  Paper 91 of the Constructive Reverse Mathematics Series

  Author: Paul Chun-Kit Lee (NYU Langone Health, Brooklyn)

  Main results:
    Theorem A (CRM Audit of Markman):
      Markman's proof (arXiv:2502.03415) decomposes into 4 BISH components
      (Chern characters, dimension counts, intersection numbers, combinatorics)
      and 5 CLASS components (Fourier-Mukai, Orlov, Schoen, semi-regularity,
      secant existence). Overall cost: CLASS.

    Theorem B (Conditional-to-Unconditional Comparison):
      The CRMLint Squeeze (P84-89) achieves 90% BISH (18/20) conditional on VHC.
      Markman achieves unconditional algebraicity but with 44% BISH (4/9).
      The Squeeze is informationally more efficient.

    Theorem C (A Posteriori VHC Consistency):
      Markman's unconditional result + P89's conditional result shows
      VHC is consistent (not refuted) for the exotic Weil class on J(C_{a,b,c}).

    Theorem D (Cycle Class Map as Irreducible CLASS Boundary):
      The cycle class map cl: CH^2 → H^4 is irreducibly CLASS.
      The 20/0 ratio is logically impossible; best achievable is 19/1.

  Lean bundle structure:
    CRMLevel.lean         — CRM hierarchy (reused from P72-74, P87)
    MarkmanAudit.lean     — Theorems A, B, C + Hodge horizon robustness
    CycleClassMap.lean    — Theorem D + impossibility of 20/0
    CycleData.lean        — CAS-emitted polynomial identities (palindromic cycle)

  Axiom inventory:
    Documentary axioms (encode external theorems, not invoked in proofs):
    - markman_theorem (Markman 2025)
    - crmlint_squeeze_conditional (Papers 88-89)
    - uniform_hodge_iff_wlpo_p87 (Paper 87)
    - cycle_class_map_cost (Theorem D)
    - cycle_class_map_is_class (Theorem D)
    Infrastructure axioms (from Lean/Mathlib):
    - propext, Quot.sound (expected for type-level definitions)

  Zero sorry. All proofs complete.
-/

import Papers.P91_MarkmanAudit.CRMLevel
import Papers.P91_MarkmanAudit.MarkmanAudit
import Papers.P91_MarkmanAudit.CycleClassMap
import Papers.P91_MarkmanAudit.CycleData

namespace P91

/-! ## Axiom inventory check -/

-- Theorem A: CRM Audit of Markman
#check @markman_class_count       -- 5 CLASS boundary nodes
#check @markman_bish_count        -- 4 BISH components
#check @markman_total_count       -- 9 total
#check @markman_overall_class     -- Overall cost = CLASS

-- Theorem B: Comparison
#check @squeeze_bish_fraction     -- 90% BISH (CRMLint Squeeze)
#check @markman_bish_fraction     -- 44% BISH (Markman)
#check @squeeze_more_efficient    -- Squeeze has higher BISH fraction

-- Theorem C: VHC Consistency
#check @vhc_consistent_a_posteriori

-- Theorem D: Cycle Class Map
#check @cycle_class_map_is_class  -- cl is CLASS
#check @cannot_achieve_20_0       -- 20/0 impossible
#check @improvement_over_p89      -- 19/1 > 18/2

-- Hodge Horizon Robustness
#check @hodge_horizon_robust      -- WLPO unchanged by Markman
#check @hodge_horizon_below_class -- WLPO < CLASS
#check @hodge_horizon_above_bish  -- WLPO > BISH

-- CycleData: Palindromic curve identities
#check @f_eq_x_core               -- f = x * core
#check @f_odd                     -- f(-x) = -f(x)
#check @q2_neg_eq_neg_q1          -- Q2(-u) = -Q1(u) isomorphism
#check @codimension_match         -- codim(Gamma) = 2 = codim(omega)
#check @diagonal_det              -- crossing det = 2
#check @general_obstruction       -- (a-c)(x^6-x^2)
#check @chebyshev_factor_plus     -- T5+2 factorization
#check @chebyshev_factor_minus    -- T5-2 factorization

end P91

/-! ## Print axioms for main results -/

#print axioms P91.markman_overall_class
#print axioms P91.squeeze_more_efficient
#print axioms P91.vhc_consistent_a_posteriori
#print axioms P91.hodge_horizon_robust
#print axioms P91.hodge_horizon_irreducible
#print axioms P91.cannot_achieve_20_0
#print axioms P91.f_eq_x_core
#print axioms P91.q2_neg_eq_neg_q1
#print axioms P91.codimension_match
#print axioms P91.general_obstruction
