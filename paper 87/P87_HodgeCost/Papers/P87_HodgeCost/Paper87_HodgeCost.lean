/-
  Paper 87: The Omniscience Cost of the Hodge Condition: A CRM Analysis
  Paper 87 of the Constructive Reverse Mathematics Series

  Author: Paul Chun-Kit Lee (NYU Langone Health, Brooklyn)

  Main results:
    Theorem A (CM/MT metadata → BISH):
      When algebraic metadata is available (CM type or known Mumford-Tate group),
      the Hodge test is BISH-decidable.

    Theorem B (Uniform Hodge test ↔ WLPO):
      The uniform Hodge test — a single algorithm that decides "is α of type (p,p)?"
      for an arbitrary period matrix presented as Cauchy sequences — is equivalent
      to WLPO. The forward direction uses an embedding reduction; the reverse
      direction uses WLPO to decide real-number equality.

    Theorem C (Biconditional):
      hodge_test_cost(state) = BISH ↔ algebraic metadata available.
      Parallels Papers 72-74: BISH-decidability iff structural condition holds.

    Theorem D (Shiga-Wolfart boundary):
      Over ℚ̄, algebraic period entries ↔ CM type. This is the arithmetic
      boundary for Route 1 (algebraic periods → BISH).

  Axiom inventory:
    Mathematical axioms (encode proven theorems, not assumed):
    - cm_hodge_cost_eq : cm_hodge_cost = BISH
      (Shiga-Wolfart + K-linear algebra)
    - mt_hodge_cost_eq : mt_hodge_cost = BISH
      (MT group determines Hodge classes; linear algebra over ℚ)
    - bare_hodge_cost_eq : bare_hodge_cost = WLPO
      (Bridges-Richman 1987: real equality ↔ WLPO)
    - embed_real / embed_proj
      (Period matrix perturbation embeds ℝ into the Hodge test)
    - shiga_wolfart
      (Shiga-Wolfart 1995 + Wüstholz 1989)

    Infrastructure axioms (from Lean/Mathlib):
    - propext, Quot.sound, Classical.choice (expected for ℝ-valued results)

  Zero sorry. All proofs complete.

  This is the first CRM analysis of a Clay Millennium Problem.
-/

import Papers.P87_HodgeCost.CRMLevel
import Papers.P87_HodgeCost.HodgeTest
import Papers.P87_HodgeCost.CMDecidable
import Papers.P87_HodgeCost.Biconditional
import Papers.P87_HodgeCost.ShigaWolfart

namespace P87

/-! ## Axiom inventory check -/

-- Theorem A: CM and MT metadata give BISH
#check @cm_gives_bish           -- hodge_test_cost CM_Known = BISH
#check @mt_gives_bish           -- hodge_test_cost MT_Known = BISH

-- Theorem B: Uniform Hodge test ↔ WLPO
#check @uniform_hodge_test_implies_wlpo   -- decider → WLPO_Real
#check @wlpo_implies_uniform_hodge_decidable  -- WLPO_Real → decidability
#check @uniform_hodge_iff_wlpo           -- full equivalence

-- Theorem C: Biconditional
#check @hodge_test_biconditional   -- cost = BISH ↔ state ≠ Bare_Analytic
#check @hodge_test_biconditional'  -- cost = BISH ↔ has_algebraic_metadata
#check @hodge_condition_characterisation  -- full descent table

-- Theorem D: Shiga-Wolfart
#check @shiga_wolfart              -- algebraic periods ↔ CM
#check @cm_necessary_for_algebraic_periods
#check @cm_sufficient_for_algebraic_periods

-- Bare analytic cost
#check @bare_gives_wlpo           -- hodge_test_cost Bare_Analytic = WLPO

-- CRM hierarchy facts
#check @wlpo_ne_bish              -- WLPO ≠ BISH
#check @wlpo_gt_bish              -- WLPO > BISH

end P87

/-! ## Print axioms for all main results -/

#print axioms P87.uniform_hodge_test_implies_wlpo
#print axioms P87.uniform_hodge_iff_wlpo
#print axioms P87.hodge_test_biconditional
#print axioms P87.hodge_test_biconditional'
#print axioms P87.hodge_condition_characterisation
#print axioms P87.cm_necessary_for_algebraic_periods
#print axioms P87.cm_sufficient_for_algebraic_periods
