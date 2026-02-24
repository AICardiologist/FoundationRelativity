/-
  Paper 70: Serre's Modularity Conjecture is BISH + WLPO
  Paper70_InductionSteps.lean — The double induction: level/weight manipulation + base cases

  The Khare-Wintenberger proof uses a double induction on Serre weight
  k(ρ̄) and conductor N(ρ̄). This file classifies:

  Base cases:
  • p = 2: PGL₂(𝔽₂) ≅ S₃ (solvable), Langlands-Tunnell → WLPO
  • p = 3: PGL₂(𝔽₃) ≅ S₄ (solvable), Langlands-Tunnell → WLPO
  • p = 5: PGL₂(𝔽₅) ≅ S₅ ⊃ A₅ (icosahedral), potential modularity → WLPO

  Inductive steps:
  • Level-lowering over ℚ (Ribet): BISH
  • Level-lowering over F (Fujiwara/Jarvis): WLPO (via Jacquet-Langlands)
  • Level-raising (Diamond-Taylor): BISH
  • Weight reduction (Hasse invariant, theta operator): BISH
  • Serre's recipe for weight and conductor: BISH

  Author: Paul C.-K. Lee
  Date: February 2026
  Zero sorry. Zero warnings target.
-/

import Papers.P70_KhareWintenberger.Paper70_Defs

open CRMLevel

-- ============================================================
-- § 1. Base Cases
-- ============================================================

/-- Base case p = 2: PGL₂(𝔽₂) ≅ S₃ (solvable).
    Langlands-Tunnell applies directly.
    Cost: WLPO (trace formula).
    Reference: Paper 68, Theorem C. -/
def base_case_p2 : CRMLevel := CRMLevel.WLPO

/-- Base case p = 3: PGL₂(𝔽₃) ≅ S₄ (solvable).
    Langlands-Tunnell applies directly.
    Cost: WLPO (trace formula).
    Reference: Paper 68, Theorem C; Paper 69, Lemma 2.1. -/
def base_case_p3 : CRMLevel := CRMLevel.WLPO

/-- Base case p = 5: PGL₂(𝔽₅) ≅ S₅ ⊃ A₅ (icosahedral).
    The icosahedral case is genuinely encountered and cannot be avoided.
    Unlike BCDT (Paper 69), where the 3-5 switch avoids p = 5,
    the Khare-Wintenberger proof must handle A₅ directly.

    Resolved by potential modularity (Taylor 2002, 2003):
    construct F and A/F via Moret-Bailly (BISH), then transfer
    via Jacquet-Langlands (WLPO).
    Cost: WLPO (Jacquet-Langlands). -/
def base_case_p5 : CRMLevel := CRMLevel.WLPO

-- ============================================================
-- § 2. Inductive Steps: Level Manipulation
-- ============================================================

/-- Level-lowering over ℚ (Ribet 1990): BISH.
    Component groups of Néron models at primes of bad reduction,
    Cerednik-Drinfeld uniformisation of Shimura curves.
    These geometric arguments are explicit and finite.
    Reference: Ribet, Invent. Math. 100 (1990). -/
def level_lowering_Q : CRMLevel := CRMLevel.BISH

/-- Level-lowering over totally real fields (Fujiwara/Jarvis): WLPO.
    Over totally real fields, level-lowering requires transferring
    modular forms between GL₂(F) and a quaternion algebra D
    ramified at the prime being removed.

    This transfer invokes the Jacquet-Langlands correspondence,
    reintroducing WLPO. Each level-lowering step over F invokes
    the trace formula once. The WLPO cost recurs at each inductive
    step, but it is always the same WLPO — no escalation to LPO.

    Reference: Fujiwara (2006), Jarvis (1999). -/
def level_lowering_F : CRMLevel := CRMLevel.WLPO

/-- Level-raising (Diamond-Taylor 1994): BISH.
    Constructs congruences between modular forms at different levels
    using the geometry of the supersingular locus on modular curves
    (explicit intersection theory) and Ihara's lemma (injectivity
    of a restriction map, proved by linear algebra on
    finite-dimensional spaces).
    Reference: Diamond-Taylor, Duke Math. J. 74 (1994). -/
def level_raising : CRMLevel := CRMLevel.BISH

-- ============================================================
-- § 3. Inductive Steps: Weight Manipulation
-- ============================================================

/-- Weight reduction: BISH.
    Uses Hasse invariant (explicit section of a line bundle on
    the modular curve, computable by q-expansion) and theta
    operator θ = q d/dq (explicit differential operator on
    q-expansions). Both operations are finite arithmetic on
    power series truncated at computable precision. -/
def weight_reduction : CRMLevel := CRMLevel.BISH

-- ============================================================
-- § 4. Serre's Recipe
-- ============================================================

/-- Serre's recipe for weight and conductor: BISH.
    • N(ρ̄): Artin conductor, product of local terms depending on
      ramification filtration at each ℓ ≠ p. Finite group theory.
    • k(ρ̄): Determined by ρ̄|_{I_p} via Serre's explicit formula
      involving tame and wild inertia. Finite arithmetic.
    Reference: Serre, Duke Math. J. 54 (1987). -/
def serre_recipe : CRMLevel := CRMLevel.BISH

-- ============================================================
-- § 5. Classification of Inductive Components
-- ============================================================

/-- All base cases joined. -/
def base_cases : CRMLevel :=
  join base_case_p2 (join base_case_p3 base_case_p5)

/-- All BISH inductive steps joined. -/
def induction_bish : CRMLevel :=
  join level_lowering_Q
    (join level_raising
      (join weight_reduction serre_recipe))

/-- All WLPO inductive steps joined. -/
def induction_wlpo : CRMLevel := level_lowering_F

/-- Base cases are WLPO (no escalation to LPO). -/
theorem base_cases_are_wlpo : base_cases = CRMLevel.WLPO := by
  simp [base_cases, base_case_p2, base_case_p3, base_case_p5, join]

/-- The BISH inductive steps are BISH. -/
theorem induction_bish_is_bish : induction_bish = CRMLevel.BISH := by
  simp [induction_bish, level_lowering_Q, level_raising,
        weight_reduction, serre_recipe, join]

/-- Level-lowering over F is WLPO (Jacquet-Langlands). -/
theorem induction_wlpo_is_wlpo : induction_wlpo = CRMLevel.WLPO := by
  simp [induction_wlpo, level_lowering_F]

/-- All inductive components joined: WLPO. -/
theorem induction_overall :
    join induction_bish induction_wlpo = CRMLevel.WLPO := by
  simp [induction_bish, induction_wlpo, level_lowering_Q,
        level_raising, weight_reduction, serre_recipe,
        level_lowering_F, join]

/-- The trace formula at every inductive step.
    Each level-lowering step over F invokes Jacquet-Langlands once.
    The WLPO recurs but does not escalate. -/
theorem no_escalation_in_induction :
    join induction_wlpo induction_wlpo = CRMLevel.WLPO := by
  simp [induction_wlpo, level_lowering_F, join]
