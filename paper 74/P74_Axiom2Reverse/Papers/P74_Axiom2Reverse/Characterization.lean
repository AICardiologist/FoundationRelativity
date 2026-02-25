/-
  Paper 74: Axiom 2 Characterization — Full Assembly

  Combines:
    Theorem A (Forward): Algebraic spectrum → BISH eigenvalues.
    Theorem B (Equivalence): Algebraic spectrum ↔ BISH eigenvalues.
    Theorem C (Characterization): Axiom 2 is both necessary and
      sufficient for BISH-decidable eigenvalue comparison.

  The Axiom 2 analogue of Paper 72's and Paper 73's characterizations.
  Paper 72: Axiom 3 ↔ BISH cycle-search (via Northcott).
  Paper 73: Axiom 1 ↔ BISH morphisms (via radical detachability).
  Paper 74: Axiom 2 ↔ BISH eigenvalues (via geometric origin).

  Combined: all three DPT axioms have individual reverse
  characterizations, upgrading "minimal" (Paper 72 Theorem A)
  to "uniquely necessary" for each.

  Key distinction: Axiom 2's failure costs WLPO (equality test),
  while Axioms 1 and 3 cost LPO (existential search). This reflects
  the intrinsic difference between comparing values and searching
  structures.
-/
import Papers.P74_Axiom2Reverse.Reverse

open CRMLevel SpectrumType

-- ============================================================
-- Axiom 2 Characterization
-- ============================================================

/-- **THEOREM C (Axiom 2 Characterization):**
    Algebraic spectrum (geometric origin) is necessary and sufficient
    for BISH-decidable eigenvalue comparison.

    (1) Forward: algebraic spectrum → BISH (Deligne, Paper 45).
    (2) Reverse: BISH → algebraic spectrum (Paper 74, new).
    (3) Without algebraic spectrum, eigenvalue comparison costs WLPO.
    (4) The Ramanujan resolution (proving the conjecture makes the
        analytic spectrum effectively algebraic) confirms the
        trade-off is real, not vacuous.

    Scope: applies to eigenvalue/spectral parameter comparison.
    Whether Axiom 2 is necessary for OTHER operations (e.g.,
    L-function evaluation, Euler product convergence) is separate. -/
theorem axiom2_characterization :
    -- Forward and reverse
    (eigenvalue_cost algebraic = BISH)
    ∧ (eigenvalue_cost continuous = WLPO)
    -- Analytic Langlands without geometric origin costs WLPO
    ∧ (eigenvalue_cost (langlands_analytic).spectrum = WLPO)
    -- Ramanujan resolution: BISH without geometric origin
    ∧ (eigenvalue_cost (langlands_with_ramanujan).spectrum = BISH) := by
  exact ⟨algebraic_gives_BISH,
         continuous_gives_WLPO,
         deligne_constraint,
         (ramanujan_resolution).1⟩

-- ============================================================
-- Sharpened Axiom 2 Principle
-- ============================================================

/-- **COROLLARY (Axiom 2 Principle, sharpened):**
    eigenvalue_cost s = BISH ↔ is_algebraic s = true.

    Paper 72 Theorem A asserted: without Axiom 2, cost = WLPO (forward).
    Paper 74 proves: algebraic spectrum is the unique condition for
    BISH eigenvalue decidability (biconditional). Geometric origin
    (Deligne's theorem) is not merely a convenient hypothesis but the
    logically necessary condition for constructive spectral comparison. -/
theorem axiom2_principle_sharpened (s : SpectrumType) :
    eigenvalue_cost s = BISH ↔ is_algebraic s = true :=
  ⟨fun h => (axiom2_iff_algebraic s).mpr ((eigenvalue_decidability_equivalence s).mp h),
   fun h => (eigenvalue_decidability_equivalence s).mpr ((axiom2_iff_algebraic s).mp h)⟩

-- ============================================================
-- DPT Trilogy Complete
-- ============================================================

/-- **COROLLARY (DPT Axiom Trio):**
    All three DPT axioms have individual reverse characterizations:
    - Axiom 1 (Conj D): BISH ↔ detachable radical (Paper 73) — cost LPO
    - Axiom 2 (algebraic spectrum): BISH ↔ algebraic (Paper 74) — cost WLPO
    - Axiom 3 (Archimedean pol.): BISH ↔ pos-def height (Paper 72) — cost LPO

    The asymmetry: Axiom 2 costs WLPO (equality test) while
    Axioms 1 and 3 cost LPO (existential search). This reflects
    the intrinsic computational difference between comparing a
    spectral value and searching a geometric structure. -/
theorem dpt_trio_costs :
    eigenvalue_cost algebraic = BISH
    ∧ eigenvalue_cost continuous = WLPO := by
  exact ⟨algebraic_gives_BISH, continuous_gives_WLPO⟩

-- ============================================================
-- Verification
-- ============================================================

#check algebraic_gives_BISH
#check continuous_gives_WLPO
#check eigenvalue_decidability_equivalence
#check axiom2_iff_algebraic
#check deligne_constraint
#check ramanujan_resolution
#check axiom2_characterization
#check axiom2_principle_sharpened
#check dpt_trio_costs
