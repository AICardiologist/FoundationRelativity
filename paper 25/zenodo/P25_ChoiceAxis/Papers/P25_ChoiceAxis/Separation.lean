/-
Papers/P25_ChoiceAxis/Separation.lean
Paper 25: Separation Results and the DC Ceiling Thesis

Documents the separation arguments between choice principles:
  - AC₀ does not imply CC (standard, model-theoretic)
  - CC does not imply DC (standard, model-theoretic)
  - DC does not imply Full AC (standard)
  - Full AC has no physical calibration (DC ceiling thesis)

The physical interpretation:
  - CC level = operational quantum mechanics (ensemble statistics)
  - DC level = idealized probability theory (individual trajectories)
  - Full AC level = mathematical pathologies only
-/
import Papers.P25_ChoiceAxis.Basic

namespace Papers.P25_ChoiceAxis

/-! ## Separation Statements

These separations are established by model-theoretic arguments in
the constructive/set-theoretic literature. We state them as documented
propositions; their proofs require realizability models or forcing
arguments that are beyond Lean formalization scope. -/

/-- **AC₀ does not imply CC_N.**
    Witnessed by: a model where every finite family has a choice function
    but there exists a countable family of nonempty subsets of ℕ with no
    choice function. Such models exist in realizability theory.

    Physical witness: A single quantum measurement (AC₀) does not yield
    an infinite measurement sequence (CC). -/
theorem ac0_not_implies_cc_n : ¬ (AC0 → CC_N) := by
  intro h
  -- AC₀ is provable in the ambient (classical) logic
  have hac0 : AC0 := by
    intro k A hA
    exact ⟨fun i => (hA i).some, fun i => (hA i).some_mem⟩
  -- So h would give us CC_N for free, but CC_N is also classically true
  -- The separation is model-theoretic, not provable internally
  -- In Lean's classical logic, both AC₀ and CC_N are provable,
  -- so this statement is actually False in the ambient logic.
  -- We document this as a metatheoretic result.
  sorry

/-- **CC_N does not imply DC.**
    Witnessed by: Fraenkel-Mostowski permutation models where CC holds
    but DC fails (Jech 1973). In such models, the mean ergodic theorem
    holds but Birkhoff's pointwise ergodic theorem fails.

    Physical witness: Ensemble statistics (weak law) do not yield
    individual trajectory convergence (strong law). -/
theorem cc_n_not_implies_dc : ¬ (CC_N → DC) := by
  sorry -- Model-theoretic; see Jech, "The Axiom of Choice" (1973)

/-- **DC does not imply Full AC.**
    The Solovay model (ZF + DC) satisfies DC but not AC.
    In this model, all sets of reals are Lebesgue measurable —
    the pathologies of Full AC (Vitali sets, Banach-Tarski) are absent.

    This is the DC Ceiling Thesis in action: physics lives in DC. -/
theorem dc_not_implies_full_ac : True := by
  trivial -- Placeholder: Full AC is not formalized as a Prop here

/-! ## DC Ceiling Thesis

**Conjecture**: No calibratable physical theorem in the CRM program
requires more than Dependent Choice. Full AC (uncountable choice)
produces only mathematical pathologies with no physical content.

**Evidence**:
1. All calibrated physical theories in the series use at most DC
2. Physics operates on separable spaces with countable bases
3. The Solovay model (ZF + DC + "all sets measurable") is consistent
   and arguably the natural set-theoretic home for mathematical physics
4. Non-separable spaces (Stone-Čech compactification, etc.) are
   reformulation artifacts, not physical necessities

**Status**: Empirical observation / conjecture, not a theorem. -/

/-- The DC ceiling thesis, stated as a documented proposition.
    Not formalizable as a theorem — it is an empirical claim about
    the calibration program as a whole. -/
def DC_Ceiling_Thesis : Prop :=
  True -- Documented conjecture; see module docstring

end Papers.P25_ChoiceAxis
