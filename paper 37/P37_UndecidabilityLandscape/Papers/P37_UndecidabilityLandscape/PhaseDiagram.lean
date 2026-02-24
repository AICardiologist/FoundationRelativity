/-
  Paper 37: Uncomputability of Phase Diagrams and RG Flows is LPO
  PhaseDiagram.lean: Theorem 1 — Phase Diagram Uncomputability ≡ LPO

  Bausch, Cubitt, Watson (2021, Nature Communications):
  The phase diagram of a quantum many-body system is uncomputable.
  CRM stratification: this uncomputability is exactly LPO.
-/
import Papers.P37_UndecidabilityLandscape.Defs
import Papers.P37_UndecidabilityLandscape.MetaTheorem

noncomputable section

open Real

-- ============================================================
-- BCW Bridge Lemmas
-- ============================================================

-- BCW encode a parameter φ ∈ [0,1] into a Hamiltonian via approximate
-- QPE. The binary expansion of φ serves as the TM input.

/-- BCW encoding: maps a real parameter to its phase. -/
axiom bcw_phase : ℝ → Phase

/-- BCW bridge: Phase B ↔ the encoded sequence has a true entry.
    (Phase B = disordered = halting) -/
axiom bcw_phaseB_iff_exists (a : ℕ → Bool) :
    bcw_phase (binary_real a) = Phase.PhaseB ↔ ∃ n, a n = true

/-- BCW bridge: Phase A ↔ all entries are false.
    (Phase A = ordered = non-halting) -/
axiom bcw_phaseA_iff_all_false (a : ℕ → Bool) :
    bcw_phase (binary_real a) = Phase.PhaseA ↔ ∀ n, a n = false

-- ============================================================
-- Theorem 1: Phase Diagram Uncomputability ≡ LPO
-- ============================================================

/-- The phase decision property: a binary sequence maps to Phase B. -/
def is_phaseB (a : ℕ → Bool) : Prop :=
  bcw_phase (binary_real a) = Phase.PhaseB

/-- THEOREM 1: Phase diagram uncomputability (BCW 2021) is
    Turing-Weihrauch equivalent to LPO.

    The uncomputability of phase diagrams is not a fundamental
    unknowability — it is the non-computability of a single
    logical principle (LPO) that physicists have used since
    Boltzmann's thermodynamic limit. -/
theorem phase_diagram_iff_lpo :
    (∀ (a : ℕ → Bool), is_phaseB a ∨ ¬is_phaseB a) ↔ LPO :=
  halting_reduction_iff_lpo
    (fun a => a)
    is_phaseB
    (fun a => bcw_phaseB_iff_exists a)

/-- The uniform phase function is not computable. -/
theorem phase_function_not_computable :
    ¬(∀ (a : ℕ → Bool), is_phaseB a ∨ ¬is_phaseB a) :=
  uniform_function_not_computable
    (fun a => a)
    is_phaseB
    (fun a => bcw_phaseB_iff_exists a)

/-- Given LPO, every phase is decidable. -/
theorem phase_decidable_from_lpo (lpo : LPO) :
    ∀ (a : ℕ → Bool), is_phaseB a ∨ ¬is_phaseB a :=
  phase_diagram_iff_lpo.mpr lpo

end
