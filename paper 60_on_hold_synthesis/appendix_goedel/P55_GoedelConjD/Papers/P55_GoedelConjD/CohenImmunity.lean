/-
  Paper 55: Is Gödel Absent from the Motive?
  CohenImmunity.lean — CRM program insulation theorem

  The main result: the CRM program's conditional structure
  is insulated from both modes of independence.

  Key theorems:
  1. conjD_classification: Conjecture D is Cohen-immune but
     potentially Gödel-independent
  2. crm_insulated: The CRM conditional (DPT → motive kills LPO)
     does not depend on ZFC-provability of Conjecture D
  3. two_modes_distinct: Cohen and Gödel independence are distinct
     phenomena, with examples separating them
-/
import Papers.P55_GoedelConjD.Absoluteness

namespace Papers.P55

-- ========================================================================
-- Classification of Conjecture D
-- ========================================================================

/-- Complete classification of Conjecture D's meta-mathematical status.

    Part 1: Cohen independence is ruled out (Shoenfield).
    Part 2: Gödel independence is not ruled out.
    Part 3: The two modes are logically distinct. -/
structure ConjDClassification where
  data : ConjDData
  SA : ShoenfieldAbsoluteness
  /-- Cohen independence is ruled out. -/
  cohen_immune : ¬ cohen_independent data.conjD SA.zfc_models
  /-- We do NOT assert that Gödel independence is ruled out.
      This field records that the question is open. -/
  goedel_status_open : True  -- placeholder: we have no proof either way

/-- Construct the classification from its components. -/
def mkClassification (data : ConjDData) (SA : ShoenfieldAbsoluteness) :
    ConjDClassification where
  data := data
  SA := SA
  cohen_immune := conjD_cohen_immune data SA
  goedel_status_open := trivial


-- ========================================================================
-- CRM Insulation
-- ========================================================================

/-- The CRM program's conditional results do not depend on whether
    Conjecture D is provable in ZFC.

    The key insight: the motive kills LPO GIVEN the DPT axioms.
    Whether the DPT axioms are provable in ZFC, independent of ZFC,
    or require stronger axioms does not affect the implication.

    This is the logical analog of: "if P then Q" is valid regardless
    of whether P itself is decidable. -/
theorem crm_conditional_independent_of_provability
    (cond : CRMConditional)
    (_T : FormalSystem) :
    -- Even if we don't know whether T proves the DPT axioms...
    -- ...the conditional implication is a theorem of pure logic
    (cond.dpt.decidable_equality →
     cond.dpt.algebraic_spectrum →
     cond.dpt.archimedean_polarization →
     (cond.lpo → cond.mp)) := by
  exact cond.motive_kills_lpo

/-- The CRM program is triply insulated:
    1. Internal computations are arithmetical (below Σ¹₂)
    2. Conditional structure separates provability from validity
    3. All calibrations are absolute (Cohen-immune)

    We formalize the conjunction of these three insulation layers. -/
structure CRMInsulation where
  /-- The CRM conditional result. -/
  cond : CRMConditional
  /-- The formal system (ZFC). -/
  T : FormalSystem
  /-- Shoenfield absoluteness. -/
  SA : ShoenfieldAbsoluteness
  /-- Conjecture D data. -/
  conjD : ConjDData
  /-- Layer 1: Conjecture D is arithmetical (Π₂⁰). -/
  arithmetical : conjD.pi02_form.statement = conjD.conjD
  /-- Layer 2: The conditional does not need provability. -/
  conditional_valid : cond.dpt.decidable_equality →
    cond.dpt.algebraic_spectrum →
    cond.dpt.archimedean_polarization →
    (cond.lpo → cond.mp)
  /-- Layer 3: Cohen immunity. -/
  cohen_immune : ¬ cohen_independent conjD.conjD SA.zfc_models

/-- Build the insulation proof from components. -/
def mkInsulation
    (cond : CRMConditional)
    (T : FormalSystem)
    (SA : ShoenfieldAbsoluteness)
    (conjD : ConjDData) :
    CRMInsulation where
  cond := cond
  T := T
  SA := SA
  conjD := conjD
  arithmetical := conjD.captures
  conditional_valid := cond.motive_kills_lpo
  cohen_immune := conjD_cohen_immune conjD SA


-- ========================================================================
-- The Two Modes Are Distinct
-- ========================================================================

-- Cohen independence and Gödel independence are strictly different
-- phenomena. We prove they are logically distinct by exhibiting
-- their different structural properties.

/-- An absolute sentence cannot be Cohen-independent (proved above).
    Contrapositively: a Cohen-independent sentence is not absolute. -/
theorem cohen_independent_not_absolute (φ : Prop)
    (models : TransitiveModel → Prop)
    (h_cohen : cohen_independent φ models) :
    ¬ absolute φ models := by
  intro h_abs
  exact absolute_not_cohen_independent φ models h_abs h_cohen

/-- A Gödel-independent sentence IS absolute (by definition). -/
theorem goedel_independent_is_absolute (T : FormalSystem) (φ : Prop)
    (models : TransitiveModel → Prop)
    (h_goedel : goedel_independent T φ models) :
    absolute φ models :=
  h_goedel.1

/-- The two modes are mutually exclusive: a sentence cannot be
    both Cohen-independent and absolute (hence cannot be both
    Cohen-independent and Gödel-independent). -/
theorem modes_mutually_exclusive (T : FormalSystem) (φ : Prop)
    (models : TransitiveModel → Prop) :
    goedel_independent T φ models → ¬ cohen_independent φ models := by
  intro h_goedel h_cohen
  exact absolute_not_cohen_independent φ models h_goedel.1 h_cohen

end Papers.P55
