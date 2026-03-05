/-
  Paper 98: The Motivic CRM Architecture — Assembly and Axiom Inventory

  Main file importing all components and providing the CRM audit.
-/

import Papers.P98_MotivicCRM.CRMLevel
import Papers.P98_MotivicCRM.Realizations
import Papers.P98_MotivicCRM.ArchimedeanObstruction
import Papers.P98_MotivicCRM.Calibration
import Papers.P98_MotivicCRM.Langlands
import Papers.P98_MotivicCRM.Physics

/-! ## CRM Audit

  **Theorem inventory (0 sorry):**

  ### Core Framework
  - `motive_is_bish` : motive_signature.level = .BISH
  - `non_archimedean_is_bish` : non-archimedean realizations → BISH
  - `non_archimedean_comparison_is_bish` : non-archimedean comparisons → BISH
  - `archimedean_obstruction` : **Theorem A** — the central theorem

  ### Calibration Theorems
  - `hodge_generic_is_class` : Hodge detection (generic) = CLASS
  - `hodge_palindromic_is_bish` : Hodge detection (palindromic) = BISH
  - `bsd_rank_is_bish` : BSD rank verification = BISH
  - `bsd_sha_is_class` : BSD Sha finiteness = CLASS
  - `modularity_core_is_bish` : Modularity algebraic core = BISH
  - `modularity_bridge_is_class` : Modularity analytic bridge = CLASS
  - `excision_1993_to_1995` : CLASS → WKL₀ excision

  ### Langlands
  - `langlands_verification_is_bish` : verification = BISH
  - `langlands_proof_is_class` : proof = CLASS
  - `langlands_gap` : verification < proof
  - `function_field_langlands_is_bish` : function field = BISH
  - `function_field_langlands_is_bish'` : same, via Archimedean Obstruction

  ### Physics
  - `physics_mirror_specific_bish` : specific instances = BISH
  - `physics_mirror_general_class` : general existence = CLASS
  - `physics_gap_qm` : QM gap
  - `physics_gap_gr` : GR gap

  **Axiom inventory (actual):**
  - `propext` : propositional extensionality (Lean infrastructure)
  - `Quot.sound` : quotient soundness (Lean infrastructure)
  - `native_decide` : kernel-trusted decision procedure (calibration theorems)
  - No `Classical.choice`. No mathematical axioms.
-/

-- Axiom check: the core theorem
#print axioms archimedean_obstruction

-- Axiom check: calibration theorems
#print axioms hodge_generic_is_class
#print axioms hodge_palindromic_is_bish
#print axioms bsd_rank_is_bish
#print axioms bsd_sha_is_class
#print axioms modularity_core_is_bish
#print axioms modularity_bridge_is_class
#print axioms excision_1993_to_1995

-- Axiom check: Langlands
#print axioms function_field_langlands_is_bish
#print axioms function_field_langlands_is_bish'

-- Axiom check: physics
#print axioms physics_gap_qm
#print axioms physics_gap_gr
