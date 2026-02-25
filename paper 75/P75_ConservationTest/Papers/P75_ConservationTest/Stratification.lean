/-
  Paper 75: Three-Layer Stratification

  Theorem A: the CRM cost of the Fargues-Scholze proof of the
  Genestier-Lafforgue LLC is CLASS, determined by the maximum
  of its three independent layers.

  The algebraic layer (BISH) does not contribute to the proof cost.
  The homological (CLASS/Zorn) and geometric (CLASS/BPI) layers
  are independently CLASS, and either alone suffices to force
  the proof into CLASS.

  This stratification is the structural novelty of Paper 75:
  unlike Papers 72–74 (which prove biconditionals within DPT),
  this paper decomposes an external proof into CRM-calibrated layers.
-/
import Papers.P75_ConservationTest.Defs

open CRMLevel ProofLayer

-- ============================================================
-- Layer Cost Function
-- ============================================================

/-- CRM cost assigned to each proof layer. -/
def layer_cost : ProofLayer → CRMLevel
  | algebraic   => algebraic_layer_cost
  | homological  => homological_layer_cost
  | geometric    => geometric_layer_cost

-- ============================================================
-- Proof Cost (join of all layers)
-- ============================================================

/-- The total CRM cost of the Fargues-Scholze proof:
    the join (maximum) of all three layer costs. -/
def fs_proof_cost : CRMLevel :=
  CRMLevel.join algebraic_layer_cost
    (CRMLevel.join homological_layer_cost geometric_layer_cost)

-- ============================================================
-- Layer Evaluations
-- ============================================================

/-- The algebraic layer is constructive (BISH).
    Solidification's inverse limits over finite sets have split
    transition maps → Mittag-Leffler → lim¹ = 0 → no DC. -/
theorem algebraic_is_BISH : layer_cost algebraic = BISH := by
  unfold layer_cost
  exact algebraic_layer_cost_eq

/-- The homological layer is classical (CLASS).
    K-injective resolutions require Zorn's lemma. Čech bypass fails
    due to infinite cohomological dimension of the v-site. -/
theorem homological_is_CLASS : layer_cost homological = CLASS := by
  unfold layer_cost
  exact homological_layer_cost_eq

/-- The geometric layer is classical (CLASS).
    v-covers and the sheaf condition for BunG require BPI. -/
theorem geometric_is_CLASS : layer_cost geometric = CLASS := by
  unfold layer_cost
  exact geometric_layer_cost_eq

-- ============================================================
-- Theorem A: Proof Cost = CLASS
-- ============================================================

/-- **THEOREM A (Stratification):**
    The total CRM cost of the FS proof is CLASS.

    fs_proof_cost = join(BISH, join(CLASS, CLASS)) = CLASS.

    Two independent mechanisms force the proof into CLASS:
    (1) Homological: Zorn's lemma for injective envelopes.
    (2) Geometric: BPI for v-covers.
    The algebraic layer contributes nothing (BISH ≤ CLASS). -/
theorem fs_proof_cost_is_CLASS : fs_proof_cost = CLASS := by
  unfold fs_proof_cost CRMLevel.join
  rw [algebraic_layer_cost_eq, homological_layer_cost_eq, geometric_layer_cost_eq]
  decide

-- ============================================================
-- The Algebraic Layer Is Free
-- ============================================================

/-- **COROLLARY (Solidification is free):**
    The algebraic layer does not contribute to logical cost.
    BISH ≤ CLASS, so removing it does not change the proof cost.

    This corrects earlier programme estimates that placed
    solidification at LPO (via Mittag-Leffler/DC). In fact,
    transition maps of finite sets are split epimorphisms,
    so Mittag-Leffler holds trivially without DC. -/
theorem algebraic_layer_free : algebraic_layer_cost ≤ fs_proof_cost := by
  rw [algebraic_layer_cost_eq, fs_proof_cost_is_CLASS]
  show BISH.toNat ≤ CLASS.toNat
  decide
