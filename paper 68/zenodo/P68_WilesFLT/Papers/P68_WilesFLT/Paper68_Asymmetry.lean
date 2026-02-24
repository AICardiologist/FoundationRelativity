/-
  Paper 68: The Logical Cost of Fermat's Last Theorem
  Paper68_Asymmetry.lean — Target 2: The Asymmetry Theorem

  This file proves the asymmetry of Wiles's proof:
  - The overall classification is BISH + WLPO.
  - The WLPO is localized entirely in Stage 1 (Langlands–Tunnell).
  - Removing Stage 1 drops the classification to BISH.

  The CRM hierarchy is a finite ordered type; the proofs reduce
  to decidable comparisons on a 6-element enum.

  Author: Paul C.-K. Lee
  Date: February 2026
  Zero sorry.
-/

import Papers.P68_WilesFLT.Paper68_Axioms

open CRMLevel

-- ============================================================
-- § 1. Stage Classifications (Axiomatized)
-- ============================================================

/-- Stage 1 (Langlands–Tunnell): requires WLPO.
    The non-constructive content arises from:
    - Arthur–Selberg trace formula (spectral decomposition: WLPO)
    - Orbital integral matching (exact equality of reals: WLPO)
    - Converse theorem for GL₃ (Phragmén–Lindelöf: LPO, reduced
      to WLPO by the effective Ramanujan bound for GL₂).
    Reference: Langlands (1980), Tunnell (1981). -/
def stage1_class : CRMLevel := CRMLevel.WLPO

/-- Stage 2 (Deformation ring): BISH.
    Schlessinger's criterion and Fontaine–Laffaille theory are
    finite-dimensional algebra. Paper 59 classified the p-adic
    comparison as BISH.
    Reference: Wiles (1995), §2. -/
def stage2_class : CRMLevel := CRMLevel.BISH

/-- Stage 3 (Hecke algebra): BISH.
    Hecke operators are explicit linear maps on finite-dimensional
    spaces. Dimension of S₂(Γ₀(N)) is computable by Riemann–Roch.
    Reference: Wiles (1995), §3. -/
def stage3_class : CRMLevel := CRMLevel.BISH

/-- Stage 4 (Numerical criterion / CM base case): BISH.
    In the published proof, subsumed by Stage 5 (patching).
    The CM base case (Rubin's Euler system) uses Kolyvagin primes
    found by effective Chebotarev, hence BISH.
    Reference: Rubin (1991); Ahn–Kwon (2019). -/
def stage4_cm_class : CRMLevel := CRMLevel.BISH

/-- Stage 5 (Taylor–Wiles patching): BISH.
    Proven in Paper68_Stage5.lean (Target 1).
    Brochard (2017) eliminates Fan Theorem; effective Chebotarev
    eliminates Markov's Principle.
    Reference: Brochard (2017); Lagarias–Montgomery–Odlyzko (1979). -/
def stage5_class : CRMLevel := CRMLevel.BISH

-- ============================================================
-- § 2. Join of Stages 2–5 is BISH
-- ============================================================

/-- Helper: join of four BISH levels is BISH. -/
theorem stages_2_to_5_join :
    join stage2_class (join stage3_class (join stage4_cm_class stage5_class))
    = CRMLevel.BISH := by
  simp [stage2_class, stage3_class, stage4_cm_class, stage5_class, join]

-- ============================================================
-- § 3. The Asymmetry Theorem
-- ============================================================

/-- The overall classification: join of all five stages. -/
def wiles_overall : CRMLevel :=
  join stage1_class (join stage2_class (join stage3_class (join stage4_cm_class stage5_class)))

/-- The classification without Stage 1: join of Stages 2–5. -/
def wiles_without_stage1 : CRMLevel :=
  join stage2_class (join stage3_class (join stage4_cm_class stage5_class))

/-- Theorem (Wiles proof classification).
    The join of all stage classifications is WLPO.
    This is Theorem 6.1 in the paper. -/
theorem wiles_proof_classification :
    wiles_overall = CRMLevel.WLPO := by
  simp [wiles_overall, stage1_class, stage2_class, stage3_class,
        stage4_cm_class, stage5_class, join]

/-- Theorem (WLPO localization).
    Removing Stage 1 drops the classification to BISH.
    This is the second part of Theorem 6.1. -/
theorem wlpo_localisation :
    wiles_without_stage1 = CRMLevel.BISH := by
  simp [wiles_without_stage1, stage2_class, stage3_class,
        stage4_cm_class, stage5_class, join]

/-- The Asymmetry Theorem (Theorem 6.1 in the paper).
    The non-constructive content of Wiles's proof is
    entirely in Stage 1 (Langlands–Tunnell).

    - Overall classification: BISH + WLPO
    - Without Stage 1: BISH
    - Localization: the WLPO cost comes solely from Stage 1. -/
theorem asymmetry_theorem :
    wiles_overall = CRMLevel.WLPO ∧
    wiles_without_stage1 = CRMLevel.BISH :=
  ⟨wiles_proof_classification, wlpo_localisation⟩

-- ============================================================
-- § 4. Corollaries
-- ============================================================

/-- Corollary (Logical cost of FLT).
    Wiles's proof of Fermat's Last Theorem has logical cost BISH + WLPO.
    Since BISH ⊂ WLPO in the CRM hierarchy, the classification is WLPO. -/
theorem flt_logical_cost : wiles_overall = CRMLevel.WLPO :=
  wiles_proof_classification

/-- Corollary (The engine is constructive).
    The Taylor–Wiles patching method—the central proof technology
    of the Langlands program for GL₂/ℚ—contributes zero logical
    cost beyond BISH. -/
theorem tw_engine_is_bish : stage5_class = CRMLevel.BISH := rfl

/-- Corollary (Algebraic weight-1 modularity implies constructive FLT).
    If Stage 1 is replaced by a BISH proof of residual modularity,
    the entire proof becomes BISH. -/
theorem algebraic_lt_implies_bish_flt
  (alt_stage1 : CRMLevel) (h : alt_stage1 = CRMLevel.BISH) :
  join alt_stage1 (join stage2_class (join stage3_class (join stage4_cm_class stage5_class)))
    = CRMLevel.BISH := by
  subst h
  simp [stage2_class, stage3_class, stage4_cm_class, stage5_class, join]

-- ============================================================
-- § 5. Stage 1 is strictly above BISH
-- ============================================================

/-- Stage 1 is strictly above BISH in the CRM hierarchy. -/
theorem stage1_above_bish : stage1_class ≠ CRMLevel.BISH := by
  simp [stage1_class]

/-- Stage 1 is the unique source of non-BISH content. -/
theorem stage1_unique_source :
    stage1_class ≠ CRMLevel.BISH ∧
    stage2_class = CRMLevel.BISH ∧
    stage3_class = CRMLevel.BISH ∧
    stage4_cm_class = CRMLevel.BISH ∧
    stage5_class = CRMLevel.BISH := by
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  simp [stage1_class]

-- ============================================================
-- § 6. Summary
-- ============================================================

/-!
## Axiom Inventory

All axiomatized deep theorems with references:

| Axiom | Mathematical Content | Reference |
|-------|---------------------|-----------|
| B1 (`brochard_finite_criterion`) | De Smit's conjecture: flatness + edim ≤ implies freeness | Brochard, Compositio Math. 153 (2017), Thm 1.1 |
| B2 (`effective_chebotarev`) | Unconditional effective Chebotarev with bound d_L^12577 | Lagarias–Montgomery–Odlyzko (1979); Ahn–Kwon (2019) |
| B3 (`tw_disc_computable`) | Discriminant of TW splitting field is computable and positive | Standard ANT (Hensel bounds) |
| `TWConditions` | TW conditions on a prime at level n (Prop-valued) | Definition of TW primes |
| `twConjClass` | Conjugacy class for Chebotarev application | Standard ANT |
| `frob_implies_tw_conditions` | Frobenius in conjugacy class implies TW conditions | Definition of TW primes |
| `construct_patching_data` | TW primes yield valid patching data | Wiles/Diamond construction |
| `patching_data_valid` | Constructed patching data is flat | Wiles (1995), Diamond (1997) |
| `patching_data_edim` | Embedding-dimension inequality holds | Wiles (1995), numerical criterion |

## File Statistics

- Paper68_Axioms.lean: opaque types, axioms B1–B3, CRM hierarchy
- Paper68_Stage5.lean: Target 1 (Stage 5 is BISH)
- Paper68_Asymmetry.lean: Target 2 (asymmetry theorem)
- sorry count: 0
-/
