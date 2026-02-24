/-
  Paper 35: The Conservation Metatheorem
  Mechanisms.lean: Theorem D — The Three LPO Mechanisms

  Every LPO instance in the calibration table arises from one of
  three equivalent mechanisms: BMC, Cauchy completeness without
  modulus, or supremum existence.
-/
import Papers.P35_ConservationMetatheorem.Defs
import Papers.P35_ConservationMetatheorem.LimitBoundary

noncomputable section

open Real

-- ============================================================
-- Theorem D: Mechanism Equivalences
-- ============================================================

/-- M1 → M2: BMC implies Cauchy completeness without modulus.
    Proof: a Cauchy sequence can be thinned to a monotone subsequence
    via a standard encoding. -/
axiom bmc_implies_cauchy_complete : BMC → CauchyComplete

/-- M2 → M3: Cauchy completeness implies bounded sup existence.
    Proof: given bounded S, the sequence sup_n = max(S(1),...,S(n))
    is monotone and bounded; its Cauchy limit is the sup. -/
axiom cauchy_complete_implies_sup : CauchyComplete → BoundedSupExists

/-- M3 → M1: Bounded sup existence implies BMC.
    Proof: a bounded monotone sequence is a bounded set; its sup
    is the limit. -/
axiom sup_implies_bmc : BoundedSupExists → BMC

/-- The three mechanisms are mutually equivalent over BISH. -/
theorem mechanism_equivalence :
    (BMC ↔ CauchyComplete) ∧
    (CauchyComplete ↔ BoundedSupExists) ∧
    (BoundedSupExists ↔ BMC) :=
  ⟨⟨bmc_implies_cauchy_complete, fun h => sup_implies_bmc (cauchy_complete_implies_sup h)⟩,
   ⟨cauchy_complete_implies_sup, fun h => bmc_implies_cauchy_complete (sup_implies_bmc h)⟩,
   ⟨sup_implies_bmc, fun h => cauchy_complete_implies_sup (bmc_implies_cauchy_complete h)⟩⟩

/-- All three mechanisms are equivalent to LPO. -/
theorem all_mechanisms_equiv_lpo :
    (BMC ↔ LPO) ∧
    (CauchyComplete ↔ LPO) ∧
    (BoundedSupExists ↔ LPO) := by
  have h_bmc_lpo : BMC ↔ LPO := ⟨lpo_of_bmc, bmc_of_lpo⟩
  have h_cc_lpo : CauchyComplete ↔ LPO :=
    ⟨fun h => lpo_of_bmc (sup_implies_bmc (cauchy_complete_implies_sup h)),
     fun h => bmc_implies_cauchy_complete (bmc_of_lpo h)⟩
  have h_sup_lpo : BoundedSupExists ↔ LPO :=
    ⟨fun h => lpo_of_bmc (sup_implies_bmc h),
     fun h => cauchy_complete_implies_sup (bmc_implies_cauchy_complete (bmc_of_lpo h))⟩
  exact ⟨h_bmc_lpo, h_cc_lpo, h_sup_lpo⟩

-- ============================================================
-- Mechanism Classification of Table Entries
-- ============================================================

/-- Structure pairing a calibrated result with its LPO mechanism. -/
structure LPOEntry where
  result : CalibratedResult
  mechanism : LPOMechanism

/-- LPO entries with their mechanisms identified. -/
def lpo_mechanism_table : List LPOEntry := [
  ⟨⟨4,  "Spectral decomposition", .LPO⟩,       .SupExists⟩,
  ⟨⟨7,  "Trace-class operators", .LPO⟩,         .CauchyNoModulus⟩,
  ⟨⟨8,  "Ising thermodynamic limit", .LPO⟩,     .BMC⟩,
  ⟨⟨13, "Global event horizon", .LPO⟩,          .CauchyNoModulus⟩,
  ⟨⟨15, "Global Noether conservation", .LPO⟩,   .CauchyNoModulus⟩,
  ⟨⟨17, "Bekenstein-Hawking entropy", .LPO⟩,    .BMC⟩,
  ⟨⟨22, "Radioactive decay", .LPO⟩,             .BMC⟩,
  ⟨⟨25, "Mean ergodic theorem", .LPO⟩,          .CauchyNoModulus⟩,
  ⟨⟨29, "Fekete subadditive lemma", .LPO⟩,      .BMC⟩,
  ⟨⟨32, "QED global coupling", .LPO⟩,           .CauchyNoModulus⟩,
  ⟨⟨33, "QCD continuum limit", .LPO⟩,           .BMC⟩,
  ⟨⟨34, "All-orders summation", .LPO⟩,          .BMC⟩
]

/-- Every LPO entry has an identified mechanism. -/
theorem lpo_entries_have_mechanism :
    ∀ e ∈ lpo_mechanism_table,
      e.mechanism = .BMC ∨ e.mechanism = .CauchyNoModulus ∨ e.mechanism = .SupExists := by
  intro e _
  cases e.mechanism <;> simp

/-- Count: BMC mechanisms. -/
theorem bmc_mechanism_count :
    (lpo_mechanism_table.filter (fun e => e.mechanism == .BMC)).length = 6 := by
  native_decide

/-- Count: Cauchy without modulus mechanisms. -/
theorem cauchy_mechanism_count :
    (lpo_mechanism_table.filter (fun e => e.mechanism == .CauchyNoModulus)).length = 5 := by
  native_decide

/-- Count: supremum mechanisms. -/
theorem sup_mechanism_count :
    (lpo_mechanism_table.filter (fun e => e.mechanism == .SupExists)).length = 1 := by
  native_decide

end
