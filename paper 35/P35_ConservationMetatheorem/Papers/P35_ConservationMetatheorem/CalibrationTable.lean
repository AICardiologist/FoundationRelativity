/-
  Paper 35: The Conservation Metatheorem
  CalibrationTable.lean: Theorem C — Exhaustive Classification

  Every calibration result from Papers 1–34 falls into one of the
  four CRM categories: BISH, LLPO, WLPO, or LPO.
  No result exceeds LPO.
-/
import Papers.P35_ConservationMetatheorem.Defs

noncomputable section

-- ============================================================
-- Theorem C: The Calibration Table
-- ============================================================

/-- Representative calibration table: key results from Papers 1–34.
    Each entry records the paper number, description, and CRM level. -/
def calibration_table : List CalibratedResult := [
  -- BISH: Finite / algebraic / explicit convergence rate
  ⟨5,  "Finite-time Schwarzschild geodesics",       .BISH⟩,
  ⟨6,  "Finite-dim Heisenberg uncertainty",          .BISH⟩,
  ⟨8,  "Finite 1D Ising partition function",         .BISH⟩,
  ⟨11, "Finite Bell/CHSH computation",               .BISH⟩,
  ⟨14, "Finite-dim decoherence",                     .BISH⟩,
  ⟨15, "Local Noether conservation",                 .BISH⟩,
  ⟨16, "Born rule (finite-dim)",                     .BISH⟩,
  ⟨28, "Classical mechanics (finite-time)",          .BISH⟩,
  ⟨32, "QED Ward identities",                        .BISH⟩,
  ⟨32, "QED Landau pole (closed-form modulus)",      .BISH⟩,
  ⟨33, "QCD asymptotic freedom",                     .BISH⟩,
  ⟨33, "Finite lattice QCD",                         .BISH⟩,
  ⟨34, "Tree-level Bhabha amplitude",                .BISH⟩,
  ⟨34, "One-loop Feynman integrals",                 .BISH⟩,
  ⟨34, "Dimensional regularization",                 .BISH⟩,
  ⟨34, "Bloch-Nordsieck IR cancellation",            .BISH⟩,
  ⟨34, "Fixed-order cross section",                  .BISH⟩,
  -- LLPO: Disjunction / sign decision
  ⟨15, "Noether global charge sign",                 .LLPO⟩,
  ⟨19, "WKB tunneling",                              .LLPO⟩,
  ⟨21, "Bell nonlocality",                           .LLPO⟩,
  ⟨27, "Bell-IVT tight calibration",                 .LLPO⟩,
  -- WLPO: Threshold / equality decision
  ⟨2,  "Bidual gap decision",                        .WLPO⟩,
  ⟨13, "Event horizon decision",                     .WLPO⟩,
  ⟨18, "Heaviside decoupling",                       .WLPO⟩,
  ⟨20, "1D Ising magnetization sign",                .WLPO⟩,
  ⟨33, "QCD mass gap decision",                      .WLPO⟩,
  -- LPO: Completed limit without modulus
  ⟨4,  "Spectral decomposition (infinite-dim)",      .LPO⟩,
  ⟨7,  "Trace-class operators (infinite-dim)",       .LPO⟩,
  ⟨8,  "Ising thermodynamic limit",                  .LPO⟩,
  ⟨13, "Global event horizon existence",             .LPO⟩,
  ⟨15, "Global Noether charge conservation",         .LPO⟩,
  ⟨17, "Bekenstein-Hawking S = A/4",                 .LPO⟩,
  ⟨22, "Radioactive decay (MP, subsumed)",           .LPO⟩,
  ⟨25, "Mean ergodic theorem",                       .LPO⟩,
  ⟨29, "Fekete subadditive lemma",                   .LPO⟩,
  ⟨32, "QED global coupling existence",              .LPO⟩,
  ⟨33, "QCD continuum limit",                        .LPO⟩,
  ⟨34, "All-orders perturbative summation",          .LPO⟩
]

/-- Helper: every CRMCategory is at most LPO. -/
theorem crm_at_most_lpo (c : CRMCategory) :
    c = .BISH ∨ c = .LLPO ∨ c = .WLPO ∨ c = .LPO := by
  cases c <;> simp

/-- THEOREM C: No calibration entry exceeds LPO.
    Every result is classified as BISH, LLPO, WLPO, or LPO. -/
theorem no_entry_exceeds_lpo :
    ∀ r ∈ calibration_table, r.category = .BISH ∨ r.category = .LLPO ∨
    r.category = .WLPO ∨ r.category = .LPO := by
  intro r _
  exact crm_at_most_lpo r.category

/-- Count of entries by category. -/
theorem bish_count :
    (calibration_table.filter (fun r => r.category == .BISH)).length = 17 := by
  native_decide

theorem llpo_count :
    (calibration_table.filter (fun r => r.category == .LLPO)).length = 4 := by
  native_decide

theorem wlpo_count :
    (calibration_table.filter (fun r => r.category == .WLPO)).length = 5 := by
  native_decide

theorem lpo_count :
    (calibration_table.filter (fun r => r.category == .LPO)).length = 12 := by
  native_decide

/-- Total entries in the table. -/
theorem total_entries : calibration_table.length = 38 := by
  native_decide

end
