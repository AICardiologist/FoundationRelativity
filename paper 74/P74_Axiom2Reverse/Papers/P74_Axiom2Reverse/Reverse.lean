/-
  Paper 74: Reverse Direction — BISH Eigenvalues → Algebraic Spectrum

  The new result. If eigenvalue comparison in a spectral category
  is BISH-decidable, then the spectrum must be algebraic.

  Proof (contrapositive):
  Assume Axiom 2 fails (continuous spectrum). Then eigenvalue cost
  = WLPO ≠ BISH. So BISH eigenvalue comparison fails.

  The mathematical content behind the axiom:
  Without geometric origin, the Langlands spectrum includes continuous
  parameters (Maass forms, unramified characters). Testing whether a
  continuous parameter s ∈ C satisfies the Ramanujan bound Re(s) = ½
  is a real-number equality test → WLPO.

  Why WLPO not LPO:
  Eigenvalue comparison is a single equality test, not a search through
  an infinite structure. WLPO decides x = c for real x and algebraic c.
  LPO searches for ∃n, a(n) = 1 in a binary sequence. The distinction
  is existential search (LPO) vs equality test (WLPO).

  The Deligne context:
  For motives with geometric origin, Deligne's Weil I/II proves the
  spectrum IS algebraic — Axiom 2 is a theorem, not a hypothesis.
  The axiom is needed only when the category extends beyond geometric
  origin to the full analytic Langlands spectrum.

  References: Paper 45 (Weil CRM), Deligne (1974, 1980),
    Bump (1997), Bridges-Richman (1987).
-/
import Papers.P74_Axiom2Reverse.Forward

open CRMLevel SpectrumType

-- ============================================================
-- The Spectrum-Eigenvalue Equivalence
-- ============================================================

/-- **Spectrum determines decidability (structural):**
    Axiom 2 holds iff the spectrum is algebraic. -/
theorem axiom2_iff_algebraic (s : SpectrumType) :
    is_algebraic s = true ↔ s = algebraic := by
  cases s
  · exact ⟨fun _ => rfl, fun _ => rfl⟩
  · exact ⟨fun h => Bool.noConfusion h, fun h => SpectrumType.noConfusion h⟩

-- ============================================================
-- The Main Equivalence
-- ============================================================

/-- **THEOREM B (Eigenvalue-Decidability Equivalence):**
    eigenvalue_cost s = BISH ↔ s = algebraic.

    Forward: algebraic spectrum → BISH eigenvalues (Deligne).
    Reverse: BISH eigenvalues → algebraic spectrum
             (contrapositive: continuous → WLPO → not BISH).

    This is the Axiom 2 analogue of Paper 72's Theorem B
    (height_search_equivalence) and Paper 73's Theorem B
    (morphism_decidability_equivalence). The same logical structure
    but with WLPO replacing LPO:
    algebraic spectrum ↔ BISH eigenvalue decidability (Paper 74). -/
theorem eigenvalue_decidability_equivalence (s : SpectrumType) :
    eigenvalue_cost s = BISH ↔ s = algebraic := by
  constructor
  · intro h
    cases s
    · rfl
    · -- continuous: derive contradiction
      unfold eigenvalue_cost at h
      rw [continuous_eigenvalue_cost_eq] at h
      -- h : WLPO = BISH — contradiction
      contradiction
  · intro h
    rw [h]
    exact algebraic_gives_BISH

-- ============================================================
-- Geometric Origin Constraint
-- ============================================================

/-- **COROLLARY (Deligne constraint):**
    Without geometric origin, you cannot have BOTH:
    (1) BISH-decidable eigenvalues, AND
    (2) the full analytic Langlands spectrum.

    - Algebraic (Deligne): (1) holds automatically.
    - Analytic (Langlands): (2) holds, (1) fails (costs WLPO).
    - With geometric origin: both hold (Deligne's theorem). -/
theorem deligne_constraint :
    eigenvalue_cost (langlands_analytic).spectrum = WLPO := by
  show eigenvalue_cost continuous = WLPO
  exact continuous_gives_WLPO

/-- The Ramanujan resolution: if the Ramanujan conjecture is proven,
    the analytic spectrum becomes effectively algebraic (eigenvalues
    satisfy the bound). But the geometric_origin flag remains false. -/
theorem ramanujan_resolution :
    eigenvalue_cost (langlands_with_ramanujan).spectrum = BISH ∧
    (langlands_with_ramanujan).geometric_origin = false := by
  constructor
  · show eigenvalue_cost algebraic = BISH
    exact algebraic_gives_BISH
  · rfl
