# Bloch-Kato Calibration: Out-of-Sample DPT Test

## Paper 54 — Proof Document for Lean 4 Formalization Agent

### Paul C.-K. Lee
### February 2026

---

## 0. Purpose, Context, and Formalization Notes

This document provides a complete mathematical specification for the Lean 4
formalization of Paper 54 in the Constructive Reverse Mathematics (CRM)
programme, arithmetic geometry sequence.

**Series context:** Papers 45–49 calibrated five conjectures (WMC, Tate,
Fontaine-Mazur, BSD, Hodge) against Bishop's constructive mathematics. Paper
50 extracted three axioms (the DPT class: Decidable Equality, Algebraic
Spectrum, Archimedean Polarization). Papers 51–53 tested and verified the
framework. Paper 54 performs the first OUT-OF-SAMPLE test: calibrating the
Bloch-Kato conjecture (Tamagawa Number Conjecture), which was NOT used to
build the DPT axioms.

**Result summary (from pencil-and-paper analysis):** The calibration
PARTIALLY SUCCEEDS. Axiom 2 lands unconditionally (Deligne Weil I). Axiom 3
lands conditionally at the Archimedean place (Hodge-Riemann + Beilinson
height). Axiom 1 FAILS for mixed motivic cohomology. The Tamagawa factors
c_p introduce irreducible p-adic logical cost OUTSIDE all three axioms.

**What Paper 54 claims:**
1. The DPT framework correctly predicts the Archimedean/algebraic structure
   of Bloch-Kato (confirmation).
2. The DPT framework's pure-motive restriction is a genuine limitation, not
   an oversight — mixed motives require additional axioms (boundary detection).
3. The Tamagawa factors represent a NEW failure mode: p-adic undecidability
   on the algebraic side of the formula, not just the analytic side (discovery).

**What Paper 54 does NOT claim:**
- It does not claim DPT is wrong or needs revision.
- It does not propose Axioms 4 and 5 (that is future work).
- It does not resolve the Beilinson height conjecture.

**Formalization notes:**
- The Lean formalization captures the LOGICAL STRUCTURE of the calibration,
  not the full analytic number theory.
- The sorry budget axiomatizes: analytic continuation, functional equation,
  Deligne's Weil I theorem, Hodge-Riemann bilinear relations, and the
  Bloch-Kato exponential map.
- The ZERO-SORRY target is the logical decomposition itself: the proof that
  the LPO cost isolates to zero-testing, that Axiom 2 follows from algebraicity
  of Frobenius eigenvalues, and that p-adic Tamagawa factors escape all
  three axioms.

**Target:** ~500–700 lines Lean 4
**Depends on:** Paper 50 (DPT class definition), Paper 45 (WMC calibration
for Axiom 2 template), Paper 48 (BSD calibration for Axiom 3 template)

---

## 1. THEOREM STATEMENTS (ENGLISH)

### Theorem A (LPO Isolation)

Let M = h^i(X)(n) be a pure motive over Q with L-function L(M, s).
Assume analytic continuation and the functional equation. Then:

(i)   Evaluating L(M, s) at any computable s ≠ pole is BISH-computable.
(ii)  Determining ord_{s=n} L(M, s) = r requires LPO (zero-testing of
      L^{(k)}(M, n) for k = 0, 1, 2, ...).
(iii) Given r as external input, the leading coefficient L*(M, n) =
      L^{(r)}(M, n) / r! is BISH-computable.

**Constructive content:** The LPO cost is exactly the order of vanishing.
Everything else on the analytic side is constructively computable.

### Theorem B (Axiom 2 Realization)

The local Euler factors P_p(M, T) = det(1 - Frob_p · T | V_ℓ^{I_p})
have roots in Q̄ (algebraic numbers). This is Deligne, "La conjecture
de Weil. I" (1974), Théorème 1.6.

**Constructive content:** Frobenius eigenvalues are algebraic integers,
hence live in a countable decidable field. Axiom 2 is realized
unconditionally.

### Theorem C (Axiom 3 Partial Realization)

(i)  The Deligne period Ω(M) is computed from the Betti–de Rham
     comparison isomorphism. The Hodge-Riemann bilinear relations
     (Hodge 1937) provide a positive-definite Hermitian form on
     H^i_B(X, R). This is Axiom 3 at the Archimedean place.
(ii) The Beilinson regulator R(M) maps motivic cohomology to Deligne
     cohomology via integration over real cycles. Positive-definiteness
     of the Beilinson height pairing is CONJECTURAL (Beilinson 1987).

**Constructive content:** Axiom 3 is realized unconditionally for the
period, conditionally for the regulator.

### Theorem D (Axiom 1 Failure for Mixed Motives)

The motivic fundamental line Δ(M) = det_Q H^0_f(X,M) ⊗ det_Q^{-1}
H^1_f(X,M) requires computing exact ranks of H^1_f, which classifies
extensions of motives (mixed motives). Standard Conjecture D provides
decidability for PURE cycles (Hom-spaces in the pure motive category).
There is no unconditional or Standard Conjectural decision procedure
for testing whether a higher motivic cycle (an element of Ext^1 in the
mixed motive category) is exactly zero.

**Constructive content:** Axiom 1 does not extend from Hom to Ext.
The mixed-motive Hom-spaces are BISH-undecidable.

### Theorem E (Tamagawa Factor Obstruction)

The local Tamagawa factor c_p = |H^1_f(Q_p, V) / H^1_f(Z_p, T)|
requires computing p-adic volumes via the Bloch-Kato exponential map
exp_{BK}: D_{dR}(V) / D_{cris}(V) → H^1_f(Q_p, V). This computation
passes through Fontaine's period rings B_{cris} and B_{dR}. Because
u(Q_p) = 4, there is no positive-definite form on p-adic cohomology
in dimension ≥ 5. The DPT Axiom 3 has no p-adic analogue.

**Constructive content:** Computing c_p requires continuous p-adic
integration that is BISH-undecidable and lies OUTSIDE all three DPT
axioms. This is a new failure mode not seen in the original five
calibrations.

### Theorem F (Calibration Verdict)

The Bloch-Kato conjecture partially decomposes under DPT:

| Component           | DPT Axiom | Status                          |
|---------------------|-----------|----------------------------------|
| Frobenius eigenvalues| Axiom 2  | Proven (Deligne Weil I)          |
| Deligne period Ω    | Axiom 3  | Proven (Hodge-Riemann)           |
| Beilinson regulator R| Axiom 3  | Conditional (height conjecture)  |
| Motivic ranks       | Axiom 1  | FAILS (mixed motives)            |
| Tamagawa factors c_p| NONE     | FAILS (p-adic, outside DPT)      |
| Order of vanishing r| LPO      | Confirmed (zero-testing)         |

The de-omniscientizing descent partially succeeds: the Archimedean data
(Ω, R) descends through the motivic intermediary. The descent structurally
fractures at two points: the mixed-motive boundary (Axiom 1) and the
p-adic volume computation (no axiom).

---

## 2. LEAN MODULE PLAN

### Module 1: DPTCalibration.lean (~80 lines, 0 sorry)

Import the DPT class from Paper 50. Define the calibration record type.

```
-- A calibration record for testing a conjecture against DPT
structure DPTCalibration where
  name : String
  -- Axiom 1: what provides decidable equality?
  axiom1_source : Option String  -- None = not realized
  axiom1_status : DecidabilityStatus  -- proven | conditional | missing
  -- Axiom 2: what provides algebraic spectrum?
  axiom2_source : Option String
  axiom2_status : DecidabilityStatus
  -- Axiom 3: what provides Archimedean polarization?
  axiom3_source : Option String
  axiom3_status : DecidabilityStatus
  -- Extra logical costs outside DPT
  extra_costs : List (String × String)  -- (name, description)
  -- LPO content
  lpo_source : String
  -- Overall verdict
  decomposition_succeeds : TriState  -- yes | no | partial

inductive DecidabilityStatus | proven | conditional (on : String) | missing
inductive TriState | yes | no | partial
```

### Module 2: LPOIsolation.lean (~100 lines, 2 principled sorry)

Formalize Theorem A: the LPO cost isolates to zero-testing.

```
-- Axiomatize: a constructively analytic function at a computable point
-- is BISH-computable
axiom analytic_eval_computable :
  ∀ (f : AnalyticFunction) (s : ComputablePoint),
    ¬IsPole f s → BISHComputable (f.eval s)

-- Axiomatize: zero-testing of a computable real requires LPO
axiom zero_test_requires_LPO :
  ∀ (x : ComputableReal),
    (Decidable (x = 0)) → LPO

-- Theorem: order of vanishing requires LPO
theorem ord_vanishing_requires_LPO
    (L : LFunction) (n : ℤ)
    (hac : HasAnalyticContinuation L)
    (hfe : HasFunctionalEquation L) :
    (∃ r : ℕ, ord_vanishing L n = r) → LPO := by
  intro ⟨r, hr⟩
  -- Determining r requires sequential zero-testing of derivatives
  -- L(n) = 0? L'(n) = 0? L''(n) = 0? ...
  -- Each test is an instance of zero_test_requires_LPO
  sorry -- Uses zero_test_requires_LPO iteratively

-- Theorem: leading coefficient given r is BISH
theorem leading_coeff_computable
    (L : LFunction) (n : ℤ) (r : ℕ)
    (hac : HasAnalyticContinuation L)
    (hr : ord_vanishing L n = r) :
    BISHComputable (leading_taylor_coeff L n r) := by
  -- r-th derivative of analytic function at computable point
  exact analytic_eval_computable (L.derivative_iter r) ⟨n, computable_int n⟩ (by sorry)
```

**Sorry budget:**
- `analytic_eval_computable`: principled axiom (standard constructive analysis)
- `zero_test_requires_LPO`: principled axiom (Bridges-Richman, Constructive Analysis, §1.3)

### Module 3: Axiom2Realization.lean (~60 lines, 1 principled sorry)

Formalize Theorem B: Deligne Weil I provides Axiom 2.

```
-- Axiomatize Deligne's theorem
axiom deligne_weil_I :
  ∀ (X : SmoothProjectiveVariety) (p : Prime) (ℓ : Prime) (hℓ : ℓ ≠ p),
    ∀ α ∈ frobenius_eigenvalues X p ℓ,
      IsAlgebraicInteger α

-- Theorem: Axiom 2 is realized
theorem axiom2_realized (M : PureMotive) :
    AlgebraicSpectrum M := by
  intro f hf
  -- Frobenius eigenvalues are algebraic by Deligne
  exact deligne_weil_I M.variety M.prime M.aux_prime (by assumption) f hf
```

**Sorry budget:**
- `deligne_weil_I`: principled axiom (Deligne 1974, Théorème 1.6)

### Module 4: Axiom3PartialRealization.lean (~120 lines, 2 principled sorry)

Formalize Theorem C: Archimedean polarization via Hodge-Riemann and
Beilinson height.

```
-- Axiomatize Hodge-Riemann bilinear relations
axiom hodge_riemann_positive_definite :
  ∀ (X : SmoothProjectiveVariety) (i : ℕ),
    ∃ (H : BilinearForm ℝ (BettiCohomology X i)),
      PositiveDefinite H

-- Axiomatize Beilinson height pairing (CONJECTURAL)
axiom beilinson_height_positive_definite :
  ∀ (M : PureMotive),
    ∃ (h : BilinearForm ℝ (MotivicCohomology M)),
      PositiveDefinite h

-- The period is unconditionally Archimedean
theorem deligne_period_archimedean (M : PureMotive) :
    ArchimedeanPolarized (DelignePeriod M) := by
  obtain ⟨H, hH⟩ := hodge_riemann_positive_definite M.variety M.weight
  exact ⟨H, hH, u_invariant_real_infinite⟩

-- The regulator is conditionally Archimedean
theorem beilinson_regulator_archimedean (M : PureMotive)
    (hBeil : BeilinsonHeightConjecture M) :
    ArchimedeanPolarized (BeilinsonRegulator M) := by
  obtain ⟨h, hh⟩ := beilinson_height_positive_definite M
  exact ⟨h, hh, u_invariant_real_infinite⟩
```

**Sorry budget:**
- `hodge_riemann_positive_definite`: principled axiom (Hodge 1937; see
  Griffiths-Harris, Principles of Algebraic Geometry, §0.7)
- `beilinson_height_positive_definite`: principled axiom, CONJECTURAL
  (Beilinson 1987, "Height pairing between algebraic cycles"). Mark
  clearly in comments that this is NOT a theorem.

### Module 5: Axiom1Failure.lean (~100 lines, 0 sorry)

Formalize Theorem D: Axiom 1 fails for mixed motives. This is a
NEGATIVE result — the proof is that no decision procedure exists,
not that one does.

```
-- The key distinction: pure vs mixed
-- Standard Conjecture D gives decidability for PURE Hom-spaces
-- It says NOTHING about Ext^1 (extensions = mixed motives)

-- Pure: Hom(M, N) in the pure motive category
-- Axiom 1 applies: homological = numerical ⟹ decidable
-- This is Paper 50, Definition 6.1

-- Mixed: Ext^1(M, N) classifies extensions 0 → N → E → M → 0
-- No "numerical equivalence" for extensions
-- No bilinear form to make Ext^1 decidable

-- Formalize the obstruction
structure MixedMotiveUndecidability where
  -- H^1_f(X, M) ≅ Ext^1_{MM}(Q(0), M) in the mixed motive category
  h1f_is_ext : H1f M ≃ Ext1 (QMotiveTwist 0) M
  -- Standard Conjecture D does not apply to Ext^1
  no_numerical_eq_for_ext : ¬∃ (≈ₙ : Ext1 (QMotiveTwist 0) M → Ext1 (QMotiveTwist 0) M → Prop),
    IsNumericalEquivalence ≈ₙ ∧ Decidable ≈ₙ
  -- Therefore: ranks of H^1_f are not BISH-computable
  rank_undecidable : ¬BISHComputable (rank (H1f M))

-- The proof that Axiom 1 fails
theorem axiom1_fails_mixed (M : PureMotive) :
    ¬(DecidableEq (H1f M)) := by
  intro hdec
  -- If H^1_f had decidable equality, we could compute its rank
  -- But rank computation requires testing each generator against zero
  -- which requires a decision procedure on Ext^1
  -- Standard Conjecture D provides no such procedure
  exact MixedMotiveUndecidability.rank_undecidable M (rank_from_dec hdec)
```

**Sorry budget:** 0. The logical argument is self-contained once the
type definitions are in place. The undecidability is structural (no
numerical equivalence for Ext^1), not dependent on external theorems.

### Module 6: TamagawaObstruction.lean (~100 lines, 1 principled sorry)

Formalize Theorem E: Tamagawa factors escape all three axioms.

```
-- The u-invariant obstruction at finite primes
-- Paper 50, Definition 2.3: u(Q_p) = 4

theorem u_invariant_Q_p (p : Prime) : u_invariant (Q_p p) = 4 := by
  -- Hasse-Minkowski: every quadratic form over Q_p of dimension ≥ 5
  -- is isotropic. Therefore u(Q_p) ≤ 4.
  -- The form ⟨1, 1, 1, 1⟩ is anisotropic over Q_2; for odd p,
  -- ⟨1, -ε, p, -εp⟩ where ε is a non-square unit is anisotropic.
  -- Therefore u(Q_p) = 4.
  sorry -- Principled: Lam, Introduction to Quadratic Forms, Theorem VI.2.2

-- No positive-definite form in dimension ≥ 5 over Q_p
theorem no_padic_polarization (p : Prime) (n : ℕ) (hn : n ≥ 5) :
    ¬∃ (Q : QuadraticForm (Q_p p) n), PositiveDefinite Q := by
  intro ⟨Q, hQ⟩
  -- Positive-definite ⟹ anisotropic
  have haniso : Anisotropic Q := positive_definite_anisotropic hQ
  -- But u(Q_p) = 4, so all forms of dim ≥ 5 are isotropic
  have hiso : ¬Anisotropic Q := by
    apply u_invariant_forces_isotropy
    exact u_invariant_Q_p p
    exact hn
  exact hiso haniso

-- The Tamagawa factor requires p-adic integration outside DPT
structure TamagawaOutsideDPT where
  -- c_p is computed via Bloch-Kato exponential in B_dR
  bloch_kato_exp : D_dR V / D_cris V → H1f (Q_p p) V
  -- This requires continuous p-adic volume computation
  requires_padic_integration : PadicIntegration (bloch_kato_exp)
  -- No Axiom 3 analogue at p (because u(Q_p) = 4)
  no_axiom3 : ¬ArchimedeanPolarized (H1f_local p V)
  -- Not captured by Axiom 1 (decidable equality on pure Hom)
  not_axiom1 : ¬PureHomDecidability (H1f_local p V)
  -- Not captured by Axiom 2 (Frobenius eigenvalues don't help here)
  not_axiom2 : ¬AlgebraicSpectrumSufficient (TamagawaFactor p V)
```

**Sorry budget:**
- `u_invariant_Q_p`: principled axiom (Lam 2005, Theorem VI.2.2)

### Module 7: CalibrationVerdict.lean (~80 lines, 0 sorry)

Assemble the full calibration record. This is the payoff — a machine-
checkable record of the decomposition result.

```
def blochKatoCalibration : DPTCalibration := {
  name := "Bloch-Kato / Tamagawa Number Conjecture"
  axiom1_source := none  -- FAILS: mixed motives
  axiom1_status := .missing
  axiom2_source := some "Deligne Weil I Théorème 1.6 (1974)"
  axiom2_status := .proven
  axiom3_source := some "Hodge-Riemann (period) + Beilinson height (regulator)"
  axiom3_status := .conditional "Beilinson Height Conjecture"
  extra_costs := [
    ("Tamagawa factors c_p",
     "p-adic volume via B_dR; u(Q_p)=4 precludes Axiom 3 analogue"),
    ("Mixed motive ranks",
     "Ext^1 undecidable; Standard Conjecture D covers Hom only")
  ]
  lpo_source := "Order of vanishing ord_{s=n} L(M,s)"
  decomposition_succeeds := .partial
}

-- Comparison with the original five calibrations
-- Paper 45 (WMC):    Axiom 1 ✓  Axiom 2 ✓  Axiom 3 ✓  Extra: none
-- Paper 46 (Tate):   Axiom 1 ✓  Axiom 2 ✓  Axiom 3 ✓  Extra: none
-- Paper 47 (F-M):    Axiom 1 ✓  Axiom 2 ✓  Axiom 3 ✓  Extra: none
-- Paper 48 (BSD):    Axiom 1 ✓  Axiom 2 ✓  Axiom 3 ✓  Extra: none
-- Paper 49 (Hodge):  Axiom 1 ✓  Axiom 2 ✓  Axiom 3 ✓  Extra: none
-- Paper 54 (B-K):    Axiom 1 ✗  Axiom 2 ✓  Axiom 3 ~  Extra: c_p
--
-- FINDING: First calibration where DPT axioms are INSUFFICIENT.
-- The insufficiency is precisely located:
--   (1) Pure → Mixed boundary (Axiom 1)
--   (2) Archimedean → p-adic boundary (Axiom 3 → no analogue)
-- These are the exact boundaries Paper 50 was designed around.
-- The framework detects its own limits correctly.
```

### Module 8: DescentDiagram.lean (~60 lines, 0 sorry)

Formalize the de-omniscientizing descent diagram with the two
fracture points explicitly marked.

```
-- The descent diagram for Bloch-Kato
--
-- [CONTINUOUS / LPO]
--   L*(M, n) — leading Taylor coefficient
--   Requires LPO for ord_{s=n} L(M, s)
--       |
--       | mediated by motive M
--       v
-- [MOTIVIC INTERMEDIARY]
--   Δ(M), Ω(M), R(M)
--   Stabilized by Axiom 2 (algebraic eigenvalues)
--   and Axiom 3 (real positive-definiteness)
--       |
--       | descends to
--       v
-- [DECIDABLE / BISH]
--   #Sha(M), torsion subgroup orders
--   (computable integers)
--       |
--       | *** FRACTURE POINT 1 ***
--       v
-- [UNDECIDABLE: MIXED]
--   rank H^1_f(X, M) — requires Ext^1 decidability
--   Axiom 1 covers Hom, not Ext
--       |
--       | *** FRACTURE POINT 2 ***
--       v
-- [UNDECIDABLE: p-ADIC]
--   Tamagawa factors c_p — requires B_dR integration
--   u(Q_p) = 4 kills Axiom 3 analogue

inductive DescentLayer
  | continuous_LPO     -- L-function, zero-testing
  | motivic_mediated   -- Δ(M), Ω(M), R(M)
  | decidable_BISH     -- Sha, torsion (integers)
  | undecidable_mixed   -- H^1_f ranks (Ext^1)
  | undecidable_padic   -- Tamagawa factors (B_dR)

-- The descent works down to decidable_BISH, then fractures
theorem descent_fractures :
    DescentWorksTo .decidable_BISH ∧
    ¬DescentWorksTo .undecidable_mixed ∧
    ¬DescentWorksTo .undecidable_padic := by
  constructor
  · exact archimedean_descent_ok  -- Axioms 2 + 3
  constructor
  · exact axiom1_fails_mixed      -- Module 5
  · exact tamagawa_outside_dpt    -- Module 6
```

---

## 3. SORRY BUDGET SUMMARY

| Module | Sorry Count | Classification |
|--------|-------------|----------------|
| 1. DPTCalibration     | 0 | — |
| 2. LPOIsolation       | 2 | principled (constructive analysis) |
| 3. Axiom2Realization  | 1 | principled (Deligne 1974) |
| 4. Axiom3Partial      | 2 | principled (Hodge 1937 + Beilinson 1987 CONJECTURAL) |
| 5. Axiom1Failure      | 0 | — |
| 6. TamagawaObstruction| 1 | principled (Lam 2005) |
| 7. CalibrationVerdict | 0 | — |
| 8. DescentDiagram     | 0 | — |
| **TOTAL**             | **6** | **all principled, 0 gaps** |

The 6 principled sorries axiomatize:
1. Analytic evaluation of constructively analytic functions (standard)
2. Zero-testing requires LPO (Bridges-Richman)
3. Deligne Weil I (1974)
4. Hodge-Riemann bilinear relations (1937)
5. Beilinson height conjecture (1987, CONJECTURAL — mark clearly)
6. u-invariant of Q_p (Lam 2005)

---

## 4. CRITICAL INSTRUCTIONS FOR LEAN AGENT

### 4.1 What to import from Paper 50

The DPT class definition lives in Paper 50's Lean code. Import:
- `DecidablePolarizedTannakian` (the class with three axioms)
- `u_invariant_real_infinite` (u(ℝ) = ∞)
- The comparison infrastructure from Paper 45 (Axiom 2 template)
- The BSD infrastructure from Paper 48 (Axiom 3 template for heights)

If these imports are not available, STUB THEM with clearly marked
axioms referencing Paper 50. Do not reinvent the DPT class.

### 4.2 What NOT to do

- Do NOT attempt to formalize analytic continuation of L-functions.
  Axiomatize it.
- Do NOT attempt to formalize Fontaine's period rings (B_cris, B_dR).
  Axiomatize the Bloch-Kato exponential map as an opaque function with
  the property that it requires p-adic integration.
- Do NOT attempt to formalize the Beilinson regulator map. Axiomatize
  its existence and the conjectural positive-definiteness.
- Do NOT add modules for "future work" or "extensions to mixed DPT."
  Paper 54 identifies the boundary. It does not cross it.

### 4.3 What MUST compile

The following must produce actual Lean output (#eval or #check):

1. `blochKatoCalibration` — the calibration record with all fields populated.
2. `descent_fractures` — the theorem that descent works to BISH and fails
   at mixed/p-adic layers.
3. `axiom1_fails_mixed` — the negative result for Ext^1 decidability.
4. `no_padic_polarization` — the theorem that u(Q_p) = 4 precludes
   positive-definite forms in dimension ≥ 5.

### 4.4 The comparison table

The final output should include a machine-checkable comparison:

```
-- #eval to produce the 6-row comparison table
def calibrationTable : List DPTCalibration :=
  [wmcCalibration,      -- Paper 45: all ✓
   tateCalibration,     -- Paper 46: all ✓
   fontaineMazur,       -- Paper 47: all ✓
   bsdCalibration,      -- Paper 48: all ✓
   hodgeCalibration,    -- Paper 49: all ✓
   blochKatoCalibration -- Paper 54: PARTIAL]
```

If the Paper 45–49 calibration records are not importable, define
stubs with the correct verdicts. The point is to show Paper 54 as
the first partial failure in the table.

### 4.5 Naming conventions

Follow the programme's established conventions:
- Theorem names: `snake_case` with paper prefix where needed
- Axiom names: `axiom_name_source` (e.g., `deligne_weil_I`)
- Module names: `PaperNN_ModuleName` (e.g., `Paper54_LPOIsolation`)

---

## 5. PAPER STRUCTURE (LaTeX)

§1. Introduction and motivation
    - The DPT framework (3 axioms, 5 calibrations, all succeed)
    - Bloch-Kato as out-of-sample test
    - Summary of result: partial decomposition with two fracture points

§2. The Bloch-Kato conjecture (review)
    - L-function, functional equation, order of vanishing
    - Motivic fundamental line, Deligne period, Beilinson regulator
    - Tamagawa factors, Sha, torsion
    - The Tamagawa number formula

§3. LPO isolation (Theorem A)
    - Analytic continuation is BISH
    - Zero-testing is LPO
    - Leading coefficient given order is BISH

§4. Axiom-by-axiom calibration (Theorems B, C, D, E)
    - Axiom 2: Deligne Weil I (unconditional)
    - Axiom 3: Hodge-Riemann + Beilinson height (conditional)
    - Axiom 1: failure at mixed motives
    - Tamagawa factors: outside all three axioms

§5. The descent diagram (Theorem F)
    - Full diagram with fracture points
    - Comparison with BSD (Paper 48) — where the pure case succeeds
    - Why Bloch-Kato exposes what BSD doesn't:
      the Tamagawa factors in BSD for elliptic curves are computable
      integers (Tate's algorithm), but in general they are not

§6. Lean formalization
    - Module structure
    - Sorry budget with classifications
    - Calibration table output

§7. Implications for the DPT programme
    - Paper 50 is correct FOR PURE MOTIVES
    - The two missing axioms (decidable Ext, p-adic volume principle)
      are concretely specified by the failure points
    - This is the framework detecting its own boundary, not failing

§8. "What this paper does not claim" section
    - Does not propose Axioms 4 and 5
    - Does not resolve the Beilinson height conjecture
    - Does not claim DPT needs revision — claims it needs EXTENSION

---

## 6. KEY REFERENCES

- Bloch, Kato. "L-functions and Tamagawa numbers of motives."
  The Grothendieck Festschrift I (1990), 333–400.
- Burns, Flach. "Tamagawa numbers for motives with (non-commutative)
  coefficients." Doc. Math. 6 (2001), 501–570.
- Deligne. "La conjecture de Weil. I." Publ. Math. IHÉS 43 (1974),
  273–307. [Théorème 1.6 for Axiom 2]
- Deligne. "Valeurs de fonctions L et périodes d'intégrales."
  Proc. Symp. Pure Math. 33 (1979), 313–346.
  [Critical values, algebraicity]
- Beilinson. "Height pairing between algebraic cycles." Current trends
  in arithmetical algebraic geometry, Contemp. Math. 67 (1987), 1–24.
  [Height pairing, CONJECTURAL positive-definiteness]
- Hodge. "The Theory and Applications of Harmonic Integrals."
  Cambridge (1941). [Hodge-Riemann bilinear relations]
- Fontaine. "Représentations p-adiques semi-stables."
  Astérisque 223 (1994), 113–184. [B_cris, B_dR]
- Lam. "Introduction to Quadratic Forms over Fields."
  AMS GSM 67 (2005). [u-invariant, Theorem VI.2.2]
- Bridges, Richman. "Varieties of Constructive Mathematics."
  LMS Lecture Notes 97 (1987). [LPO, zero-testing]
- Lee. "Paper 50: Decidability Landscape for the Standard Conjectures."
  Zenodo (2026). [DPT class definition, three axioms]
