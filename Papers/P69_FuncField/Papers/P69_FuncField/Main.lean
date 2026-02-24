/-
  Paper 69: The Logical Cost of the Archimedean Place
  Function Field Langlands is BISH

  Lean 4 formal verification of the CRM assembly.
  This file verifies the logical structure: given axiomatised CRM classifications
  of individual components, the overall classification follows by finite decision.

  Zero sorry. Every axiom has a mathematical reference.
-/

-- CRM hierarchy as a finite totally ordered type
inductive CRMLevel : Type where
  | BISH   : CRMLevel  -- Bishop's constructive mathematics
  | MP     : CRMLevel  -- Markov's Principle
  | LLPO   : CRMLevel  -- Lesser Limited Principle of Omniscience
  | WLPO   : CRMLevel  -- Weak Limited Principle of Omniscience
  | LPO    : CRMLevel  -- Limited Principle of Omniscience
  | CLASS  : CRMLevel  -- Full classical logic
  deriving DecidableEq, Repr

open CRMLevel

instance : LE CRMLevel where
  le a b := a.ctorIdx ≤ b.ctorIdx

instance : LT CRMLevel where
  lt a b := a.ctorIdx < b.ctorIdx

instance (a b : CRMLevel) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.ctorIdx ≤ b.ctorIdx))

instance (a b : CRMLevel) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.ctorIdx < b.ctorIdx))

-- Join (supremum) in the CRM lattice
def CRMLevel.join (a b : CRMLevel) : CRMLevel :=
  if a.ctorIdx ≥ b.ctorIdx then a else b

-- ============================================================
-- SECTION 1: Components of Laurent Lafforgue's proof (GL_n)
-- ============================================================

/-- Compactification of shtuka moduli: algebraic intersection theory
    on Deligne-Mumford stacks over F_q.
    Reference: L. Lafforgue, Invent. Math. 147 (2002), Chapters I-IV. -/
axiom laurent_compactification : CRMLevel
axiom laurent_compactification_eq : laurent_compactification = BISH

/-- ℓ-adic étale cohomology of compactified shtuka stacks:
    finite-dimensional Q_ℓ-vector spaces, Frobenius eigenvalues are
    algebraic (Weil numbers) by Deligne's Weil II.
    Reference: Deligne, Publ. Math. IHÉS 52 (1980). -/
axiom laurent_etale_cohomology : CRMLevel
axiom laurent_etale_cohomology_eq : laurent_etale_cohomology = BISH

/-- Grothendieck-Lefschetz trace formula: finite alternating sum of
    traces of Frobenius on finite-dimensional vector spaces.
    Evaluates as a finite identity of algebraic numbers.
    Reference: SGA 4½, Grothendieck. -/
axiom grothendieck_lefschetz : CRMLevel
axiom grothendieck_lefschetz_eq : grothendieck_lefschetz = BISH

/-- Function field Arthur-Selberg trace formula: continuous spectrum
    exists but is parametrised by compact algebraic torus with
    rational Plancherel measure. Contour integral reduces to
    finite sum of algebraic residues.
    Reference: L. Lafforgue, Invent. Math. 147 (2002), §V. -/
axiom funcfield_arthur_selberg : CRMLevel
axiom funcfield_arthur_selberg_eq : funcfield_arthur_selberg = BISH

/-- Isolation of cuspidal component: Harder's theorem gives
    finite-dimensional space of cusp forms at fixed level.
    Decomposition is finite linear algebra.
    Reference: Harder, Ann. Math. 100 (1974). -/
axiom laurent_cuspidal_isolation : CRMLevel
axiom laurent_cuspidal_isolation_eq : laurent_cuspidal_isolation = BISH

-- ============================================================
-- SECTION 2: Components of Vincent Lafforgue's proof (general G)
-- ============================================================

/-- G-shtuka cohomology: Deligne-Mumford stacks over C^I,
    finite-dimensional ℓ-adic cohomology.
    Reference: V. Lafforgue, JAMS 31 (2018), §§3-5. -/
axiom vincent_shtuka_cohomology : CRMLevel
axiom vincent_shtuka_cohomology_eq : vincent_shtuka_cohomology = BISH

/-- Geometric Satake equivalence: tensor equivalence between
    perverse sheaves on affine Grassmannian and Rep(Ĝ).
    Constructed via intersection cohomology over F_q.
    Reference: Mirković-Vilonen, Ann. Math. 166 (2007). -/
axiom geometric_satake : CRMLevel
axiom geometric_satake_eq : geometric_satake = BISH

/-- Excursion operators and algebra B: commutative algebra acting
    on finite-dimensional C_cusp(K). Image is Artinian,
    MaxSpec finite and computable.
    Reference: V. Lafforgue, JAMS 31 (2018), §§10-11. -/
axiom excursion_algebra : CRMLevel
axiom excursion_algebra_eq : excursion_algebra = BISH

/-- Characters to Langlands parameters: pseudo-characters
    (Taylor-Rouquier) + Chevalley restriction theorem.
    Over function fields, effective Chebotarev from Weil conjectures.
    Reference: V. Lafforgue, JAMS 31 (2018), §12;
    Taylor, Duke Math. J. 63 (1991). -/
axiom chars_to_parameters : CRMLevel
axiom chars_to_parameters_eq : chars_to_parameters = BISH

/-- Effective Chebotarev over function fields: follows from
    Weil conjectures. Zeta function is rational, RH for curves
    gives polynomial bounds.
    Reference: Weil (1948); see also Serre, Annals 1965. -/
axiom funcfield_chebotarev : CRMLevel
axiom funcfield_chebotarev_eq : funcfield_chebotarev = BISH

-- ============================================================
-- SECTION 3: Assembly theorems
-- ============================================================

/-- Laurent Lafforgue's proof for GL_n is the join of its five components. -/
noncomputable def laurent_proof : CRMLevel :=
  [laurent_compactification,
   laurent_etale_cohomology,
   grothendieck_lefschetz,
   funcfield_arthur_selberg,
   laurent_cuspidal_isolation].foldl CRMLevel.join BISH

theorem laurent_is_BISH : laurent_proof = BISH := by
  unfold laurent_proof CRMLevel.join
  rw [laurent_compactification_eq, laurent_etale_cohomology_eq,
      grothendieck_lefschetz_eq, funcfield_arthur_selberg_eq,
      laurent_cuspidal_isolation_eq]
  decide

/-- Vincent Lafforgue's proof for general G is the join of its five components. -/
noncomputable def vincent_proof : CRMLevel :=
  [vincent_shtuka_cohomology,
   geometric_satake,
   excursion_algebra,
   chars_to_parameters,
   funcfield_chebotarev].foldl CRMLevel.join BISH

theorem vincent_is_BISH : vincent_proof = BISH := by
  unfold vincent_proof CRMLevel.join
  rw [vincent_shtuka_cohomology_eq, geometric_satake_eq,
      excursion_algebra_eq, chars_to_parameters_eq,
      funcfield_chebotarev_eq]
  decide

-- ============================================================
-- SECTION 4: Comparison with number field case (from Paper 68)
-- ============================================================

/-- Number field Arthur-Selberg trace formula at weight 1:
    L² spectral decomposition with transcendental Archimedean integrands.
    Reference: Paper 68, §§6-7. -/
axiom numfield_arthur_selberg : CRMLevel
axiom numfield_arthur_selberg_eq : numfield_arthur_selberg = WLPO

/-- Number field Langlands-Tunnell (Wiles's Stage 1):
    base change via Arthur-Selberg trace formula.
    Reference: Paper 68, §6. -/
axiom langlands_tunnell : CRMLevel
axiom langlands_tunnell_eq : langlands_tunnell = WLPO

/-- Number field cusp form space at weight 1:
    no algebraic dimension formula, trace formula required.
    Reference: Paper 68, §11.4. -/
axiom numfield_weight1_space : CRMLevel
axiom numfield_weight1_space_eq : numfield_weight1_space = WLPO

/-- Taylor-Wiles patching (any number field): BISH.
    Reference: Paper 68, §§8-9; Brochard, Compositio 153 (2017). -/
axiom taylor_wiles : CRMLevel
axiom taylor_wiles_eq : taylor_wiles = BISH

-- The logical cost of R: every WLPO component over number fields
-- has a BISH counterpart over function fields

theorem archimedean_trace_formula_descent :
    numfield_arthur_selberg = WLPO ∧ funcfield_arthur_selberg = BISH := by
  exact ⟨numfield_arthur_selberg_eq, funcfield_arthur_selberg_eq⟩

theorem archimedean_base_case_descent :
    langlands_tunnell = WLPO ∧ excursion_algebra = BISH := by
  exact ⟨langlands_tunnell_eq, excursion_algebra_eq⟩

theorem archimedean_cusp_space_descent :
    numfield_weight1_space = WLPO ∧ laurent_cuspidal_isolation = BISH := by
  exact ⟨numfield_weight1_space_eq, laurent_cuspidal_isolation_eq⟩

-- Patching is BISH in both settings
theorem patching_invariant :
    taylor_wiles = BISH := taylor_wiles_eq

-- ============================================================
-- SECTION 5: The main theorem
-- ============================================================

/-- Paper 69, Theorem 1.1: The function field Langlands correspondence is BISH.
    Both Laurent (GL_n) and Vincent (general G) proofs classify at BISH. -/
theorem funcfield_langlands_is_BISH :
    laurent_proof = BISH ∧ vincent_proof = BISH :=
  ⟨laurent_is_BISH, vincent_is_BISH⟩

/-- Paper 69, Theorem C: Every WLPO component over number fields has a
    BISH counterpart over function fields; the Archimedean place is the source.

    Proof structure: every component that costs WLPO over number fields
    (trace formula, base case, cusp form space) has a BISH counterpart
    over function fields. The structural shift in each case is the
    replacement of the Archimedean local field R by non-Archimedean F_q((t)). -/
theorem logical_cost_of_R :
    -- Function field: everything is BISH
    laurent_proof = BISH
    ∧ vincent_proof = BISH
    -- Number field WLPO components have BISH function field counterparts
    ∧ (numfield_arthur_selberg = WLPO ∧ funcfield_arthur_selberg = BISH)
    ∧ (langlands_tunnell = WLPO ∧ excursion_algebra = BISH)
    ∧ (numfield_weight1_space = WLPO ∧ laurent_cuspidal_isolation = BISH) :=
  ⟨laurent_is_BISH,
   vincent_is_BISH,
   archimedean_trace_formula_descent,
   archimedean_base_case_descent,
   archimedean_cusp_space_descent⟩

-- ============================================================
-- Verification: all theorems type-check
-- ============================================================

#check funcfield_langlands_is_BISH
#check logical_cost_of_R
#check laurent_is_BISH
#check vincent_is_BISH
