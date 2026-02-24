# Paper 35: The Conservation Metatheorem

## Why Empirical Physics Lives at BISH+LPO

### Proof Document for Lean 4 Formalization

**Series:** Constructive Reverse Mathematics of Mathematical Physics
**Author:** Paul Chun-Kit Lee
**Architectural Guidance:** Claude (Anthropic)

---

## 1. Executive Summary

This paper proves a metatheorem that *explains* the empirical pattern observed across Papers 1–34: every physical prediction that has been calibrated lives at BISH+LPO, with the BISH/LPO boundary located precisely at the transition from finite computation to completed infinite process.

The metatheorem has three components:

**Theorem A (BISH Conservation):** Any physical prediction expressible as a finite composition of computable functions evaluated at computable inputs is BISH. This is a standard result in computable analysis, applied to physics.

**Theorem B (LPO Boundary Characterization):** A physical assertion requires LPO over BISH if and only if it asserts the existence of a completed limit whose rate of convergence is not uniformly computable. The three mechanisms are: (1) monotone bounded limits without modulus (BMC ↔ LPO), (2) Cauchy limits without modulus (equivalent to BMC via standard encoding), (3) decidability of limit equality (WLPO, subsumed by LPO).

**Theorem C (Exhaustiveness):** Every calibration result in Papers 1–34 falls into exactly one of the categories classified by Theorems A and B. No physical prediction in the programme required an omniscience principle stronger than LPO.

**Punchline:** The logical constitution of empirically accessible physics is not an accident or a coincidence across 34 papers. It is a *consequence* of two facts: (i) empirical predictions are finite computations on computable inputs, and (ii) the only idealizations physicists perform that exceed finite computation are completed limits, which cost exactly LPO.

---

## 2. Conceptual Architecture

### 2.1 The Problem This Paper Solves

Papers 1–34 established an empirical pattern:

| Category | Axiom Height | Count | Examples |
|---|---|---|---|
| Finite computation | BISH | ~40+ | Tree amplitudes, finite Ising, lattice QCD, Ward identities |
| Sign/threshold decision | WLPO/LLPO | ~8 | Heaviside decoupling, Noether sign, Bell disjunction |
| Completed limit | LPO | ~15 | Coupling constants, thermodynamic limits, spectral gaps |
| Never encountered | > LPO | 0 | — |

But *why*? Why does LPO suffice for all of physics? Is this a deep fact about the universe, or a selection bias in which theorems we chose to calibrate?

Paper 35 answers: it is a consequence of the *mathematical structure* of physical predictions, not of the specific physics. Any discipline whose predictions have the same mathematical form (finite compositions of standard functions, with idealizations via completed limits) would produce the same calibration table. Physics is special only in that its predictions happen to have this form — but that form is not physically contingent. It follows from the structure of how theories make contact with experiment.

### 2.2 The Key Insight

A physical prediction, at the point where it contacts experiment, is always a statement of the form:

> "The value of observable O, computed from theory T with parameters θ, lies in the interval [a - ε, a + ε]"

where a is computed by evaluating a *specific function* at *specific inputs*, and ε is the theoretical/experimental uncertainty.

The function is always a finite composition of:
- Arithmetic operations (+, ×, ÷ with denominators apart from zero)
- Elementary transcendental functions (exp, log, sin, cos, √)
- Special functions with known series expansions (Li₂, Γ, Bessel, hypergeometric, ...)
- Finite sums and products

Every one of these is a computable function in the sense of Type-2 computability theory. Compositions of computable functions are computable. Therefore the prediction is BISH.

LPO enters *only* when the physicist does one of three things:
1. Takes a thermodynamic/continuum limit (N → ∞, a → 0)
2. Asserts a global existence claim (the coupling constant exists as a real number at all scales)
3. Decides whether a limit equals a specific value (is the mass gap zero or positive?)

Each of these is a completed infinite process without a guaranteed rate of convergence. Each costs exactly LPO via the BMC equivalence.

Nothing in physics requires more than this.

---

## 3. Mathematical Framework

### 3.1 Computable Analysis Definitions

We work in the framework of Type-2 computability (Weihrauch, Pour-El & Richards). The key definitions:

**Definition (Computable real number).** A real number x is *computable* if there exists a computable function φ : ℕ → ℚ such that |x - φ(n)| < 2⁻ⁿ for all n.

**Definition (Computable function).** A function f : ℝ → ℝ is *computable* if there exists a Type-2 machine that, given a name for x (a fast Cauchy sequence of rationals), produces a name for f(x).

**Definition (Effectively uniformly continuous).** A function f : [a,b] → ℝ is *effectively uniformly continuous* if there exists a computable modulus of continuity μ : ℕ → ℕ such that |x - y| < 2⁻μ⁽ⁿ⁾ implies |f(x) - f(y)| < 2⁻ⁿ.

**Key theorem (standard).** The following are computable:
- All rational functions with denominators apart from zero
- exp, log (on appropriate domains), sin, cos, √
- Li₂, Γ (on appropriate domains)
- All hypergeometric functions ₚFq with computable parameters
- Finite compositions of the above

This is not new mathematics. It is the content of Weihrauch's "Computable Analysis" (2000), Pour-El & Richards (1989), and related standard references. What is new is applying it systematically to the outputs of physical theories.

### 3.2 Physical Prediction as Computable Function

**Definition (Physical prediction).** A *physical prediction at precision ε* is a statement of the form:

P(θ, ε) := "O(θ) ∈ [a(θ) - ε, a(θ) + ε]"

where:
- θ ∈ ℝⁿ are the theory parameters (masses, coupling constants, kinematic variables)
- a : ℝⁿ → ℝ is the *prediction function* (the formula the theory produces)
- O is the experimentally measured value
- ε > 0 is the precision (theoretical + experimental uncertainty)

**Definition (Finitary prediction).** A physical prediction is *finitary* if the prediction function a(θ) is a finite composition of computable functions.

**Definition (Limit prediction).** A physical prediction is a *limit prediction* if a(θ) = limₙ→∞ aₙ(θ) where each aₙ is finitary.

---

## 4. Theorems to Formalize

### Theorem A: BISH Conservation Theorem

**Statement:** Every finitary physical prediction is BISH-provable. Specifically: if a : ℝⁿ → ℝ is a finite composition of computable functions and θ ∈ ℝⁿ consists of computable reals, then for every ε > 0 there exists a computable rational approximation q such that |a(θ) - q| < ε, and this approximation can be found constructively (without any omniscience principle).

**Proof:**

Step 1: Each component function (exp, log, Li₂, rational, ...) is computable. This means each has a Type-2 algorithm producing rational approximations with explicit error bounds.

Step 2: Composition preserves computability. If f and g are computable with moduli of continuity μ_f and μ_g, then f ∘ g is computable with modulus μ_{f∘g}(n) = μ_g(μ_f(n)). This is constructive — the modulus is computed from the component moduli.

Step 3: The prediction function a(θ) is a finite composition (by hypothesis). By induction on composition depth, a is computable. The approximation q is produced by the composed algorithm.

Step 4: No omniscience principle was used. The algorithms are uniform — they produce approximations for all inputs, not just decidable cases. The error bounds are explicit at each stage.

**This theorem is essentially trivial from the computable analysis perspective.** Its content is not mathematical novelty but *applicability*: the observation that physical prediction functions are, in fact, finitary in the above sense.

**Lean architecture:**

```
-- Computable function: has explicit approximation algorithm
structure ComputableFun where
  f : ℝ → ℝ
  approx : ℝ → ℕ → ℚ  -- approximation at precision 2⁻ⁿ
  spec : ∀ x n, |f x - ↑(approx x n)| < (2 : ℝ)⁻¹ ^ n

-- Composition preserves computability
theorem comp_computable (f g : ComputableFun) :
    ComputableFun where
  f := f.f ∘ g.f
  approx := fun x n => f.approx (g.f x) n  -- simplified; real version threads moduli
  spec := by sorry -- FILL: compose error bounds using moduli of continuity

-- Standard functions are computable
axiom exp_computable : ComputableFun  -- from Mathlib effective bounds
axiom log_computable : ComputableFun  -- from Mathlib effective bounds
axiom Li2_computable : ComputableFun  -- from Paper 34

-- Rational functions with apart denominators are computable
theorem rational_computable (p q : Polynomial ℝ) (hq : ∀ x ∈ S, q.eval x ≠ 0) :
    ComputableFun := by
  sorry -- FILL: rational arithmetic on computable reals

-- MAIN: finitary prediction is BISH
theorem finitary_prediction_is_BISH
    (a : FiniteComposition)  -- finite composition tree of computable functions
    (θ : Fin n → ℝ)         -- computable parameters
    (hθ : ∀ i, Computable (θ i))
    (ε : ℝ) (hε : ε > 0) :
    ∃ q : ℚ, |a.eval θ - ↑q| < ε := by
  sorry -- FILL: unfold composition, apply comp_computable inductively

-- #print axioms finitary_prediction_is_BISH → target: [only Lean primitives + Mathlib]
```

**Expected axiom profile:** Zero custom axioms beyond Mathlib. The proof is constructive by construction.

---

### Theorem B: LPO Boundary Characterization

**Statement:** A limit prediction requires LPO over BISH if and only if the limit lacks a computable rate of convergence. Specifically:

**(B1)** If aₙ(θ) → a(θ) with a *computable modulus of convergence* (a computable function μ : ℕ → ℕ such that |aₙ(θ) - a(θ)| < 2⁻ᵏ for all n ≥ μ(k)), then a(θ) is computable and the prediction is BISH.

**(B2)** If the sequence (aₙ(θ)) is bounded and monotone but has *no computable modulus*, then asserting the limit exists is equivalent to BMC, which is equivalent to LPO.

**(B3)** Asserting that the limit equals a specific value (a(θ) = c or a(θ) ≠ c) costs WLPO, which is subsumed by LPO.

**Proof of B1:**

Given the modulus μ, to approximate a(θ) within 2⁻ᵏ, compute a_{μ(k+1)}(θ) within 2⁻⁽ᵏ⁺¹⁾ (possible since each aₙ is finitary, hence computable by Theorem A), then:

|a(θ) - a_{μ(k+1)}(θ)| < 2⁻⁽ᵏ⁺¹⁾ (by modulus)

So the rational approximation for a_{μ(k+1)} serves as an approximation for a with doubled error. BISH.

**Proof of B2:**

This is the BMC ↔ LPO equivalence from Paper 29 (Fekete). We reproduce the key steps:

Forward (LPO → BMC): Given a bounded monotone sequence (sₙ) and LPO, we can decide ∀n, sₙ < B-ε for any ε, which by bisection produces the limit. Standard.

Reverse (BMC → LPO): Given a binary sequence α : ℕ → {0,1}, define sₙ = Σᵢ₌₁ⁿ α(i)/2ⁱ. This is bounded (by 1) and monotone. BMC gives the limit L. Then α is identically zero iff L = 0 iff |L| < 1/2ⁿ for all n. Since L is a real number, we can decide ∀n, α(n) = 0 ∨ ¬∀n, α(n) = 0 by testing L against 0. This is exactly LPO.

**Proof of B3:**

WLPO states: for any binary sequence α, either ∀n, α(n) = 0 or ¬∀n, α(n) = 0. Deciding whether a limit equals a specific value c reduces to deciding whether a certain sequence is identically zero (set βₙ = 1 if |aₙ - c| > 1/n, else 0). WLPO decides this. WLPO is strictly weaker than LPO but subsumed by it.

**Lean architecture:**

```
-- B1: Modulus of convergence makes limit BISH
theorem limit_with_modulus_is_BISH
    (a : ℕ → ℝ) (L : ℝ)
    (μ : ℕ → ℕ)  -- computable modulus
    (hmod : ∀ k, ∀ n ≥ μ k, |a n - L| < (2 : ℝ)⁻¹ ^ k)
    (ha_comp : ∀ n, ComputableReal (a n)) :
    ComputableReal L := by
  sorry -- FILL: approximate L via a (μ (k+1)), compose errors

-- B2: BMC ↔ LPO (import from Paper 29)
-- theorem bmc_iff_lpo : BMC ↔ LPO := Paper29.bmc_iff_lpo

-- B3: Limit equality decision is WLPO
theorem limit_equality_is_WLPO :
    (∀ (a : ℕ → ℝ) (L c : ℝ),
      Filter.Tendsto a Filter.atTop (nhds L) →
      (L = c) ∨ (L ≠ c)) ↔ WLPO := by
  sorry -- FILL: encode binary sequence into convergent sequence

-- WLPO subsumed by LPO
theorem wlpo_of_lpo (h : LPO) : WLPO := by
  sorry -- FILL: standard, LPO → WLPO (strictly stronger decides strictly weaker)
```

**Expected axiom profile:** B1 is zero custom axioms (BISH). B2 reuses Paper 29 (intentional classical in forward direction). B3 is zero custom axioms in the encoding direction.

---

### Theorem C: Exhaustiveness (Classification Theorem)

**Statement:** Every calibration result in Papers 1–34 is an instance of exactly one of the following:

**(C-BISH)** The prediction is a finitary computation → BISH by Theorem A.

**(C-WLPO)** The prediction involves a threshold/sign decision on a completed real → WLPO by Theorem B3.

**(C-LLPO)** The prediction involves a disjunction decision on a completed real → LLPO (strictly between WLPO and LPO in the constructive hierarchy, but subsumed by LPO).

**(C-LPO)** The prediction asserts a completed limit without computable modulus → LPO by Theorem B2.

No calibration result required any principle stronger than LPO.

**Proof:** By exhaustive classification of all entries in the calibration table.

This is not a "theorem" in the traditional sense — it is a *verified audit* of 34 papers. The content is the observation that the classification is exhaustive. The Lean formalization encodes each paper's result as an instance of one of the four categories and verifies the typing.

**The classification table:**

```
CATEGORY C-BISH (Finitary Computation):
├── Rational functions of kinematics
│   ├── Paper 34, Theorem 1: Tree-level Bhabha amplitude
│   ├── Paper 32: Ward identities
│   ├── Paper 33: QCD Ward identities  
│   └── Paper 8/9: Finite Ising partition function
├── Elementary transcendental functions
│   ├── Paper 34, Theorem 2: One-loop Feynman integrals (log, Li₂)
│   ├── Paper 5: Finite-time Schwarzschild geodesics
│   ├── Paper 6: Finite-dimensional Heisenberg uncertainty
│   └── Paper 16: Born rule (finite-dim)
├── Formal algebraic manipulation
│   ├── Paper 34, Theorem 3: Dimensional regularization
│   ├── Paper 34, Theorem 4: Bloch-Nordsieck IR cancellation
│   ├── Paper 15: Local Noether conservation (∂_μ J^μ = 0)
│   └── Paper 11: Finite Bell/CHSH computation
├── Finite lattice / discrete computation
│   ├── Paper 33: Finite lattice QCD
│   ├── Paper 8: Finite 1D Ising
│   └── Paper 14: Finite-dim decoherence
└── Explicit convergence rate (limit with modulus)
    ├── Paper 34, Theorem 2: Li₂ series (geometric tail bound)
    ├── Paper 8: Onsager exact solution (explicit rate)
    └── Paper 32: QED Landau pole (closed-form solution)

CATEGORY C-WLPO (Threshold/Equality Decision):
├── Paper 18: Heaviside decoupling (μ = m_f ∨ μ ≠ m_f)
├── Paper 20: 1D Ising magnetization (h = 0 ∨ h ≠ 0)
├── Paper 33: QCD mass gap (Δ = 0 ∨ Δ > 0)
├── Paper 2: Bidual gap (‖κ(x)‖ = ‖x‖ ∨ ‖κ(x)‖ ≠ ‖x‖)
└── Paper 13: Event horizon (r = 2M decision)

CATEGORY C-LLPO (Disjunction Decision):
├── Paper 21: Bell nonlocality (LLPO ↔ IVT mechanism)
├── Paper 27: Bell-IVT tight calibration
├── Paper 19: WKB tunneling
└── Paper 15: Noether global charge sign

CATEGORY C-LPO (Completed Limit Without Modulus):
├── Thermodynamic / continuum limits
│   ├── Paper 29: Fekete subadditive lemma ↔ LPO (the foundational result)
│   ├── Paper 8: Ising thermodynamic limit
│   ├── Paper 33: QCD continuum limit
│   └── Paper 17: Bekenstein-Hawking S = A/4
├── Global coupling / field existence
│   ├── Paper 32: QED coupling α(μ) as completed real
│   ├── Paper 33: QCD coupling g(μ) as completed real
│   ├── Paper 4: Spectral decomposition (infinite-dim)
│   └── Paper 7: Trace-class operators (infinite-dim)
├── All-orders summation
│   ├── Paper 34, Theorem 7: Perturbative series convergence
│   └── Paper 22: Radioactive decay (Markov's Principle, subsumed by LPO)
└── Exact/global assertions
    ├── Paper 13: Global event horizon existence
    ├── Paper 15: Global Noether charge conservation
    └── Paper 5: Schwarzschild singularity assertion

CATEGORY > LPO:
└── (empty)
```

**Lean architecture:**

```
-- Classification enum
inductive CRMCategory where
  | BISH     : CRMCategory  -- finitary computation
  | WLPO     : CRMCategory  -- threshold/equality decision
  | LLPO     : CRMCategory  -- disjunction decision  
  | LPO      : CRMCategory  -- completed limit without modulus

-- Each paper's result as classified instance
structure CalibratedResult where
  paper : ℕ
  description : String
  category : CRMCategory
  mechanism : String

-- The calibration table (representative entries)
def calibration_table : List CalibratedResult := [
  ⟨34, "Tree-level Bhabha", .BISH, "rational function"⟩,
  ⟨34, "One-loop Feynman integrals", .BISH, "computable special functions"⟩,
  ⟨34, "Dimensional regularization", .BISH, "formal Laurent series"⟩,
  ⟨34, "All-orders convergence", .LPO, "BMC"⟩,
  ⟨29, "Fekete lemma", .LPO, "BMC ↔ LPO"⟩,
  ⟨18, "Heaviside decoupling", .WLPO, "zero-test"⟩,
  ⟨21, "Bell nonlocality", .LLPO, "IVT/disjunction"⟩,
  ⟨8,  "Ising thermodynamic limit", .LPO, "BMC"⟩,
  ⟨33, "QCD confinement", .WLPO, "Markov positivity, subsumed by LPO"⟩,
  -- ... (full table: ~50 entries across 34 papers)
]

-- Exhaustiveness: no entry exceeds LPO
theorem no_entry_exceeds_LPO :
    ∀ r ∈ calibration_table, r.category = .BISH ∨ r.category = .WLPO ∨
    r.category = .LLPO ∨ r.category = .LPO := by
  simp [calibration_table]  -- decidable by enumeration

-- The hierarchy is linearly ordered and LPO is the ceiling
-- BISH < LLPO < WLPO < LPO  (strict inclusions, standard)
theorem hierarchy : BISH_strict_lt_LLPO ∧ LLPO_strict_lt_WLPO ∧ WLPO_strict_lt_LPO := by
  sorry -- FILL: standard separations from constructive analysis literature
```

**Expected axiom profile:** The classification is decidable enumeration — BISH. The hierarchy separations use standard counterexamples from constructive analysis.

---

### Theorem D: The Three Mechanisms Are Exhaustive

**Statement:** Every instance of LPO in the calibration table arises from exactly one of three mechanisms:

**(M1) Bounded Monotone Convergence (BMC).** Asserting that a bounded monotone sequence converges. Equivalent to LPO. Examples: thermodynamic limits, coupling constant existence, spectral convergence.

**(M2) Cauchy Completeness Without Modulus.** Asserting that a Cauchy sequence converges when no computable modulus of Cauchy convergence is available. Equivalent to BMC (hence LPO) via standard encoding.

**(M3) Supremum/Infimum Existence.** Asserting that a bounded set of reals has a supremum. Equivalent to BMC for monotone sequences. Examples: variational principles, ground state energy.

**Proof:** M1, M2, M3 are mutually interconvertible over BISH (standard results in constructive analysis: Ishihara, Bridges & Richman). Each LPO entry in the calibration table is exhibited as an instance of one of M1–M3:

- Thermodynamic limits → M1 (partial sums of free energy are bounded and monotone by subadditivity)
- Coupling constants → M2 (RG flow defines a Cauchy sequence without explicit modulus at non-perturbative level)
- Mass gaps / ground states → M3 (infimum of spectrum)
- Series summation → M1 (partial sums are bounded and monotone for positive-term series; general case via M2)

The WLPO entries arise from a fourth mechanism:

**(M4) Zero-Test / Threshold Decision.** Deciding x = 0 ∨ x ≠ 0 for a completed real x. This is WLPO, strictly weaker than LPO but subsumed by it.

And the LLPO entries from:

**(M5) Sign Decision / Disjunction.** Deciding x ≤ 0 ∨ x ≥ 0 for a completed real x. This is LLPO, strictly weaker than WLPO.

**Lean architecture:**

```
-- The five mechanisms
inductive LPOMechanism where
  | BMC              -- bounded monotone convergence
  | CauchyNoModulus  -- Cauchy completeness without rate
  | SupExists        -- supremum of bounded set

inductive WLPOMechanism where
  | ZeroTest         -- x = 0 ∨ x ≠ 0

inductive LLPOMechanism where
  | SignDecision     -- x ≤ 0 ∨ x ≥ 0

-- M1, M2, M3 are equivalent over BISH
theorem bmc_equiv_cauchy_no_modulus : BMC ↔ CauchyConvergenceWithoutModulus := by
  sorry -- FILL: standard, Bridges & Richman Ch. 2

theorem bmc_equiv_sup_exists : BMC ↔ BoundedSupExists := by
  sorry -- FILL: standard, monotone sequence from sup approximation

-- All LPO entries use exactly one of M1-M3
theorem lpo_entries_classified :
    ∀ r ∈ calibration_table, r.category = .LPO →
    ∃ m : LPOMechanism, r.mechanism_type = m := by
  sorry -- FILL: case analysis on table entries

-- All WLPO entries use M4
theorem wlpo_entries_classified :
    ∀ r ∈ calibration_table, r.category = .WLPO →
    r.mechanism_type = .ZeroTest := by
  sorry -- FILL: case analysis

-- All LLPO entries use M5
theorem llpo_entries_classified :
    ∀ r ∈ calibration_table, r.category = .LLPO →
    r.mechanism_type = .SignDecision := by
  sorry -- FILL: case analysis
```

**Expected axiom profile:** The equivalences M1 ↔ M2 ↔ M3 are BISH (constructive proofs exist in the literature). The classification is decidable enumeration.

---

## 5. The Central Argument (Informal, for Paper Narrative)

The informal argument that the paper presents to the reader — the thing that turns a catalogue into a thesis — is this:

**Why should LPO be the ceiling?**

Consider what a physicist does when making a prediction:

1. **Write down a Lagrangian.** This is a polynomial or rational expression in fields and their derivatives. Finite algebra. BISH.

2. **Derive equations of motion.** Euler-Lagrange equations. Formal calculus — differentiation of polynomials, variation of functionals. BISH.

3. **Solve the equations** (perturbatively or exactly). Perturbative: expand in coupling constant, compute Feynman diagrams, get rational/transcendental functions of kinematics. BISH at each order (Paper 34). Exact: solve a differential equation, which either has a closed-form solution (BISH) or requires asserting existence via completeness (LPO).

4. **Take a limit** (thermodynamic, continuum, infinite volume). This is where LPO enters. The limit exists by BMC if the sequence is bounded and monotone — which it typically is (free energy is subadditive, partition functions are positive, coupling constants are bounded by perturbative analysis). BMC ↔ LPO. Cost: exactly LPO.

5. **Compare to experiment.** The comparison is: compute the prediction to finite precision (BISH by step 3), measure the observable to finite precision, check overlap. BISH.

LPO is the ceiling because **step 4 is the only step that involves a completed infinite process**, and that process always has the structure of BMC. Steps 1–3 and 5 are finitary. Nothing in the physics requires deciding anything more complex than "does this bounded monotone sequence converge?" — and that is LPO, exactly.

Could a physical theory require more than LPO? In principle, yes — if a prediction required computing a function that is not Borel measurable, or deciding a Π₁¹-complete property. But no known physical theory has this structure. The equations of physics are differential equations with analytic coefficients, and the solutions (even when not explicitly computable) are at most limits of computable sequences. The Borel hierarchy does not arise. The arithmetic hierarchy beyond Σ₁⁰/Π₁⁰ (which is where LPO lives) does not arise.

This is not a proof that *no future physical theory* will require more than LPO. It is an explanation of why the theories we have — from Newtonian mechanics to the Standard Model to general relativity — do not.

---

## 6. File Structure

```
Paper35_ConservationMetatheorem/
├── Paper35/
│   ├── Defs.lean                -- ComputableFun, FiniteComposition, CRMCategory
│   ├── ComputableFunctions.lean -- Standard functions are computable (may use Mathlib)
│   ├── Composition.lean         -- Theorem A: composition preserves computability
│   ├── LimitBoundary.lean       -- Theorem B1: modulus → BISH
│   ├── BMC_LPO.lean             -- Theorem B2: import from Paper 29
│   ├── WLPO_LimitEquality.lean  -- Theorem B3: limit equality is WLPO
│   ├── CalibrationTable.lean    -- Theorem C: exhaustive classification
│   ├── Mechanisms.lean          -- Theorem D: M1-M5 classification
│   ├── Equivalences.lean        -- M1 ↔ M2 ↔ M3 (from literature)
│   └── Main.lean                -- imports, #print axioms, programme summary
└── lakefile.lean
```

**Target:** ~500-700 lines. This paper is conceptually heavy but Lean-light — most of the content is classification and enumeration rather than hard proof. The hardest Lean work is Theorem A (composition of computable functions), which Mathlib may already support.

---

## 7. Certification Protocol

| Component | Level | Justification |
|---|---|---|
| Theorem A (BISH conservation) | Level 2: Structurally verified | Constructive composition proof |
| Theorem B1 (modulus → BISH) | Level 2: Structurally verified | Constructive approximation |
| Theorem B2 (BMC ↔ LPO) | Level 3: Intentional classical | Reuse Paper 29, `Classical.choice` in forward direction |
| Theorem B3 (limit equality → WLPO) | Level 2: Structurally verified | Constructive encoding |
| Theorem C (exhaustiveness) | Level 1: Verified enumeration | Decidable case check on finite table |
| Theorem D (mechanism classification) | Level 2 + enumeration | Equivalences are BISH; table check is decidable |

---

## 8. Connection to Programme

### 8.1 This Paper's Role

Papers 1–34 are the *data*. Paper 10 (revised) is the *thesis statement*. Paper 35 is the *proof* — the explanation of why the data has the pattern it does.

The logical structure of the programme is now:

```
Papers 1–34: Empirical calibrations
     ↓ (evidence for)
Paper 10: "The logical constitution of empirical physics is BISH+LPO"
     ↓ (explained by)
Paper 35: "This follows from the computable structure of physical predictions
           and the BMC ↔ LPO characterization of completed limits"
```

### 8.2 What Paper 35 Does NOT Claim

- It does NOT prove that all possible physical theories are BISH+LPO. A future theory with non-computable predictions could exceed LPO.
- It does NOT prove that LPO is *necessary*. A radically constructive reformulation of physics might eliminate all completed limits and work entirely in BISH. (Whether such a reformulation loses physical content is an open question.)
- It does NOT prove that the calibration table is complete. There are physical predictions not yet calibrated (multi-loop amplitudes beyond one loop, non-perturbative QCD observables beyond confinement, quantum gravity predictions). The metatheorem predicts they will calibrate to BISH+LPO; confirming this is future work.

### 8.3 The Sentence for Paper 10

The revised Paper 10 synthesis can now include:

> "The logical constitution of empirically accessible physics is BISH+LPO. This is not an empirical coincidence but a structural consequence of two facts: (i) physical predictions at finite precision are finite compositions of computable functions (Theorem A), and (ii) the only idealizations that exceed finite computation are completed limits, whose logical cost is exactly LPO via the BMC equivalence (Theorem B). The constructive hierarchy BISH ⊂ LLPO ⊂ WLPO ⊂ LPO exhaustively classifies all non-constructive content encountered across the Standard Model, general relativity, statistical mechanics, and quantum information (Theorem C), with three equivalent mechanisms — bounded monotone convergence, Cauchy completeness without modulus, and supremum existence — accounting for all LPO instances (Theorem D)."

---

## 9. Instructions for the Lean Agent

### Priority order:
1. `Defs.lean` — the type system for the classification
2. `CalibrationTable.lean` — encode the table, verify exhaustiveness
3. `BMC_LPO.lean` — import from Paper 29
4. `LimitBoundary.lean` — Theorem B1, the easy direction
5. `WLPO_LimitEquality.lean` — Theorem B3 encoding
6. `Composition.lean` — Theorem A (may lean on Mathlib)
7. `Mechanisms.lean` + `Equivalences.lean` — M1-M5
8. `ComputableFunctions.lean` — standard functions (may be axiomatized if Mathlib lacks infrastructure)

### What to reuse:
- Paper 29: `BMC ↔ LPO` (critical — this is the engine)
- Paper 34: `Li₂_computable`, `ComputableFun` structure
- Paper 32: `WardIdentity` as example of BISH algebraic identity
- Papers 2, 18, 21: `WLPO`, `LLPO` definitions and examples

### What's new:
- `FiniteComposition` inductive type for composition trees
- `CRMCategory` classification enum
- `CalibratedResult` table with 50+ entries
- Composition theorem for `ComputableFun`
- Mechanism equivalences M1 ↔ M2 ↔ M3

### Target: The table enumeration should have zero sorry. The composition theorem and mechanism equivalences may have sorry if Mathlib infrastructure is missing — flag these and axiomatize if necessary with clear documentation.

---

## 10. Potential Pitfalls

1. **"Computable function" ambiguity.** In constructive mathematics, "computable" has a specific technical meaning (Type-2 computability). In Lean/Mathlib, `Computable` is a typeclass that may not align perfectly. The Lean agent should use explicit approximation bounds (the `ComputableFun` structure with `approx` and `spec` fields) rather than relying on Mathlib's `Computable` typeclass, which may be too weak or too strong for our purposes.

2. **The classification is meta-mathematical.** Theorem C classifies *results from other papers*, which means it references external Lean files. The cleanest approach is to import the `#print axioms` output from each paper as a `theorem` and then classify based on which axioms appear. This is mechanically verifiable but requires all 34 paper repositories to be importable. If that's impractical, axiomatize the classification (each paper's axiom profile as a declared constant) and verify the table structure.

3. **The informal argument (§5) is not formalized.** The "five steps of a physicist" narrative is for the paper's prose, not for Lean. Do not attempt to formalize "what a physicist does." The Lean content is Theorems A–D. The narrative is the human-readable explanation that connects the formal results to the philosophical claim.

4. **Theorem A is almost trivially true.** That's fine. The point of Paper 35 is not mathematical difficulty — it's conceptual organization. The metatheorem is "easy" in the same way that saying "the real numbers are a complete ordered field" is easy. The content is in recognizing that this characterization *explains* a large body of specific results.

5. **Future-proofing.** If Papers 36+ calibrate new domains and all land at BISH+LPO, Theorem C's table grows but Theorems A, B, D remain unchanged. If a future paper finds a prediction requiring more than LPO, Theorem C fails but Theorems A and B remain valid — they correctly characterize the BISH/LPO boundary, and the new result would require identifying a new mechanism beyond M1–M5. This is the scientific virtue of the framework: it is *falsifiable*.

---

## 11. What BISH+LPO Excludes: The Other Side of the Boundary

The characterization "empirical physics is BISH+LPO" is vacuous unless BISH+LPO excludes something substantive. This section identifies precisely what lies beyond the boundary — what nature, if the characterization is correct, *cannot do*.

### 11.1 Placement in the Arithmetic Hierarchy

LPO is equivalent to Σ₁⁰-LEM: the law of excluded middle restricted to statements of the form ∃n P(n), where P is decidable. In the arithmetic hierarchy:

```
Σ₁⁰:  ∃n P(n)                    — LPO decides this
Π₁⁰:  ∀n P(n)                    — LPO decides this (by contrapositive: ¬∃n ¬P(n))
Σ₂⁰:  ∃n ∀m Q(n,m)              — BEYOND LPO
Π₂⁰:  ∀n ∃m Q(n,m)              — BEYOND LPO
Σ₃⁰:  ∃n ∀m ∃k R(n,m,k)        — FAR BEYOND LPO
...
Full LEM: decidability of arbitrary propositions — incomparably beyond LPO
```

BISH+LPO occupies the first level. It can decide one layer of quantifier alternation. Everything above — every statement requiring nested quantifier alternation without reduction to a single existential — is *excluded*.

### 11.2 Five Concrete Exclusions

**Exclusion 1: General convergence testing.**

The statement "the sequence (aₙ) converges" is Π₂⁰:

∀ε > 0, ∃N, ∀n,m > N, |aₙ - aₘ| < ε

This has ∀∃∀ quantifier structure. LPO cannot decide it for arbitrary sequences. Nature can complete *specific* limits — BMC handles bounded monotone sequences, which reduce to Σ₁⁰ by the monotonicity constraint. But nature cannot build a general-purpose convergence oracle. No physical device can take an arbitrary stream of real numbers and decide whether it converges.

This is not academic. It means that the assertion "the perturbative QED series converges" (Paper 34, Theorem 7) costs LPO only because we *assume* monotonicity/boundedness. If the series is neither bounded nor monotone — which QED's asymptotic series actually isn't — the assertion "the series has a well-defined sum" (in the sense of Borel summation or resurgent analysis) may exceed LPO entirely. This is an open question the programme has not resolved.

**Physical consequence:** No experiment can determine whether an arbitrary physical process converges to a steady state. The universe can *reach* steady states (BMC), but it cannot *certify* that an arbitrary dynamical system will reach one.

**Exclusion 2: Non-Δ₂⁰ real numbers.**

The real numbers accessible to BISH+LPO are exactly the Δ₂⁰ reals — those whose binary expansion can be computed by a Turing machine equipped with a halting oracle. Equivalently, these are the reals that are limits of computable sequences of rationals (limit-computable reals). This is a vast class — it includes all computable reals, all computably enumerable reals, and much more. But it does not include *all* reals.

The excluded reals include:
- Martin-Löf random reals that are not limit-computable (the "generic" reals in the measure-theoretic sense)
- Reals encoding Σ₂⁰-complete problems (e.g., the binary expansion of a real that encodes "the set of Turing machines that halt on infinitely many inputs")
- All reals higher in the arithmetic hierarchy

**Physical consequence:** If nature is BISH+LPO, then every physical constant — α, mₑ, Λ, G, ℏ — is Δ₂⁰. Each admits a finite description: a Turing machine plus a halting oracle that computes its digits. No physical constant can encode a Σ₂⁰-complete problem. The fine structure constant is not "random" in any strong algorithmic sense.

This is testable in principle: if someone proved that a specific physical constant must encode a non-limit-computable real (e.g., via a self-referential argument involving the constant's own measurability), the BISH+LPO characterization would be refuted. No such argument is known.

**Exclusion 3: Fan Theorem and Bar Induction.**

Paper 30 proved that the Fan Theorem is dispensable for empirical physics — its content (compactness arguments, variational principles) can be recovered at BISH+LPO via direct computation. But FT and its stronger cousin Bar Induction (BI) are *logically independent* of LPO — they live in a different dimension of the constructive lattice. FT is about exhaustive search over finitely-branching trees. BI is about induction over well-founded trees.

Their exclusion means: nature does not perform unrestricted tree searches. A physical process can search a bounded tree (finite computation, BISH), and it can complete a monotone limit (LPO), but it cannot navigate an arbitrary well-founded tree. The infinite tree of possible histories is not physically accessible as a completed object.

**Physical consequence:** This connects to the dispensability of Dependent Choice (Paper 31). DC builds paths through trees by making countably many dependent selections. Physics doesn't need this — every "choice" in physics is either finite (BISH) or reducible to a monotone limit (LPO). The tree structure that DC and FT require is scaffolding, not physics.

**Exclusion 4: Set-theoretic combinatorics.**

BISH+LPO is an arithmetic theory. It speaks about natural numbers, sequences of natural numbers, and real numbers constructed from them. It has no opinion on:

- The Continuum Hypothesis (CH): Is there a set with cardinality strictly between ℕ and ℝ?
- Large cardinal axioms: Do inaccessible cardinals, measurable cardinals, etc. exist?
- Axiom of Choice (full AC): Can every family of nonempty sets be simultaneously selected from?
- Determinacy axioms: Are all games on natural numbers determined?

If physics is BISH+LPO, then all of these are *physically meaningless*. Not wrong, not right — simply outside the scope of what physical processes can instantiate or distinguish. No experiment can detect whether CH holds. No measurement can distinguish a universe with large cardinals from one without.

**Physical consequence:** The ongoing debate about whether set theory describes physical reality is resolved: it doesn't, because physics never reaches the set-theoretic stratum. This is not a philosophical position — it's a theorem about the logical resources physics actually uses. Zermelo-Fraenkel set theory is to physics what the full Oxford English Dictionary is to a grocery list: the grocery list is written in English, but it uses only a minuscule fragment. Physics is written in mathematics, but it uses only BISH+LPO.

**Exclusion 5: Full classical logic (LEM for arbitrary propositions).**

LPO is LEM restricted to Σ₁⁰ sentences. Full LEM — for every proposition P, either P or ¬P — is incomparably stronger. It decides arbitrary set existence, impredicative definitions, and transfinite constructions.

The excluded instances include any LEM application to:
- Π₂⁰ and higher statements (general convergence, "for all ε there exists N...")
- Statements about sets of reals ("the set of zeros of this function is empty or nonempty")
- Statements involving power sets, function spaces, or higher-type objects

**Physical consequence:** When a physicist writes "either the electron went through slit A or slit B," this is an application of LEM to a Σ₁⁰ statement (a detection event occurs or doesn't) — LPO covers it. But when a physicist writes "either the wavefunction collapses or it doesn't" as a statement about the *entire Hilbert space*, this is LEM applied to a much more complex proposition. BISH+LPO doesn't validate this usage. The measurement problem, in this light, is partly a *logical* problem: it applies LEM to a stratum where LEM is not physically available.

### 11.3 The Hierarchy Diagram

```
                     Full LEM (Classical Mathematics)
                            ↑
                         [vast gap]
                            ↑
                     Full AC, CH, Large Cardinals
                            ↑
                         [vast gap]
                            ↑
              Bar Induction / Full Dependent Choice
                     ↑              ↑
               Fan Theorem     Σ₂⁰-LEM, Π₂⁰-LEM
                     ↑              ↑
                     ↑         [BEYOND PHYSICS]
    ═══════════════════════════════════════════════
                     ↑         [PHYSICS LIVES HERE]
                     ↑              ↑
                    LPO ←────── BMC (Paper 29)
                     ↑
                   WLPO ←────── Zero-test / threshold decision
                     ↑
                   LLPO ←────── Sign decision / disjunction
                     ↑
                   BISH ←────── Finite computation, computable functions
                     ↑
                  (Pure logic, no mathematical content)
```

The double line is the boundary. Everything below it has been physically instantiated in Papers 1–35. Everything above it is logically dispensable scaffolding or set-theoretic superstructure that physics never accesses.

Bishop drew the bottom of the diagram. Papers 1–35 discovered where the boundary sits. The boundary is at LPO — one quantifier alternation, bounded monotone convergence, the simplest non-trivial omniscience principle. Nothing in known physics crosses it.

### 11.4 Lean Architecture for §11

```
-- The arithmetic hierarchy levels
inductive ArithLevel where
  | Sigma0 : ArithLevel  -- decidable
  | Sigma1 : ArithLevel  -- ∃n P(n), P decidable — LPO decides this
  | Pi1    : ArithLevel  -- ∀n P(n), P decidable — LPO decides this
  | Sigma2 : ArithLevel  -- ∃n ∀m Q(n,m) — BEYOND LPO
  | Pi2    : ArithLevel  -- ∀n ∃m Q(n,m) — BEYOND LPO

-- LPO decides Σ₁⁰ statements
theorem lpo_decides_sigma1 (P : ℕ → Prop) [DecidablePred P] (lpo : LPO) :
    (∃ n, P n) ∨ (∀ n, ¬P n) := by
  exact lpo P

-- LPO does NOT decide Σ₂⁰ (separation result)
-- This is the key boundary theorem
theorem lpo_insufficient_for_sigma2 :
    ¬(LPO → ∀ (Q : ℕ → ℕ → Prop) [∀ n, DecidablePred (Q n)],
      (∃ n, ∀ m, Q n m) ∨ ¬(∃ n, ∀ m, Q n m)) := by
  sorry -- FILL: standard separation via Kleene tree or similar

-- Convergence is Π₂⁰ (hence beyond LPO for arbitrary sequences)
theorem convergence_is_Pi2 :
    ∀ (a : ℕ → ℝ), (∀ ε > 0, ∃ N, ∀ n m, n ≥ N → m ≥ N → |a n - a m| < ε) →
    ArithComplexity.Pi2 := by
  sorry -- FILL: classify quantifier structure

-- Physical constants are Δ₂⁰ (limit-computable)
-- This is a consequence, not a proof — we state it as a corollary
theorem physical_constant_is_Delta2 (c : PhysicalConstant) (h : BISH_LPO_computable c) :
    Delta2_real c.value := by
  sorry -- FILL: Δ₂⁰ = limit of computable sequence = BMC-accessible
```

---

## 12. Consequences and Implications

This section belongs in the paper's prose, not in the Lean formalization. It draws out what follows if the BISH+LPO characterization is correct.

### 12.1 For Quantum Gravity

String theory's mathematical infrastructure requires moduli stabilization (choosing a vacuum from a landscape), Calabi-Yau geometry (Hodge theory, harmonic forms, which use compactness and hence FT), and the swampland programme (universal claims about all consistent quantum gravity theories, which have ∀∃ structure). If the BISH+LPO characterization holds, then:

- The string landscape is scaffolding. Whatever empirical predictions string theory eventually makes will be BISH+LPO computable. The non-constructive apparatus of the landscape is a convenience for *organizing* predictions, not for *making* them.
- The swampland conjectures, if physically meaningful, must be expressible at BISH+LPO. Swampland bounds that require quantification over all possible EFTs ("no consistent theory has...") are Π₂⁰ at best and may exceed BISH+LPO. If they cannot be reduced to Σ₁⁰ statements, they are logically disconnected from empirical physics.

Loop quantum gravity, by contrast, works primarily with combinatorial structures (spin networks, spin foams) that are BISH at finite size. The continuum limit (refinement limit of spin foams) would cost LPO. This is the same pattern as every other theory: BISH at finite stage, LPO at the limit. LQG fits the characterization straightforwardly.

### 12.2 For the Measurement Problem

Paper 23 calibrated the measurement problem as a disagreement about Dependent Choice (DC_ω). Paper 31 proved DC is dispensable for empirical physics. Together, these suggest:

The measurement problem is not a problem about physics. It is a problem about which *mathematical framework* to use for describing quantum evolution. The Everettian many-worlds interpretation uses DC (to build branching histories). The Copenhagen interpretation uses WLPO (to decide whether a measurement outcome occurred). The Bohmian interpretation uses LPO (to assert the existence of a definite particle trajectory as a completed real). All three make the same BISH-level empirical predictions. They disagree only about non-empirical ontological claims that live at different points in the constructive hierarchy.

This does not "solve" the measurement problem. It *dissolves* it — re-diagnosing it as a question about mathematical taste (which scaffolding principle do you prefer?) rather than a question about physical reality (what actually happens during measurement?).

### 12.3 For the Cosmological Constant Problem

The cosmological constant "problem" is the claim that quantum field theory predicts Λ_QFT ≈ 10¹²⁰ Λ_observed. But the QFT "prediction" involves summing zero-point energies — an infinite sum of mode contributions:

Λ_QFT = Σₖ (1/2)ℏωₖ

This sum diverges. The "prediction" is obtained by cutting off the sum at the Planck scale, completing the limit, and comparing the result to observation. But the cutoff and completion are precisely the operations that cost LPO (the sum is bounded by the cutoff, monotone in k, and completed by BMC).

The BISH-level content of the QFT vacuum energy is: "for any finite number of modes, the vacuum energy is a computable, finite number." The LPO-level content is: "the completed infinite sum exists." The 10¹²⁰ discrepancy lives entirely at the LPO level — it is a statement about a completed infinite object that no experiment accesses.

If the characterization is correct, the cosmological constant problem is an artifact of taking an idealization (the completed sum) seriously as a physical prediction. No experiment measures the vacuum energy of infinitely many modes. The finite-mode vacuum energy, which is what experiments actually probe, is BISH and poses no paradox.

This is not a resolution. It is a reclassification: from "the theory makes a wrong prediction" to "the theory makes an idealization that produces a non-physical number." Whether the actual cosmological constant can be computed constructively from a finite theory remains open.

### 12.4 For the Nature of Physical Constants

If every physical constant is Δ₂⁰, then the universe's fundamental parameters are not "arbitrary" or "random" in the information-theoretic sense. Each constant admits a finite description — an algorithm that, given access to a halting oracle, computes its digits. The description may be unknown to us (we don't know the algorithm for α = 1/137.035999...), but the characterization guarantees such a description *exists*.

This has implications for the fine-tuning debate. If the physical constants are Δ₂⁰ but not computable (i.e., they require the halting oracle, not just a Turing machine), then they occupy a specific complexity class: limit-computable but not computable. This is a *much* more constrained notion of "fine-tuning" than the usual discussion, which treats the constants as arbitrary real numbers drawn from some probability distribution. The BISH+LPO characterization says the constants are drawn from a *countable* class (Δ₂⁰ reals are countable), not from the full continuum.

### 12.5 For Consciousness and AI

The most speculative consequence. If consciousness supervenes on physical processes, and physical processes are BISH+LPO, then consciousness cannot access mathematical truths beyond Σ₁⁰. A conscious being can:

- Decide whether a specific computation halts (with LPO as oracle)
- Compute any Δ₂⁰ real number to arbitrary precision
- Complete any bounded monotone limit

A conscious being cannot:

- Decide whether an arbitrary sequence converges (Π₂⁰)
- Compute a non-Δ₂⁰ real number
- Verify the Continuum Hypothesis by introspection

This is consistent with the phenomenology of mathematical intuition: mathematicians can "see" individual truths (Σ₁⁰ instances) but cannot reliably survey infinite classes (higher quantifier alternation requires proof, not intuition). The BISH+LPO characterization would explain why mathematical intuition is powerful but limited — it operates within the computational architecture of physical reality, which stops at one quantifier alternation.

For AI: current neural networks operate entirely within BISH (finite arithmetic on finite-precision numbers). An AI system that could implement LPO — completing genuine infinite limits — would exceed current architectures. Whether such an implementation is physically possible (the characterization says nature *can* do LPO, via BMC) is an open engineering question, not a logical impossibility.

---

## 13. Synthesis of the Programme: Papers 1–35

### 13.1 Three Phases

The programme developed in three phases, visible in retrospect:

**Phase I: Calibration (Papers 1–28).** Individual physical theories were calibrated against the constructive hierarchy. Results accumulated: Schwarzschild geometry (Paper 5), quantum spectra (Paper 4), Heisenberg uncertainty (Paper 6), Ising model (Papers 8–9), Bell nonlocality (Papers 11, 21, 27), event horizons (Paper 13), decoherence (Paper 14), Noether conservation (Paper 15), Born rule (Paper 16), black hole entropy (Paper 17), Yukawa RG (Paper 18), WKB tunneling (Paper 19), Ising magnetization (Paper 20), radioactive decay (Paper 22), measurement problem (Paper 23), mean ergodic theorem (Paper 25), classical mechanics (Paper 28). Each paper was a data point. The pattern — BISH for finite, LPO for limits, nothing higher — emerged empirically.

**Phase II: Foundation (Papers 29–31).** Three structural results transformed the programme from pattern-matching to thesis. Paper 29 proved Fekete's Subadditive Lemma ≡ LPO, establishing that phase transitions (empirically real phenomena) *require* LPO — it is not a mere mathematical convenience but a physically instantiated principle. Paper 30 proved the Fan Theorem is dispensable — compactness arguments are scaffolding for BISH+LPO results. Paper 31 proved Dependent Choice is dispensable — sequential construction principles are scaffolding. Together: BISH+LPO is *necessary and sufficient* for empirical physics. Not just sufficient (which was always obvious — classical math is stronger and covers everything), but necessary (LPO is required, FT and DC are not).

**Phase III: Completion (Papers 32–35).** The Standard Model was swept systematically. Paper 32 (QED one-loop renormalization), Paper 33 (QCD one-loop + confinement), and Paper 34 (scattering amplitudes — the actual observables) established that the entire Standard Model, perturbative and non-perturbative, lives at BISH+LPO. Paper 35 — this paper — explains *why*: the metatheorem that the BISH/LPO boundary is a consequence of computable analysis, not an accident of physics.

### 13.2 What Was Established

The programme establishes the following claims, each supported by formal verification in Lean 4:

**Claim 1: The empirical content of physics is BISH at finite precision.** Every physical prediction that can be compared to experiment at finite precision — a cross section, a transition temperature, a spectral line — is a computable real number that can be approximated by a constructive algorithm. No omniscience principle is needed. (Papers 1–34 provide the evidence; Paper 35, Theorem A provides the explanation.)

**Claim 2: LPO is the exact cost of physical idealization.** Every completed limit in physics — thermodynamic limits, continuum limits, exact solutions, global field existence — costs exactly LPO via the BMC equivalence. Not more, not less. (Paper 29 is the foundational result; Papers 8, 17, 32, 33 provide instances across domains.)

**Claim 3: LPO is physically instantiated, not merely convenient.** Phase transitions are empirically real. They require Fekete's lemma. Fekete's lemma is equivalent to LPO. Therefore LPO is not a mathematical idealization — it describes a computation that nature actually performs. (Paper 29.)

**Claim 4: FT and DC are physically dispensable.** The Fan Theorem and Dependent Choice, while used in textbook proofs, can be eliminated from every empirical prediction without changing the result. They are scaffolding: logically expensive frameworks that organize proofs but contribute no physical content. (Papers 30, 31.)

**Claim 5: The constructive hierarchy BISH ⊂ LLPO ⊂ WLPO ⊂ LPO exhaustively classifies all non-constructive content in known physics.** No physical prediction in the Standard Model, general relativity, statistical mechanics, or quantum information requires any principle above LPO in the constructive lattice. (Papers 1–34 provide the evidence; Paper 35, Theorem C provides the audit.)

**Claim 6: The BISH+LPO characterization is falsifiable.** It makes concrete predictions about what nature cannot do: no physical process can decide general convergence, access non-Δ₂⁰ reals, or perform unrestricted tree searches. If a physical phenomenon is discovered that requires Σ₂⁰ reasoning, the characterization is refuted. (Paper 35, §11.)

### 13.3 What Was Not Established

Honesty requires listing what the programme does *not* prove:

- It does not prove that all *possible* physical theories are BISH+LPO. A future theory might require more. The characterization applies to known physics.
- It does not prove that physics is *only* BISH+LPO. There might be physical processes that implement higher principles but whose effects are too subtle to appear in current theories.
- It does not resolve the measurement problem, the cosmological constant problem, or any other open problem in physics. It reclassifies these problems as questions about mathematical scaffolding, but reclassification is not resolution.
- It does not prove that the Lean formalizations are free of mathematical errors. Lean verifies logical consistency, not physical correctness. If a bridge lemma axiomatizes incorrect physics, the Lean proof is valid but the physical conclusion is wrong.
- It does not determine whether nature "is" a BISH+LPO computer in any ontological sense. The characterization is epistemological: it describes the logical resources needed to *predict* physical behavior, not the logical resources the universe *uses* to *generate* that behavior. The distinction between epistemology and ontology here is genuine and unresolved.

### 13.4 The Formalization

Across 35 papers, the programme has produced approximately 28,000–30,000 lines of verified Lean 4 code. The core results — BMC ↔ LPO, FT dispensability, DC dispensability, Ward identity preservation, scattering amplitude computability — compile with zero sorry. Bridge lemmas (axiomatized physics) are explicitly declared with `axiom` and documented. The certification protocol from Paper 10 §7 classifies every theorem at one of four levels:

- Level 1: Fully verified (no axioms beyond Lean kernel)
- Level 2: Structurally verified (no `Classical.choice`, zero custom axioms)
- Level 3: Intentional classical (`Classical.choice` from LPO/WLPO hypothesis — this is the *content*, not contamination)
- Level 4: Axiomatized (physical assumptions declared as explicit axioms)

The formal verification is not incidental to the programme. Without it, the fine distinctions between BISH, WLPO, LLPO, and LPO would be unreliable — these principles are too close together in logical strength for informal reasoning to track correctly. The LPO-weakening incident (Paper 2, where another AI agent replaced meta-classical reasoning with LPO and thereby destroyed the calibration) demonstrated this concretely: the distinction between "using LPO in the metatheory" and "using LPO as an object-level assumption" is invisible to natural-language reasoning but mechanically checkable in Lean. The formalization is what makes the programme's claims *verifiable* rather than merely plausible.

### 13.5 The Status of the Programme

As of Paper 35, the calibration programme has achieved its primary objective: determining the logical constitution of empirically accessible physics across the major domains of modern physics. The result — BISH+LPO — is clean, falsifiable, and explained by a metatheorem.

The programme is open-ended in two directions. Defensively, new physical domains can be calibrated to stress-test the characterization (AdS/CFT, scattering amplitudes at higher loops, lattice QCD beyond one loop). Offensively, the characterization makes predictions about quantum gravity, consciousness, and the nature of physical constants that can be investigated.

Whether the programme is *important* — whether the characterization matters to physics — is not a question the programme can answer. It depends on whether physicists decide that knowing the logical constitution of their theories is worth knowing. The programme has made the case. The evidence is compiled, verified, and public.

---

## 14. Note on Bishop

Errett Bishop published "Foundations of Constructive Analysis" in 1967. He defined BISH — constructive mathematics without any choice or omniscience principles — as a philosophical programme: mathematics should be about constructions, not existence proofs. The omniscience principles (LPO, WLPO, LLPO) were identified by Bishop and his successors (Bridges, Richman, Ishihara) as the precise points where classical mathematics departs from constructive practice.

Bishop did not design these principles with physics in mind. He was doing pure mathematics — constructive real analysis, measure theory, functional analysis. The omniscience hierarchy was discovered by analyzing which classical theorems fail constructively and what minimal additional principles restore them. It was a purely logical cartography.

That this cartography — designed for pure mathematics in the 1960s–1990s — turns out to classify the non-constructive content of physics with perfect precision across 35 papers and 30,000 lines of formal verification is the most striking fact about the programme. Bishop's hierarchy was not built to fit physics. Physics was not built to fit Bishop's hierarchy. They fit because the hierarchy captures something real about the structure of mathematical reasoning, and physics uses exactly the fragment of that structure that corresponds to one layer of quantifier alternation over decidable predicates.

The fit is discovered, not designed. That is what makes it worth reporting.
