# Paper 5 Restructuring Outline: 150-200 Page Comprehensive Document

**Document:** Axiom Calibration for General Relativity: From Portal Theory to Verified Tensor Calculus
**Target Length:** 150-200 pages
**Current Base:** Paper5_GR_AxCal.tex (992 lines, ~30 pages)
**Codebase:** ~6,650 lines of Lean 4 (Schwarzschild.lean: 2,284, Riemann.lean: 4,058, Invariants.lean: 308)
**Status:** All Riemann component lemmas proven (0 errors, 0 sorries), Kretschmann scalar verified

---

## PART 1: AXIOM CALIBRATION FRAMEWORK (25-30 pages)

**Purpose:** Comprehensive exposition of the AxCal methodology applied to GR

### 1.1 Introduction and Motivation (4-5 pages)

**Content:**
- Opening narrative: Why axiom calibration matters for GR
- The "hidden axioms" problem in mathematical physics
- Structural Certification vs Foundational Verification distinction
- Roadmap for the entire paper

**Key Points:**
- Physical vs mathematical idealization (AC in maximal extensions)
- Computability crisis (Pour-El-Richards)
- The need for explicit dependency tracking

**Estimated Writing Time:** 6-8 hours

---

### 1.2 Portal Theory and Proof-Route Flags (6-8 pages)

**Content:**
- **1.2.1 The Four Portals** (2 pages)
  - Zorn Portal → Axiom of Choice (h_Choice = 1)
  - Limit-Curve Portal → FT/WKL₀ (h_Comp = 1)
  - Serial-Chain Portal → DC_ω (h_Choice = 1)
  - Reductio Portal → LEM (h_Logic = 1)

- **1.2.2 Portal Soundness** (2 pages)
  - Formal statement of Proposition 1.1 (portal soundness)
  - Meta-theoretical justification
  - Route sensitivity: same theorem, different heights

- **1.2.3 Proof-Route Flags in Practice** (2-3 pages)
  - Tagging mechanism
  - Uses(flag, derivation) predicates
  - Examples from GR literature (Wald, Hawking-Ellis)
  - How to identify portals in textbook proofs

**Mathematical Formalism:**
```
PortalFlag ∈ {uses_zorn, uses_limit_curve, uses_serial_chain, uses_reductio}
Uses(flag, D) : proof-route predicate
Portal soundness: Uses(flag, D) ⟹ HasAxiom(F)
```

**Estimated Writing Time:** 10-12 hours

---

### 1.3 AxisProfile and Height Certificates (5-7 pages)

**Content:**
- **1.3.1 The Three Axes** (2 pages)
  - h_Choice: AC, DC_ω, AC_ω (Choice axis)
  - h_Comp: FT, WKL₀ (Compactness axis)
  - h_Logic: LEM, WLPO, MP (Logic axis)
  - Height levels: {0, 1, ω}

- **1.3.2 Height Certificate Structure** (1-2 pages)
  - Witness family W
  - Profile (h_Choice, h_Comp, h_Logic)
  - Flags list
  - Upper bound proof
  - Citations

- **1.3.3 Certificate Composition** (1-2 pages)
  - Product law
  - Route alternatives
  - Profile refinement

- **1.3.4 Mathematical Height vs Infrastructural Cost** (1 page)
  - Critical distinction for this project
  - Classical mathlib as infrastructure
  - Height 0 means "portal-free at the strategic level"

**Example Certificates:**
```
G1_Vacuum_Cert: (0,0,0), flags = []
G2_MGHD_Cert: (1,0,0), flags = [uses_zorn]
G3_Penrose_Cert: (0,1,1), flags = [uses_limit_curve, uses_reductio]
```

**Estimated Writing Time:** 8-10 hours

---

### 1.4 Pinned Signature Σ₀^{GR} (3-4 pages)

**Content:**
- Fixed mathematical objects for GR
- Smooth manifolds (second-countable, Hausdorff)
- Lorentzian metrics
- Levi-Civita connection
- Curvature tensors (Riemann, Ricci, Einstein)
- Einstein Field Equations
- Pinned exemplars (Minkowski, Schwarzschild)

**Formal Specification:**
- Interpretation requirements
- Witness family construction over the pin
- Interface vs implementation

**Estimated Writing Time:** 5-6 hours

---

### 1.5 Witness Families for G1-G5 (5-6 pages)

**Content:**
- **G1: Explicit Vacuum Checks** (1 page)
  - Schwarzschild metric satisfies R_μν = 0
  - Profile: (0,0,0)
  - Finite symbolic computation

- **G2: Cauchy Problem** (1-2 pages)
  - Local PDE: well-posedness
  - MGHD: maximal globally hyperbolic development
  - Profile split: local (0,0,0) vs global (1,0,0)

- **G3: Singularity Theorems** (1 page)
  - Penrose/Hawking incompleteness
  - Profile: (0,1,1)
  - Compactness + contradiction

- **G4: Maximal Extensions** (1 page)
  - Zorn on poset of extensions
  - Profile: (1,0,0)

- **G5: Computable Evolution** (1-2 pages)
  - Pour-El-Richards negative template
  - Measurement streams and DC_ω
  - Profiles: (0,0,0) and (1,0,0)

**Estimated Writing Time:** 8-10 hours

---

### 1.6 Literature Integration (2-3 pages)

**Content:**
- Robb, Reichenbach: axiomatic kinematics
- EPS 1972: light and free-fall reconstruction
- Pour-El-Richards 1989: computability limits
- Bishop-Bridges 1985: constructive analysis
- Hellman/Bridges debate on GR foundations
- Wald, Hawking-Ellis, Choquet-Bruhat: portal locations

**Estimated Writing Time:** 4-5 hours

---

**PART 1 TOTAL PAGES:** 25-30
**PART 1 TOTAL WRITING TIME:** 40-50 hours

---

## PART 2: SCHWARZSCHILD/RIEMANN MATHEMATICAL FORMALIZATION (30-40 pages)

**Purpose:** Hand-written mathematical exposition of the formalized content (converting Lean to prose)

### 2.1 The Schwarzschild Solution (8-10 pages)

**Content:**
- **2.1.1 Schwarzschild Metric Derivation** (3-4 pages)
  - Spherical symmetry and static assumptions
  - Birkhoff's theorem (statement only)
  - Line element: ds² = -f(r)dt² + f(r)⁻¹dr² + r²dΩ²
  - The Schwarzschild factor: f(r) = 1 - 2M/r
  - Horizon at r = 2M
  - Asymptotic flatness

- **2.1.2 Christoffel Symbols** (2-3 pages)
  - General formula: Γᵃ_bc = ½gᵃᵈ(∂_b g_dc + ∂_c g_db - ∂_d g_bc)
  - Diagonal metric simplification
  - All 40 potentially non-zero symbols
  - 9 actually non-vanishing components (explicit computation)
  - Key identities: Γʳ_rr = -Γᵗ_tr, etc.

- **2.1.3 Metric Properties** (1-2 pages)
  - Signature (-,+,+,+)
  - Lorentzian structure
  - Coordinate singularities vs curvature singularities
  - Exterior region r > 2M

- **2.1.4 Derivatives and Smoothness** (1-2 pages)
  - C² smoothness of metric components
  - Derivative of f: f'(r) = 2M/r²
  - Derivative calculations for g_tt, g_rr
  - Non-vanishing conditions in exterior

**Mathematical Examples:**
```
Γᵗ_tr = M/(r(r-2M))
Γʳ_rr = -M/(r(r-2M))
Γʳ_θθ = -(r-2M)
Γᶿ_rθ = 1/r
... (all 9 non-zero components)
```

**Estimated Writing Time:** 12-15 hours

---

### 2.2 Riemann Curvature Tensor (10-12 pages)

**Content:**
- **2.2.1 Riemann Tensor Definition** (2 pages)
  - Coordinate formula: R^ρ_σμν = ∂_μ Γ^ρ_νσ - ∂_ν Γ^ρ_μσ + Γ^ρ_μλ Γ^λ_νσ - Γ^ρ_νλ Γ^λ_μσ
  - Interpretation: parallel transport around loops
  - Commutator of covariant derivatives
  - Tidal forces and geodesic deviation

- **2.2.2 Symmetries of the Riemann Tensor** (2-3 pages)
  - Antisymmetry: R_abcd = -R_bacd = -R_abdc
  - Pair exchange: R_abcd = R_cdab
  - First Bianchi identity: R_abcd + R_acdb + R_adbc = 0
  - How symmetries reduce 256 components to 20 independent

- **2.2.3 Schwarzschild Riemann Components** (3-4 pages)
  - Six non-zero independent components (by symmetry)
  - **R_trtr computation** (step-by-step)
    - Derivative terms: ∂_r Γᵗ_tr, ∂_t Γᵗ_rt
    - Product terms: Γᵗ_tr Γᵗ_tr + Γʳ_tr Γʳ_tr
    - Result: R_trtr = 2M/r³

  - **R_tθtθ computation**
    - Result: R_tθtθ = M/r

  - **R_tφtφ, R_rθrθ, R_rφrφ computations**
    - Results: M/r, M/r, M/r

  - **R_θφθφ computation**
    - Result: R_θφθφ = 2Mr²sin²θ

- **2.2.4 Raised Riemann Tensor** (1-2 pages)
  - Index raising: R^a_bcd = g^aα R_αbcd
  - Diagonal metric simplification
  - Non-zero raised components
  - Example: R^t_rtr = 2M/(r²(r-2M))

- **2.2.5 Component Lemma Strategy** (1 page)
  - Infrastructure: dCoord (directional derivative)
  - Γtot (unified Christoffel lookup)
  - Reduction lemmas for each component
  - Cancellation patterns

**Mathematical Worked Examples:**
Full by-hand computation of at least 2 components, showing every algebraic step.

**Estimated Writing Time:** 15-18 hours

---

### 2.3 Ricci Tensor and Vacuum Equations (6-8 pages)

**Content:**
- **2.3.1 Ricci Tensor Definition** (1-2 pages)
  - Contraction: R_μν = R^ρ_μρν
  - Physical interpretation: local volume expansion/contraction
  - Relationship to matter via Einstein equations

- **2.3.2 Ricci Tensor for Schwarzschild** (3-4 pages)
  - **R_tt computation**
    - Sum: R^r_trt + R^θ_tθt + R^φ_tφt
    - Cancellation: show algebraically why this vanishes
    - Final result: R_tt = 0

  - **R_rr computation**
    - Similar cancellation pattern
    - Result: R_rr = 0

  - **R_θθ and R_φφ computations**
    - Both vanish

  - **Off-diagonal components**
    - All zero by symmetry and computation

- **2.3.3 Vacuum Field Equations** (1 page)
  - Einstein vacuum equations: R_μν = 0
  - Schwarzschild as exact vacuum solution
  - Physical meaning: empty spacetime outside a spherical mass

- **2.3.4 Ricci Scalar** (1 page)
  - Definition: R = g^μν R_μν
  - For Schwarzschild: R = 0 (follows from R_μν = 0)
  - Scalar curvature vanishes in vacuum

**Estimated Writing Time:** 10-12 hours

---

### 2.4 Kretschmann Scalar Invariant (6-8 pages)

**Content:**
- **2.4.1 Curvature Invariants** (1-2 pages)
  - Why invariants matter (coordinate-independent)
  - Kretschmann scalar: K = R_abcd R^abcd
  - Physical meaning: tidal force strength

- **2.4.2 Six-Block Decomposition** (2-3 pages)
  - 256 terms in full double contraction
  - Symmetry reduces to 6 blocks (unordered pairs)
  - (t,r), (t,θ), (t,φ), (r,θ), (r,φ), (θ,φ)
  - Each block contributes with factor 4 (from ordering)

- **2.4.3 Block Calculations** (2-3 pages)
  - **(t,r) block:** 4M²/r⁶ (detailed computation)
  - **(t,θ) block:** M²/r⁶
  - **(t,φ) block:** M²/r⁶
  - **(r,θ) block:** M²/r⁶
  - **(r,φ) block:** M²/r⁶
  - **(θ,φ) block:** 4M²/r⁶

- **2.4.4 Final Result** (1 page)
  - Sum: K = 4×(4M²/r⁶ + M²/r⁶ + M²/r⁶ + M²/r⁶ + M²/r⁶ + 4M²/r⁶)
  - K = 4×12M²/r⁶ = 48M²/r⁶
  - Divergence at r = 0 (true singularity)
  - Finite at r = 2M (coordinate singularity only)
  - Physical interpretation

**Estimated Writing Time:** 10-12 hours

---

**PART 2 TOTAL PAGES:** 30-40
**PART 2 TOTAL WRITING TIME:** 47-57 hours

---

## PART 3: CODE DOCUMENTATION - SOFTWARE-STYLE WALKTHROUGH (70-90 pages)

**Purpose:** Block-by-block analysis with triple discussion (Physical/Mathematical/Lean)

### 3.1 File Organization and Architecture (8-10 pages)

**Content:**
- **3.1.1 Repository Structure** (2 pages)
  ```
  Papers/P5_GeneralRelativity/
    AxCalCore/
      Axis.lean           -- Height levels, AxisProfile
      Tokens.lean         -- Foundation tokens (HasAC, HasDCw, etc.)
    GR/
      Interfaces.lean     -- Σ₀^{GR} signature
      Portals.lean        -- Portal flags and soundness
      Witnesses.lean      -- G1-G5 witness families
      Certificates.lean   -- Height certificates
      EPSCore.lean        -- EPS kinematics (D1)
      Schwarzschild.lean  -- Schwarzschild engine (D2)
      Riemann.lean        -- Riemann tensor
      Invariants.lean     -- Kretschmann scalar (D3)
    Ledger/
      Citations.lean      -- Bibliography
  ```

- **3.1.2 Dependency Graph** (2-3 pages)
  - Interfaces → Schwarzschild → Riemann → Invariants
  - AxCalCore → Portals → Witnesses → Certificates
  - EPSCore (independent)
  - Visualization (text-based diagram)

- **3.1.3 Module Purposes** (2-3 pages)
  - Brief description of each file's role
  - Line counts and theorem counts
  - Schematic vs deep-dive distinction

- **3.1.4 Build System** (1-2 pages)
  - lake build commands
  - CI verification (no-sorry guards)
  - Axiom audits

**Estimated Writing Time:** 12-15 hours

---

### 3.2 AxCal Framework Code (12-15 pages)

**Content:**
- **3.2.1 Height and AxisProfile (Axis.lean)** (3-4 pages)

  **Block 1: Height Definition**
  ```lean
  inductive Height
  | zero  -- constructive/portal-free
  | one   -- single axiom needed
  | omega -- full classical strength
  ```

  - **Mathematical Statement:** Height levels form a three-point ordered set {0 < 1 < ω}
  - **Lean Code:** (verbatim from source)
  - **Proof Narrative:** Inductive type with three constructors
  - **Triple Discussion:**
    - **(a) Physical:** Height 0 = computationally realizable in principle
    - **(b) Mathematical:** Captures strength hierarchy (constructive → semi-classical → classical)
    - **(c) Lean Technical:** Simple inductive, computable equality/ordering

  **Block 2: AxisProfile**
  ```lean
  structure AxisProfile where
    hChoice : Height
    hComp   : Height
    hLogic  : Height
  ```

  - **Mathematical Statement:** Profile is a triple (h_C, h_Comp, h_L) ∈ {0,1,ω}³
  - **Lean Code:** (verbatim)
  - **Proof Narrative:** Structure with three fields
  - **Triple Discussion:**
    - **(a) Physical:** Separates different kinds of non-constructivity
    - **(b) Mathematical:** Product space with componentwise ordering
    - **(c) Lean Technical:** Lean structures, field access syntax

  (Continue for ~6-8 blocks total)

- **3.2.2 Portal Flags (Portals.lean)** (3-4 pages)

  **Block 1: PortalFlag Inductive**
  **Block 2: Zorn_portal axiom**
  **Block 3: LimitCurve_portal axiom**
  **Block 4: route_to_profile function**

  (Each block: Math statement + Lean code + Proof narrative + Triple discussion)

- **3.2.3 Witness Families (Witnesses.lean)** (3-4 pages)

  **Block 1: G1_Vacuum_W**
  **Block 2: G2_MGHD_W**
  **Block 3: G3_Penrose_W**

  (Each block: full treatment)

- **3.2.4 Certificates (Certificates.lean)** (3-4 pages)

  **Block 1: HeightCertificate structure**
  **Block 2: G1_Vacuum_Cert**
  **Block 3: Certificate registry**

**Estimated Writing Time:** 18-22 hours

---

### 3.3 Schwarzschild Engine Code (20-25 pages)

**Content:** Block-by-block walkthrough of Schwarzschild.lean (~96 theorems/lemmas)

**Major Blocks to Document (estimate ~25-30 blocks):**

- **3.3.1 Foundational Definitions** (3-4 pages)

  **Block 1: SchwarzschildCoords structure**
  - Math: 4-tuple (t,r,θ,φ) ∈ ℝ⁴
  - Lean: `structure SchwarzschildCoords where...`
  - Proof: N/A (definition)
  - Triple discussion:
    - (a) Physical: Standard spherical coordinates for spherically symmetric spacetime
    - (b) Mathematical: Product type ℝ⁴ with semantic field names
    - (c) Lean: Structure vs tuple trade-off, named fields

  **Block 2: Schwarzschild factor f(r) = 1 - 2M/r**
  - Math: f : ℝ × ℝ → ℝ, f(M,r) = 1 - 2M/r
  - Lean: `noncomputable def f (M r : ℝ) : ℝ := 1 - 2*M/r`
  - Proof: N/A
  - Triple discussion:
    - (a) Physical: Encodes gravitational field strength, horizon at f=0
    - (b) Mathematical: Rational function with pole at r=0, zero at r=2M
    - (c) Lean: noncomputable due to division, pure function

- **3.3.2 Positivity and Sign Properties** (4-5 pages)

  **Block 3: f_pos_of_hr theorem**
  ```lean
  theorem f_pos_of_hr (M r : ℝ) (hM : 0 < M) (hr : 2*M < r) : 0 < f M r := by
    have two_pos : 0 < (2 : ℝ) := by norm_num
    have h2Mpos : 0 < 2*M := mul_pos two_pos hM
    have hr_pos : 0 < r := lt_trans h2Mpos hr
    have hdiv : 2*M / r < 1 := (div_lt_one hr_pos).mpr hr
    simpa [f] using (sub_pos.mpr hdiv)
  ```

  - Math: ∀M,r ∈ ℝ, (M > 0 ∧ r > 2M) ⟹ f(M,r) > 0
  - Lean: (verbatim above)
  - Proof narrative:
    - "First, we establish that 2 is positive (norm_num)"
    - "Then 2M > 0 by positivity of products"
    - "Thus r > 2M > 0, so r > 0"
    - "Therefore 2M/r < 1 by division properties"
    - "Finally, 1 - 2M/r > 0 by subtraction"
  - Triple discussion:
    - (a) Physical: In the exterior region r > 2M, the metric component g_tt = -f is timelike (negative), and g_rr = 1/f is spacelike (positive). This is the signature of a Lorentzian spacetime.
    - (b) Mathematical: Basic inequality proof using ordered field properties. Demonstrates that f is a decreasing function from 1 at infinity to 0 at the horizon.
    - (c) Lean: Uses norm_num for numerical facts, mul_pos/div_lt_one from mathlib, simpa for final simplification. The have chain builds up hypotheses explicitly.

  **Block 4: f_pos_iff_r_gt_2M theorem** (iff characterization)
  **Block 5: f_eq_zero_iff_r_eq_2M theorem** (horizon characterization)

  (Continue with 5-6 more blocks on sign properties)

- **3.3.3 Derivative Calculations** (5-6 pages)

  **Block 6: f_hasDerivAt theorem**
  ```lean
  theorem f_hasDerivAt (M r : ℝ) (hr : r ≠ 0) :
      HasDerivAt (fun r' => f M r') (2*M / r^2) r := by
    have h_const : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 r := ...
    have h_id : HasDerivAt (fun x : ℝ => x) 1 r := hasDerivAt_id r
    have h_inv : HasDerivAt (fun x : ℝ => x⁻¹) (-(r^2)⁻¹) r := ...
    have h_mul : HasDerivAt (fun x : ℝ => (2*M) * x⁻¹) ((2*M) * (-(r^2)⁻¹)) r := ...
    have h_sub : HasDerivAt (fun x : ℝ => 1 - (2*M) * x⁻¹) ... r := ...
    simpa [f, div_eq_mul_inv, ...] using h_sub
  ```

  - Math: d/dr[f(M,r)] = 2M/r²
  - Lean: (verbatim above)
  - Proof narrative:
    - "The derivative of the constant function 1 is 0"
    - "The derivative of the identity r ↦ r is 1"
    - "The derivative of r⁻¹ is -r⁻² by the power rule"
    - "Multiplying by the constant 2M gives (2M)·(-r⁻²)"
    - "Subtracting from the constant 1 gives d/dr[1 - 2M/r] = 2M/r²"
  - Triple discussion:
    - (a) Physical: The derivative of f quantifies how the gravitational field strength changes with radius. Positive derivative (f increasing as r increases) means gravitational field weakens at larger distances. Near the horizon, f' = 2M/(2M)² = 1/(2M), finite and well-defined.
    - (b) Mathematical: Standard calculus chain rule and derivative rules. The form 2M/r² matches the Newtonian potential derivative, hinting at the weak-field limit. This is C^∞ for r ≠ 0.
    - (c) Lean: HasDerivAt is mathlib's formulation of differentiability at a point. Chain of have statements builds the derivative compositionally. simpa handles algebraic normalization. The hr : r ≠ 0 hypothesis is essential for the reciprocal.

  **Block 7: f_derivative theorem** (deriv form)
  **Block 8-10: g_tt, g_rr derivatives**

  (Continue with 8-10 more blocks on derivatives)

- **3.3.4 Metric Components** (3-4 pages)

  **Block 11: g definition**
  **Block 12: gInv definition**
  **Block 13: Diagonal properties**

  (4-6 blocks)

- **3.3.5 Christoffel Symbol Infrastructure** (4-5 pages)

  **Block 14: Γ_t_tr definition**
  **Block 15: Γ_r_rr definition**
  **Block 16: Γtot unified lookup**
  **Block 17-20: Zero lemmas for vanishing symbols**

  (8-10 blocks)

- **3.3.6 Ricci Tensor Scaffolding** (2-3 pages)

  **Block 21: Ricci definition**
  **Block 22: RicciScalar definition**
  **Block 23: Vacuum theorem stubs**

  (3-4 blocks)

**Estimated Writing Time:** 30-35 hours

---

### 3.4 Riemann Tensor Code (25-30 pages)

**Content:** Block-by-block walkthrough of Riemann.lean (~156 theorems/lemmas)

**THIS IS THE LARGEST AND MOST DETAILED SECTION**

**Major Subsections:**

- **3.4.1 Exterior Domain and Smoothness** (4-5 pages)

  **Block 1: Exterior structure**
  ```lean
  structure Exterior (M r θ : ℝ) : Prop where
    hM : 0 < M
    hr_ex : 2 * M < r
  ```

  - Math: Exterior domain = {(M,r,θ) | M > 0, r > 2M}
  - Lean: (verbatim)
  - Proof: N/A (definition)
  - Triple discussion:
    - (a) Physical: The exterior region is where the Schwarzschild metric is non-singular and has the correct signature. Inside r = 2M, the coordinates break down (Schwarzschild coordinates are bad there). This is the physically relevant region for observers outside a black hole.
    - (b) Mathematical: An open subset of ℝ³ defined by polynomial inequalities. The openness (proved in isOpen_exterior_set) is crucial for C² smoothness and derivative theorems.
    - (c) Lean: Defined as a Prop (proposition), not a Type. This allows using it as a hypothesis bundle. The structure syntax groups related assumptions.

  **Block 2: r_ne_zero and f_ne_zero lemmas**
  **Block 3: isOpen_exterior_set (topology)**
  **Block 4: deriv_zero_of_locally_zero (helper for Level 3 de-axiomatization)**

  **Block 5: C² Smoothness Infrastructure**
  - ContDiff lemmas for f, g components
  - HasDerivAt lemmas in neighborhoods
  - Importance for Riemann tensor computation

  (8-10 blocks in this subsection)

- **3.4.2 Directional Derivative and dCoord** (3-4 pages)

  **Block 6: dCoord definition**
  ```lean
  def dCoord (μ : Idx) (F : ℝ → ℝ → ℝ) (r θ : ℝ) : ℝ :=
    match μ with
    | Idx.t => 0
    | Idx.r => deriv (fun r' => F r' θ) r
    | Idx.θ => deriv (fun θ' => F r θ') θ
    | Idx.φ => 0
  ```

  - Math: Coordinate derivative operator ∂_μ F(r,θ)
  - Lean: (verbatim)
  - Proof: N/A (definition)
  - Triple discussion:
    - (a) Physical: The Schwarzschild metric is static and spherically symmetric, so nothing depends on t or φ. Only r and θ derivatives are non-zero. This encodes the symmetries of the spacetime.
    - (b) Mathematical: Partial derivative in 4D reduced to 2D by symmetry. The match expression dispatches on the coordinate index.
    - (c) Lean: Pattern matching on Idx. deriv is mathlib's univariate derivative. The function F takes two ℝ arguments (r and θ), and we partially apply to get univariate functions for differentiation.

  **Block 7: dCoord_r, dCoord_θ simp lemmas**
  **Block 8: dCoord linearity properties**

  (4-5 blocks)

- **3.4.3 Christoffel Derivative Calculators** (6-8 pages)

  **Block 9: deriv_Γ_t_tr_at theorem**
  ```lean
  theorem deriv_Γ_t_tr_at (M r : ℝ) (hr : r ≠ 0) (hf : f M r ≠ 0) (hr2M : r - 2*M ≠ 0) :
      deriv (fun r' => Γ_t_tr M r') r = -2*M / (r^2 * (r - 2*M)) := by
    calc
      deriv (fun r' => Γ_t_tr M r') r
          = deriv (fun r' => M / (r' * (r' - 2*M))) r := by rw [Γ_t_tr]
      _   = ... := by rw [deriv_div ...]
      _   = -2*M / (r^2 * (r - 2*M)) := by field_simp [hr, hr2M]; ring
  ```

  - Math: d/dr[Γᵗ_tr] = -2M/(r²(r-2M))
  - Lean: (verbatim, condensed)
  - Proof narrative:
    - "Start with the definition of Γᵗ_tr = M/(r(r-2M))"
    - "Apply the quotient rule for derivatives"
    - "Compute the derivative of the numerator (constant) and denominator (product)"
    - "Simplify using field arithmetic to clear denominators"
    - "Polynomial ring normalization yields the final form"
  - Triple discussion:
    - (a) Physical: This derivative appears in the R_trtr component of the Riemann tensor. The Christoffel symbols encode how the basis vectors change from point to point, and their derivatives capture the curvature. The factor 1/(r-2M) blowing up at the horizon is a coordinate artifact, not a curvature singularity.
    - (b) Mathematical: Quotient rule applied to a rational function. The result is also rational, with a higher-degree denominator. This demonstrates that the Christoffel symbols are C¹ (differentiable) in the exterior, and their derivatives are continuous.
    - (c) Lean: calc chains provide explicit intermediate steps. deriv_div is mathlib's quotient rule. field_simp clears denominators by multiplying through. ring handles polynomial identities. The three hypotheses (hr, hf, hr2M) ensure no division by zero.

  **Block 10: deriv_Γ_r_rr_at theorem**
  **Block 11: deriv_Γ_θ_φφ_at theorem**
  **Block 12: deriv_Γ_φ_θφ_at theorem**

  (These are the 4 critical derivative calculators, ~6-8 blocks total with supporting lemmas)

- **3.4.4 Riemann Tensor Definition and Reduction** (5-6 pages)

  **Block 13: Riemann definition**
  ```lean
  noncomputable def Riemann (M r θ : ℝ) (a b c d : Idx) : ℝ :=
    dCoord c (fun r' θ' => Γtot M r' θ' a b d) r θ
  - dCoord d (fun r' θ' => Γtot M r' θ' a b c) r θ
  + sumIdx (fun k => Γtot M r θ a c k * Γtot M r θ k b d)
  - sumIdx (fun k => Γtot M r θ a d k * Γtot M r θ k b c)
  ```

  - Math: R^a_bcd = ∂_c Γ^a_bd - ∂_d Γ^a_bc + Γ^a_ck Γ^k_bd - Γ^a_dk Γ^k_bc
  - Lean: (verbatim)
  - Proof: N/A (definition)
  - Triple discussion:
    - (a) Physical: The Riemann tensor is THE fundamental object in GR. It encodes all curvature information. Non-zero Riemann = spacetime is curved = gravity is present (even in vacuum). The four slots (a,b,c,d) correspond to: a = output index, b = on which vector, c,d = at which point/direction.
    - (b) Mathematical: This is the standard coordinate formula from differential geometry. The derivative terms measure the change in Christoffel symbols (connection coefficients), and the product terms account for the connection's non-linearity. Summing over k contracts one index.
    - (c) Lean: noncomputable because of deriv. dCoord applies derivatives to the Christoffel function (r,θ) ↦ Γ^a_bd(r,θ). sumIdx is a finite sum over the 4 indices {t,r,θ,φ}. Γtot is the unified Christoffel lookup table.

  **Block 14: Riemann symmetries (antisymmetry, pair exchange)**
  **Block 15: Riemann_last_equal_zero (first Bianchi identity consequence)**

  (5-6 blocks)

- **3.4.5 Six Component Reduction Lemmas** (8-10 pages)

  **THE CORE OF THE FORMALIZATION**

  **Block 16: Riemann_trtr_reduce**
  ```lean
  theorem Riemann_trtr_reduce (M r θ : ℝ) :
      Riemann M r θ Idx.t Idx.r Idx.t Idx.r
        = dCoord_r (fun r' _ => Γtot M r' θ Idx.t Idx.t Idx.r) r θ
        - dCoord_r (fun r' _ => Γtot M r' θ Idx.t Idx.r Idx.t) r θ
        + sumIdx (fun k => Γtot M r θ Idx.t Idx.t k * Γtot M r θ k Idx.r Idx.r)
        - sumIdx (fun k => Γtot M r θ Idx.t Idx.r k * Γtot M r θ k Idx.r Idx.t) := by
    unfold Riemann dCoord
    simp [sumIdx_expand]
    rfl
  ```

  - Math: R_trtr = ∂_r Γᵗ_tr - ∂_r Γᵗ_rt + Σ_k Γᵗ_tk Γᵏ_rr - Σ_k Γᵗ_rk Γᵏ_rt
  - Lean: (verbatim, condensed)
  - Proof narrative:
    - "Expand the definition of Riemann for indices (t,r,t,r)"
    - "The dCoord function evaluates: c=t gives 0, c=r gives ∂_r"
    - "Simplify the sums by expanding over all 4 indices"
    - "Definitional equality completes the proof"
  - Triple discussion:
    - (a) Physical: R_trtr measures the curvature in the (t,r) plane. This is the time-radial component, capturing how time dilation varies with radius. For Schwarzschild, this is entirely due to the mass M, and it's positive (focusing, not defocusing). The final value 2M/r³ shows the tidal force falls off as r⁻³, the Newtonian regime.
    - (b) Mathematical: Reduction from 4-index tensor to concrete formula. The antisymmetry R_trtr = -R_rttr is implicit. Many Γ terms vanish due to the diagonal metric and spherical symmetry. The sum over k has only a few non-zero contributions.
    - (c) Lean: unfold expands definitions literally. simp applies simp lemmas (like sumIdx_expand to enumerate the sum explicitly). rfl checks definitional equality (no proof needed beyond normalization). This is a "structural" lemma—it doesn't compute the final value, just reduces the form.

  **Block 17: Riemann_tθtθ_reduce**
  **Block 18: Riemann_tφtφ_reduce**
  **Block 19: Riemann_rθrθ_reduce**
  **Block 20: Riemann_rφrφ_reduce**
  **Block 21: Riemann_θφθφ_reduce**

  (Each of these 6 blocks gets FULL treatment with Math/Lean/Proof/Triple. This is ~8-10 pages total, the heart of the formalization.)

- **3.4.6 Component Value Lemmas** (5-6 pages)

  **Block 22: Riemann_trtr_value**
  ```lean
  theorem Riemann_trtr_value (M r θ : ℝ) (h_ext : Exterior M r θ) :
      Riemann M r θ Idx.t Idx.r Idx.t Idx.r = 2*M / r^3 := by
    classical
    have hr : r ≠ 0 := Exterior.r_ne_zero h_ext
    have hf : f M r ≠ 0 := Exterior.f_ne_zero h_ext
    unfold Riemann dCoord
    simp [sumIdx_expand, Γtot]
    rw [deriv_Γ_t_tr_at M r hr hf ...]
    field_simp [hr, hf, f]
    ring
  ```

  - Math: In the exterior, R_trtr = 2M/r³
  - Lean: (verbatim, condensed)
  - Proof narrative:
    - "We work in the Exterior domain, ensuring r ≠ 0 and f ≠ 0"
    - "Expand the Riemann tensor definition and directional derivatives"
    - "Simplify sums by enumerating indices and apply Γtot lookup"
    - "Most Γ terms are zero; only Γᵗ_tr contributes"
    - "Apply the derivative calculator deriv_Γ_t_tr_at"
    - "Clear denominators and simplify algebraically"
    - "Polynomial ring tactic completes the identity"
  - Triple discussion:
    - (a) Physical: The value 2M/r³ is the curvature in the (t,r) plane. At large r, this behaves like M/r³, matching Newtonian tidal forces (∼ GM/r³). Near the horizon (r → 2M), this grows like M/(2M)³ = 1/(8M²), finite and well-defined. The curvature is non-zero everywhere in the exterior, confirming that spacetime is curved by the mass M.
    - (b) Mathematical: This is a concrete numerical value (up to parameters M, r). The computation involves derivatives, sums, and algebraic simplification. The result is a rational function of r, smooth for r > 2M. This demonstrates that the Riemann tensor is explicitly computable for the Schwarzschild metric.
    - (c) Lean: classical tactic enables classical reasoning (not needed here, but harmless). have statements extract non-vanishing conditions from Exterior. unfold/simp reduce to concrete terms. rw applies the derivative lemma. field_simp clears all denominators. ring solves polynomial equations. This proof is ~10 lines, remarkably short given the complexity of the Riemann tensor formula.

  **Block 23: Riemann_tθtθ_value (M/r)**
  **Block 24: Riemann_tφtφ_value (M/r)**
  **Block 25: Riemann_rθrθ_value (M/r)**
  **Block 26: Riemann_rφrφ_value (M/r)**
  **Block 27: Riemann_θφθφ_value (2Mr²sin²θ)**

  (Each gets full treatment, ~5-6 pages)

- **3.4.7 Ricci Tensor via Contraction** (3-4 pages)

  **Block 28: Ricci definition and contraction**
  **Block 29: Ricci_tt_vanishes**
  **Block 30: Ricci_rr_vanishes**
  **Block 31: Ricci diagonal vanishing (all components)**

  (Full proofs with cancellation explanations)

- **3.4.8 Supporting Lemmas and Helpers** (3-4 pages)

  **Block 32: sumIdx infrastructure**
  **Block 33: Metric diagonal collapse lemmas**
  **Block 34: Christoffel-metric collapse lemmas**
  **Block 35: Metric compatibility (dCoord_g_via_compat_ext)**

  (These enable the main proofs)

**Estimated Writing Time:** 40-50 hours

---

### 3.5 Kretschmann Invariant Code (10-12 pages)

**Content:** Block-by-block walkthrough of Invariants.lean

- **3.5.1 Kretschmann Definition** (2-3 pages)

  **Block 1: Kretschmann definition**
  **Block 2: raise4_R helper**
  **Block 3: Diagonal reduction**

- **3.5.2 Six-Block Infrastructure** (3-4 pages)

  **Block 4: sixBlock definition**
  **Block 5: sumSixBlocks**
  **Block 6: Kretschmann_six_blocks theorem**

- **3.5.3 Block Value Calculations** (4-5 pages)

  **Block 7: sixBlock_tr_value (4M²/r⁶)**
  ```lean
  lemma sixBlock_tr_value (M r θ : ℝ) (hM : 0 < M) (hr : 2*M < r) (hθ : 0 < θ ∧ θ < Real.pi) :
    sixBlock M r θ Idx.t Idx.r = 4 * M^2 / r^6 := by
    classical
    unfold sixBlock
    simp only [Riemann_trtr_reduce, g, gInv, dCoord_r]
    simp only [Γtot]
    rw [deriv_Γ_t_tr M r ...]
    simp [Γ_t_tr, Γ_r_rr, f, one_div, inv_pow]
    field_simp [...]
    ring
  ```

  - Math: (g^tt g^rr)² (R_trtr)² = 4M²/r⁶
  - Lean: (verbatim, condensed)
  - Proof narrative:
    - "Expand sixBlock definition: (g^tt g^rr)² (R_trtr)²"
    - "Apply structural reduction for R_trtr"
    - "Substitute metric inverses: g^tt = -1/f, g^rr = f"
    - "Apply derivative of Γᵗ_tr"
    - "Evaluate Christoffel symbols and f"
    - "Clear denominators and compute the square"
    - "Polynomial simplification yields 4M²/r⁶"
  - Triple discussion:
    - (a) Physical: This block contributes the MOST to the Kretschmann scalar (factor 4 vs 1 for the other blocks). The (t,r) plane is where the gravitational field is strongest in the radial direction. The r⁻⁶ falloff is characteristic of tidal forces squared.
    - (b) Mathematical: Squaring the Riemann component and the metric factors. The computation is purely algebraic after the derivatives are evaluated. The factor 4 comes from the index pair multiplicity.
    - (c) Lean: Structural reduction exposes the relevant Riemann component. simp evaluates metric and Christoffel lookups. field_simp is essential for rational expressions. ring handles the polynomial algebra.

  **Block 8: sixBlock_tθ_value (M²/r⁶)**
  **Block 9: sixBlock_tφ_value (M²/r⁶)**
  **Block 10: sixBlock_rθ_value (M²/r⁶)**
  **Block 11: sixBlock_rφ_value (M²/r⁶)**
  **Block 12: sixBlock_θφ_value (4M²/r⁶)**

- **3.5.4 Final Kretschmann Theorem** (1-2 pages)

  **Block 13: Kretschmann_exterior_value (48M²/r⁶)**
  ```lean
  theorem Kretschmann_exterior_value (M r θ : ℝ) (hM : 0 < M) (hr : 2*M < r) (hθ : 0 < θ ∧ θ < Real.pi) :
    Kretschmann M r θ = 48 * M^2 / r^6 := by
    classical
    rw [Kretschmann_six_blocks]
    unfold sumSixBlocks
    rw [sixBlock_tr_value M r θ hM hr hθ, sixBlock_tθ_value M r θ hM hr hθ, ...]
    ring
  ```

  - Math: K = 48M²/r⁶
  - Lean: (verbatim, condensed)
  - Proof: Apply six-block decomposition, substitute all block values, arithmetic
  - Triple discussion:
    - (a) Physical: This is THE signature result for Schwarzschild spacetime. K diverges as r → 0 (true singularity at r=0). K is finite at r = 2M (horizon is only a coordinate singularity). Matches MTW Box 31.2 exactly.
    - (b) Mathematical: Sum of six rational functions with a common denominator. The coefficients (4,1,1,1,1,4) reflect the symmetry structure. The total factor 48 = 4×12 is memorable.
    - (c) Lean: rw chain substitutes lemmas. ring does the final arithmetic. This top-level theorem is just 5 lines because all the work is in the block lemmas.

**Estimated Writing Time:** 15-18 hours

---

### 3.6 EPS Framework Code (8-10 pages)

**Content:** Block-by-block walkthrough of EPSCore.lean

- **3.6.1 Light Rays and Free Fall** (2-3 pages)

  **Block 1: LightRay structure**
  **Block 2: FreeFall structure**

- **3.6.2 EPS Axioms** (3-4 pages)

  **Block 3: EPS_Light_Conformal**
  **Block 4: EPS_FreeFall_Projective**
  **Block 5: EPS_Compatibility**
  **Block 6: EPS_Integrability**

- **3.6.3 Height 0 Certificate** (2-3 pages)

  **Block 7: EPS_Height_Zero theorem**
  - Math: EPS reconstruction is portal-free
  - Lean: (theorem statement and proof sketch)
  - Proof: No Zorn, no compactness, no LEM needed
  - Triple discussion:
    - (a) Physical: GR can be grounded in observables (light, free-fall) without abstract axioms
    - (b) Mathematical: Constructive differential geometry is possible for this fragment
    - (c) Lean: Schematic proof (axioms as placeholders), structural certification

**Estimated Writing Time:** 12-15 hours

---

### 3.7 Build System Verification (5-6 pages)

**Content:**

- **3.7.1 Lake Build Configuration** (1-2 pages)
  - lakefile.lean structure
  - Dependency resolution
  - Toolchain pinning (lean-toolchain file)

- **3.7.2 CI/CD Pipeline** (2-3 pages)
  - GitHub Actions workflow
  - No-sorry guards
  - Axiom audits (SchematicAudit.sh, AxiomDeclAudit.sh)
  - Smoke tests

- **3.7.3 Verification Ledger** (2 pages)
  - all_certificates list
  - Profile computation tests
  - Reproducibility box (from current paper)

**Estimated Writing Time:** 8-10 hours

---

**PART 3 TOTAL PAGES:** 70-90
**PART 3 TOTAL WRITING TIME:** 115-145 hours

---

## PART 4: INSIGHTS AND REFLECTIONS (25-30 pages)

**Purpose:** Human perspective on the formalization journey, AI collaboration, and lessons learned

### 4.1 AI Collaboration Examples (6-8 pages)

**Content:**
- **4.1.1 Claude Code: Implementation and Repository Management** (2-3 pages)
  - Role: Primary coder, file operations, git management
  - Example 1: Christoffel derivative calculators (calc-chain pattern)
  - Example 2: Summand-first collapse strategy for alternation_dC_eq_Riem
  - Example 3: Repository organization and backup management
  - Strengths: Systematic, persistent, follows instructions precisely
  - Limitations: Needs clear direction, can get stuck in local optima

- **4.1.2 GPT-4o: Junior Tactics Professor** (2 pages)
  - Role: Lean tactic expert, proof strategy advisor
  - Example 1: "Use field_simp AFTER you've reduced the sums, not before"
  - Example 2: "Calc chains avoid simpa using... type mismatch issues"
  - Example 3: Debugging simp recursion depth errors
  - Strengths: Deep Lean 4 knowledge, tactical creativity
  - Limitations: Sometimes over-optimizes, needs context grounding

- **4.1.3 Gemini 2.5 Pro Deep Think: Strategic Guidance** (2-3 pages)
  - Role: High-level architect, mathematical strategist
  - Example 1: "The false lemma RiemannUp_first_equal_zero is blocking progress—components are non-zero, they just cancel algebraically"
  - Example 2: Six-block decomposition strategy for Kretschmann
  - Example 3: Structural Certification vs Foundational Verification distinction
  - Strengths: Big-picture thinking, mathematical insight, identifies foundational issues
  - Limitations: Less familiar with Lean syntax details

- **4.1.4 Multi-Agent Problem Solving Patterns** (1-2 pages)
  - Workflow: Gemini (strategy) → Claude (implementation) → GPT (debugging)
  - Iteration cycles: Try → fail → diagnose → retry
  - Handoff documents (SESSION_HANDOFF_OCT6_2025.md)
  - Version control as communication medium
  - Human oversight: course corrections, priority setting

**Estimated Writing Time:** 10-12 hours

---

### 4.2 Mathematical Insights (6-8 pages)

**Content:**
- **4.2.1 What We Learned from Formalization** (2-3 pages)
  - The Riemann tensor is MORE complex than textbooks suggest
    - 256 terms, most vanish, but tracking each one is essential
    - Symmetries are not just conveniences—they're structural necessities
  - Diagonal metrics simplify enormously (off-diagonal would be intractable)
  - The f(r) factor's ubiquity: appears in metrics, Christoffels, derivatives, everywhere
  - Cancellation is NOT simplification: R_tt = 0 because +terms and -terms cancel, not because each term is 0

- **4.2.2 Surprising Challenges** (2-3 pages)
  - **Challenge 1:** Derivative calculators
    - Naive approach: simpa using [all lemmas] → type mismatch
    - Solution: calc chains with explicit steps
    - Lesson: Lean 4 type inference is fragile at high complexity

  - **Challenge 2:** Nested sum explosion
    - Problem: 4 nested sums = 256 terms, comm/assoc search times out
    - Solution: Domain-specific collapse lemmas (use diagonal structure FIRST)
    - Lesson: General tactics (abel, ring) need help from mathematical structure

  - **Challenge 3:** The false lemma incident
    - Believed R^a_cad = 0 due to index repetition
    - Senior professor corrected: "Those components are NON-ZERO, just cancel in the sum"
    - Lesson: Formalization exposes hidden assumptions

- **4.2.3 Mathematical Patterns Discovered** (2 pages)
  - **Pattern 1:** Christoffel identities
    - Γʳ_rr = -Γᵗ_tr (exact negative)
    - Γᶿ_rθ = 1/r (independent of M)
    - These are not accidents—they follow from metric diagonality and symmetry

  - **Pattern 2:** r⁻³ vs r⁻⁶ falloff
    - Riemann components: r⁻³ (or r⁻¹ for some)
    - Kretschmann scalar: r⁻⁶ (squared)
    - Physical meaning: tidal force vs tidal force squared

  - **Pattern 3:** Six-block structure
    - 256 terms → 6 independent blocks (by symmetry)
    - Factor 4 multiplicity from ordering
    - Algebraic identity: 48 = 4×(4+1+1+1+1+4)

**Estimated Writing Time:** 10-12 hours

---

### 4.3 Physical Insights (6-8 pages)

**Content:**
- **4.3.1 GR Understanding Deepened by Formalization** (2-3 pages)
  - **Horizon vs singularity distinction** is SHARP in the formalism
    - At r = 2M: f = 0, metric components diverge, but Kretschmann finite (K = 48M²/(2M)⁶ = 3/(4M⁴))
    - At r = 0: Kretschmann diverges (K → ∞), true curvature singularity
    - Coordinate singularities can be transformed away; curvature singularities cannot

  - **Symmetry is not just simplification—it's physics**
    - Static (∂_t = 0): time translation symmetry → energy conservation
    - Spherical (∂_φ = 0, simple θ dependence): rotational symmetry → angular momentum conservation
    - These symmetries constrain the solution space massively

  - **Vacuum doesn't mean empty—it means no matter**
    - R_μν = 0 (Ricci vanishes) but R^a_bcd ≠ 0 (Riemann non-zero)
    - Spacetime is curved even in vacuum
    - The source of curvature is the boundary condition (mass M at r = 0)

- **4.3.2 Schwarzschild Geometry Insights** (2 pages)
  - **The f(r) = 1 - 2M/r factor is the key to everything**
    - g_tt = -f: time dilation (clocks slow near horizon)
    - g_rr = 1/f: radial stretching (distances expand near horizon)
    - These are inverse, ensuring the signature stays Lorentzian

  - **Christoffel symbols encode gravitational acceleration**
    - Γᵗ_tr = M/(r(r-2M)): time-radial coupling (time flows differently at different radii)
    - Γʳ_rr = -M/(r(r-2M)): radial self-connection (radial basis vector changes along radial direction)
    - These directly relate to the Newtonian potential Φ = -M/r in the weak-field limit

- **4.3.3 Curvature and Geodesics** (2-3 pages)
  - **Geodesic equation:** d²x^μ/dτ² + Γ^μ_αβ (dx^α/dτ)(dx^β/dτ) = 0
    - Christoffel symbols are the "gravitational force" terms
    - For Schwarzschild: radial geodesics curve inward (attraction)
    - Null geodesics (light): bent by gravity (gravitational lensing)

  - **Tidal forces from Riemann tensor**
    - Geodesic deviation equation: D²ξ^a/Dτ² = R^a_bcd u^b ξ^c u^d
    - R_trtr = 2M/r³: radial tidal stretching
    - Physical meaning: two nearby free-falling particles separate due to curvature

  - **Kretschmann scalar as curvature "strength"**
    - K = 48M²/r⁶: scalar measure of tidal force magnitude
    - Invariant under coordinate changes
    - Diverges at singularity, finite everywhere else

**Estimated Writing Time:** 10-12 hours

---

### 4.4 MTW Correlation (4-6 pages)

**Content:**
- **4.4.1 Misner/Thorne/Wheeler "Gravitation" Mapping** (2-3 pages)
  - **Our G1 (Schwarzschild vacuum) ↔ MTW Chapter 23, Box 23.1**
    - MTW gives the Schwarzschild metric and states R_μν = 0
    - Our verification: explicit computation in Lean
    - MTW trusts the reader; we machine-verify

  - **Our Kretschmann calculation ↔ MTW Box 31.2**
    - MTW: K = 48M²/r⁶ (stated without proof)
    - Our proof: 300 lines of Lean, six-block decomposition, every algebraic step
    - Confirms MTW's result

  - **Our Christoffel symbols ↔ MTW Table 23.1**
    - MTW lists the 9 non-zero symbols
    - Our Schwarzschild.lean: explicit definitions and derivative calculations
    - Perfect agreement

- **4.4.2 Conceptual Alignment** (1-2 pages)
  - **MTW's "geometrodynamics" philosophy**
    - "Spacetime tells matter how to move; matter tells spacetime how to curve"
    - Our formalization: makes this EXPLICIT in the Riemann and Einstein tensors

  - **MTW's "Track 1 vs Track 2"**
    - Track 1: Physical intuition and pictures
    - Track 2: Mathematical formalism
    - Our work: Track 2 at the highest rigor level

- **4.4.3 Differences and Extensions** (1 page)
  - MTW: Classical presentation, assumes axioms implicitly
  - Our work: EXPLICIT axiom tracking (AxCal)
  - MTW: Textbook proofs
  - Our work: Machine-verified proofs
  - MTW: Focuses on physics applications
  - Our work: Focuses on foundational structure

**Estimated Writing Time:** 6-8 hours

---

### 4.5 Re-explaining GR Post-Formalization (4-6 pages)

**Content:**
- **4.5.1 What Formalization Changes About Explanation** (1-2 pages)
  - **Before formalization:**
    - "The Riemann tensor measures curvature" (hand-wave)
    - "Compute some Christoffels, take derivatives, done"
    - Implicit: many steps skipped, symmetries assumed

  - **After formalization:**
    - "The Riemann tensor has 256 components, related by 4 symmetries, reducing to 20 independent in 4D, further to 6 for Schwarzschild by diagonal structure and spherical symmetry"
    - "Each component requires: 2 derivative calculations, 2 sum evaluations (4 terms each), and algebraic simplification with non-vanishing conditions"
    - Explicit: every step, every assumption, every dependency

- **4.5.2 Key Concepts Now Clearer** (2-3 pages)
  - **1. The metric is THE fundamental object**
    - Everything else (Christoffels, Riemann, Ricci, Einstein, Kretschmann) is DERIVED from the metric
    - g_μν → Γ^ρ_μν → R^ρ_σμν → R_μν → G_μν, K
    - Formalization makes this dependency chain crystal clear

  - **2. Coordinate singularities vs curvature singularities**
    - Coordinate singularity: metric components diverge, but curvature invariants finite
    - Curvature singularity: curvature invariants diverge
    - Formalization: explicit computation of K at r = 2M (finite) vs r = 0 (infinite)

  - **3. Vacuum ≠ flat**
    - Flat: R^a_bcd = 0 everywhere (Minkowski space)
    - Vacuum: R_μν = 0 but R^a_bcd ≠ 0 (Schwarzschild)
    - Riemann can be non-zero even when Ricci vanishes (Weyl curvature)

  - **4. Symmetry drastically reduces complexity**
    - 4D general metric: 10 independent components
    - Static, spherically symmetric: 2 independent functions (f(r) and r²)
    - Schwarzschild: 1 function (f(r) = 1 - 2M/r)
    - Without symmetry, this formalization would be impossible

- **4.5.3 New Pedagogical Approach** (1 page)
  - **Teach Schwarzschild as a CASE STUDY**
    - Start with symmetries (static, spherical)
    - Derive metric form
    - Compute Christoffels (9 non-zero)
    - Compute Riemann (6 non-zero)
    - Contract to Ricci (all zero)
    - Compute Kretschmann (48M²/r⁶)
    - Each step: explicit formulas, no hand-waving

  - **Emphasize computational structure**
    - Coordinate indices as enum {t,r,θ,φ}
    - Sums over finite sets
    - Diagonal matrices simplify MASSIVELY
    - Derivatives are univariate (by symmetry)

  - **Use formalization as a correctness check**
    - Textbook says R_tt = 0? Verify in Lean.
    - Paper claims K = 48M²/r⁶? Prove it formally.
    - Build trust through verification

**Estimated Writing Time:** 6-8 hours

---

**PART 4 TOTAL PAGES:** 25-30
**PART 4 TOTAL WRITING TIME:** 42-52 hours

---

---

## WRITING PLAN AND SEQUENCE

### Recommended Writing Order (with dependencies)

**Phase 1: Foundation (can be written in parallel)**
1. **Part 1.1-1.4** (AxCal basics) — 20-25 hours
2. **Part 2.1** (Schwarzschild derivation) — 12-15 hours
3. **Part 3.1** (File organization) — 12-15 hours

**Phase 2: AxCal Framework (sequential)**
4. **Part 1.5** (G1-G5 witness families) — 8-10 hours
5. **Part 1.6** (Literature) — 4-5 hours
6. **Part 3.2** (AxCal code) — 18-22 hours

**Phase 3: Mathematical Exposition (sequential)**
7. **Part 2.2** (Riemann tensor math) — 15-18 hours
8. **Part 2.3** (Ricci tensor math) — 10-12 hours
9. **Part 2.4** (Kretschmann math) — 10-12 hours

**Phase 4: Code Deep Dives (mostly parallel, but Schwarzschild before Riemann)**
10. **Part 3.3** (Schwarzschild code) — 30-35 hours
11. **Part 3.4** (Riemann code) — 40-50 hours
12. **Part 3.5** (Kretschmann code) — 15-18 hours
13. **Part 3.6** (EPS code) — 12-15 hours
14. **Part 3.7** (Build system) — 8-10 hours

**Phase 5: Insights (can be done in parallel after Phase 4)**
15. **Part 4.1** (AI collaboration) — 10-12 hours
16. **Part 4.2** (Mathematical insights) — 10-12 hours
17. **Part 4.3** (Physical insights) — 10-12 hours
18. **Part 4.4** (MTW correlation) — 6-8 hours
19. **Part 4.5** (Re-explaining GR) — 6-8 hours

**Phase 6: Integration and Polish**
20. **Abstract, Introduction, Conclusion** — 8-10 hours
21. **Bibliography** — 3-4 hours
22. **Cross-references, consistency checks** — 10-12 hours
23. **LaTeX formatting, figures, tables** — 8-10 hours
24. **Final proofreading** — 6-8 hours

---

## TIME ESTIMATES

### Total Writing Time by Part
- **Part 1:** 40-50 hours
- **Part 2:** 47-57 hours
- **Part 3:** 115-145 hours
- **Part 4:** 42-52 hours
- **Integration:** 35-44 hours

**TOTAL ESTIMATED TIME:** 279-348 hours

### At Different Work Rates
- **Full-time (8 hrs/day):** 35-44 working days (~7-9 weeks)
- **Half-time (4 hrs/day):** 70-87 days (~14-17 weeks)
- **Part-time (2 hrs/day):** 140-174 days (~20-25 weeks)

### Realistic Schedule (with revisions)
Assuming 4 hours/day focused writing:
- **Phase 1:** 2 weeks
- **Phase 2:** 1.5 weeks
- **Phase 3:** 2 weeks
- **Phase 4:** 5 weeks
- **Phase 5:** 2 weeks
- **Phase 6:** 2 weeks
- **Revisions and feedback:** 2 weeks

**TOTAL: 16-17 weeks (~4 months)**

---

## PAGE ALLOCATION SUMMARY

| Part | Subsections | Pages | Writing Hours |
|------|-------------|-------|---------------|
| **Part 1** | 6 | 25-30 | 40-50 |
| **Part 2** | 4 | 30-40 | 47-57 |
| **Part 3** | 7 | 70-90 | 115-145 |
| **Part 4** | 5 | 25-30 | 42-52 |
| **Total** | 22 | 150-190 | 244-304 |
| **+ Integration** | - | +10 | +35-44 |
| **GRAND TOTAL** | 22 | **160-200** | **279-348** |

---

## CONTENT REQUIREMENTS CHECKLIST

### Part 1 (AxCal Framework)
- [ ] Portal theory with formal definitions
- [ ] All 4 portals explained (Zorn, Limit-Curve, Serial-Chain, Reductio)
- [ ] Height certificate structure
- [ ] G1-G5 witness families
- [ ] Profile composition laws
- [ ] Structural Certification vs Foundational Verification distinction
- [ ] Literature anchors (Wald, Hawking-Ellis, Bishop-Bridges, etc.)

### Part 2 (Hand-Written Math)
- [ ] Schwarzschild metric derivation
- [ ] All 9 non-zero Christoffel symbols (explicit formulas)
- [ ] Riemann tensor definition and symmetries
- [ ] All 6 Schwarzschild Riemann components (full computation for 2+)
- [ ] Ricci tensor contraction (show cancellation for R_tt, R_rr)
- [ ] Kretschmann scalar six-block decomposition
- [ ] Final result K = 48M²/r⁶ (step-by-step)
- [ ] All in standard mathematical notation (not Lean code)

### Part 3 (Code Documentation)
For EACH code block:
- [ ] Mathematical statement (LaTeX)
- [ ] Lean code (verbatim from source)
- [ ] Proof narrative (tactics → English)
- [ ] Triple discussion: (a) Physical, (b) Mathematical, (c) Lean technical

**Minimum blocks required:**
- [ ] AxCal: 15-20 blocks (Axis, Portals, Witnesses, Certificates)
- [ ] Schwarzschild: 25-30 blocks
- [ ] Riemann: 35-40 blocks (including all 6 component lemmas)
- [ ] Invariants: 12-15 blocks (six-block calculations)
- [ ] EPS: 8-10 blocks
- [ ] Build: 5-6 blocks

**TOTAL: ~100-120 blocks with full triple discussion**

### Part 4 (Insights)
- [ ] AI collaboration: 3+ specific examples per agent (Claude, GPT-4o, Gemini)
- [ ] Multi-agent workflow description
- [ ] 3+ mathematical insights with formalization examples
- [ ] 3+ physical insights deepened by formalization
- [ ] MTW correlation: map at least 3 major results
- [ ] Post-formalization pedagogy: new approach to teaching GR

---

## SPECIAL REQUIREMENTS

### Verbatim Code Inclusion
- All Lean code must be copied EXACTLY from source files
- No paraphrasing or simplification of proofs
- Include line numbers or file references for traceability

### Mathematical Exposition ("by hands")
- Part 2 must use standard notation (∂, Γ, R, etc.)
- No Lean syntax in Part 2
- Full worked examples for at least 2 Riemann components
- Show every algebraic step in at least 1 Kretschmann block calculation

### Triple Discussion Format
For each code block in Part 3:
```
### Block N: [Name]

**Mathematical Statement:**
[LaTeX formula or statement]

**Lean Code:**
```lean
[verbatim code]
```

**Proof Narrative:**
[Convert tactics to English prose]

**Triple Discussion:**

**(a) Physical Implications:**
[What does this mean for spacetime, curvature, black holes, etc.?]

**(b) Mathematical Implications:**
[What does this prove mathematically, beyond GR?]

**(c) Lean Technical Discussion:**
[How does the proof work in Lean 4? Tactics? Dependencies?]
```

### MTW Cross-Referencing
- Identify at least 5 specific MTW sections/boxes/equations
- For each: state MTW's result, compare to our formalization
- Highlight differences (e.g., MTW hand-waves, we verify)

### AI Collaboration Documentation
- Include actual session excerpts or paraphrased dialogues
- Show version control commits as evidence
- Describe failure modes and recoveries
- Be honest about limitations and challenges

---

## DEPENDENCIES AND CRITICAL PATH

### Critical Path (must be done in order):
1. Part 1.1-1.3 (AxCal basics) → Part 1.5 (G1-G5) → Part 3.2 (AxCal code)
2. Part 2.1 (Schwarzschild math) → Part 3.3 (Schwarzschild code)
3. Part 2.2 (Riemann math) → Part 3.4 (Riemann code)
4. Part 2.4 (Kretschmann math) → Part 3.5 (Kretschmann code)
5. Parts 2 & 3 complete → Part 4 (Insights)

### Parallelizable Work:
- Part 1.4 (Pinned signature) can be written anytime
- Part 1.6 (Literature) can be written anytime
- Part 3.1 (File organization) can be written early
- Part 3.6 (EPS) and 3.7 (Build) are independent
- Part 4 subsections can be written in any order after Part 2 & 3

---

## ANTICIPATED CHALLENGES

### 1. Part 3 Scope Management
**Challenge:** 70-90 pages of code documentation is massive
**Mitigation:**
- Focus on representative blocks, not every single lemma
- Group similar lemmas (e.g., "Γ zero lemmas" as one block)
- Use appendices for exhaustive listings if needed

### 2. Mathematical Notation Consistency
**Challenge:** Converting Lean ↔ standard math notation
**Mitigation:**
- Create a notation guide (appendix)
- Be consistent: always R^a_bcd (not R^{a}_{bcd} or R^a_{bcd})
- Use macros in LaTeX

### 3. Maintaining Physical Intuition
**Challenge:** Getting lost in formalism
**Mitigation:**
- Every technical section: start with "Why does this matter physically?"
- Include concrete numbers: K at r=3M, r=10M, etc.
- Relate to observable phenomena (gravitational lensing, time dilation)

### 4. AI Collaboration Description
**Challenge:** Being honest without being dismissive
**Mitigation:**
- Frame as "case study" not "AI did everything"
- Emphasize human direction and oversight
- Describe failures and corrections
- Give credit appropriately

### 5. MTW Correlation Depth
**Challenge:** MTW is 1,200 pages; our focus is narrow
**Mitigation:**
- Focus on Chapters 23 (Schwarzschild), 31 (Curvature)
- Use Box 23.1, Box 31.2, Table 23.1
- Acknowledge scope: "We verify these specific results, not all of MTW"

---

## SUCCESS METRICS

### Minimum Viable Product (MVP)
- [ ] 150 pages total
- [ ] All 4 parts present
- [ ] All G1-G5 witness families documented
- [ ] At least 60 code blocks with triple discussion
- [ ] Hand-written math for Schwarzschild, Riemann, Kretschmann
- [ ] AI collaboration documented
- [ ] MTW correlation for 3+ results

### Stretch Goals (for 200 pages)
- [ ] 100+ code blocks with triple discussion
- [ ] Extended AI collaboration examples (10+ pages)
- [ ] Detailed MTW correlation (8+ pages)
- [ ] Appendices: notation guide, full theorem list, extended proofs
- [ ] Figures/diagrams (Penrose diagrams, curvature visualizations)

### Quality Metrics
- [ ] Every major mathematical claim has a Lean reference
- [ ] Every code block includes file path and line numbers
- [ ] Physical intuition in every technical section
- [ ] Consistent notation throughout
- [ ] Bibliography complete (20+ references)
- [ ] Proofread and LaTeX-compiled without errors

---

## ADDITIONAL RECOMMENDATIONS

### 1. Use LaTeX \input for Modularity
Structure the LaTeX source as:
```
Paper5_GR_AxCal_Extended.tex (main file)
  \input{part1_axcal_framework.tex}
  \input{part2_mathematical_exposition.tex}
  \input{part3_code_documentation.tex}
  \input{part4_insights.tex}
```

This allows:
- Parallel writing of different parts
- Easier version control
- Faster compilation during drafting

### 2. Create a Code → LaTeX Automation Script
For Part 3, consider:
- Script to extract Lean definitions/theorems with line numbers
- Auto-generate skeleton LaTeX blocks
- Human fills in narratives and triple discussions

### 3. Maintain a "Writing Log"
Track:
- Hours spent per section
- Completion percentage
- Blockers and resolutions
- Ideas for future expansion

### 4. Plan for Revisions
First draft ≠ final draft. Budget:
- **20%** of writing time for first-pass revisions
- **10%** for peer feedback incorporation
- **5%** for final polish

### 5. Consider Supplementary Materials
Beyond the paper:
- **GitHub repo README** with extended build instructions
- **Jupyter notebooks** with numerical Schwarzschild calculations (Python/Julia)
- **Video walkthrough** of a key proof (e.g., Riemann_trtr_reduce)
- **Interactive web demo** (Lean playground with Schwarzschild code)

---

## FINAL RECOMMENDATIONS

### Before Starting
1. **Read MTW Chapters 23 & 31 thoroughly** (reference during writing)
2. **Print out Schwarzschild.lean, Riemann.lean, Invariants.lean** (annotate)
3. **Set up LaTeX template** with all macros and structure
4. **Create outline in LaTeX** (section headings, page targets)

### During Writing
5. **Write in focused 2-4 hour blocks**
6. **Start each session with "What's the goal today?"**
7. **End each session with "What's next?"**
8. **Commit progress to git daily**

### Quality Control
9. **Peer review Part 1 early** (foundational concepts)
10. **Self-review Part 3 blocks for completeness** (all 3 discussion parts?)
11. **Check MTW cross-references for accuracy**
12. **Run LaTeX spell-check and grammar tools**

### Completion
13. **Compile full PDF early and often**
14. **Test build reproducibility** (fresh LaTeX environment)
15. **Archive all source files** (Lean code snapshots, LaTeX sources)
16. **Prepare a 1-page summary** (for quick reference)

---

## APPENDICES TO INCLUDE IN FINAL PAPER

### Appendix A: Notation Guide
- Lean ↔ Mathematical notation dictionary
- Index conventions (a,b,c,d vs μ,ν,ρ,σ)
- Summation notation

### Appendix B: Full Theorem List
- Every theorem/lemma in Schwarzschild.lean (with line numbers)
- Every theorem/lemma in Riemann.lean
- Every theorem/lemma in Invariants.lean
- Categorized by purpose (derivatives, components, vanishing, etc.)

### Appendix C: Axiom Audit Report
- Output of #print axioms for key theorems
- Discussion of Classical.choice dependencies
- Justification for Structural Certification methodology

### Appendix D: Extended MTW Correlation Table
| Our Result | Lean Theorem | MTW Reference | Agreement |
|------------|--------------|---------------|-----------|
| f(r) = 1-2M/r | f definition | Ch. 23 | ✓ |
| ... | ... | ... | ... |

### Appendix E: AI Collaboration Timeline
- Commit history with agent attribution
- Session handoff documents
- Key decision points and who made them

---

## CONCLUSION OF OUTLINE

This outline provides:
1. ✅ **Complete section/subsection breakdown** for all 4 parts
2. ✅ **Page estimates** for each section (totaling 150-200 pages)
3. ✅ **Content requirements** for each section (what to include)
4. ✅ **Major code blocks** from each file for Part 3 documentation
5. ✅ **Writing plan** with recommended order and dependencies
6. ✅ **Time estimates** (279-348 hours, ~4 months at 4 hrs/day)

**Next Steps:**
1. Review this outline with collaborators/advisors
2. Adjust page allocations based on priorities
3. Set up LaTeX structure
4. Begin Phase 1 writing (AxCal basics, Schwarzschild math, File organization)
5. Track progress against time estimates
6. Revise outline as needed during writing

**This outline is a living document.** Update it as the writing progresses, actual page counts emerge, and new insights suggest different emphases.

---

**Prepared:** October 2025
**For:** Paper 5 Restructuring Project
**Estimated Completion:** February-March 2026 (at 4 hrs/day pace)
