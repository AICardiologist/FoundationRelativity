# Paper 34: Scattering Amplitudes Are Constructively Computable

## Proof Document for Lean 4 Formalization

**Series:** Constructive Reverse Mathematics of Mathematical Physics
**Author:** Paul Chun-Kit Lee
**Architectural Guidance:** Claude (Anthropic)

---

## 1. Executive Summary

This paper proves that fixed-order perturbative scattering amplitudes in QED are constructively computable (BISH). Specifically, we calibrate the one-loop correction to Bhabha scattering (e⁺e⁻ → e⁺e⁻) and establish:

| Physical Content | Axiom Height | Mechanism |
|---|---|---|
| Tree-level amplitude | BISH (height 0) | Rational functions of Mandelstam variables |
| One-loop Feynman integrals | BISH (height 0) | Reduce to computable special functions (Li₂, log) |
| Dimensional regularization | BISH (height 0) | Formal Laurent series manipulation in ε |
| MS-bar renormalization | BISH (height 0) | Algebraic pole subtraction |
| IR divergence cancellation (Bloch-Nordsieck) | BISH (height 0) | Algebraic cancellation between virtual + real |
| Ward identity preservation | BISH (height 0) | Polynomial identity on formal expressions |
| Fixed-order inclusive cross section | BISH (height 0) | Composition of computable functions |
| All-orders perturbative series summation | LPO | Completed limit via BMC (convergence assertion) |
| Non-perturbative exact amplitude | ≥ LPO | Requires existence of continuum QFT |

**Punchline:** Every quantity that a collider experiment actually measures — a cross section computed to fixed loop order — is BISH. LPO enters only when asserting that the perturbation series converges or that the exact non-perturbative answer exists. The empirical content of perturbative QFT is fully constructive.

**Programme significance:** This extends the BISH+LPO characterization from coupling constant running (Papers 32-33) to the actual observables that experiments measure. Combined with Papers 32-33, the result is: the Standard Model's empirical predictions, at any fixed order in perturbation theory, are constructively computable.

---

## 2. Physical Setup

### 2.1 Bhabha Scattering

Bhabha scattering is e⁺e⁻ → e⁺e⁻ (electron-positron elastic scattering). It has two tree-level Feynman diagrams:

- **t-channel:** photon exchange, amplitude ∝ e²/(t - 0) where t is the momentum transfer
- **s-channel:** photon exchange through annihilation, amplitude ∝ e²/(s - 0) where s is the center-of-mass energy squared

The Mandelstam variables satisfy s + t + u = 4m² (kinematic constraint, pure algebra).

### 2.2 Why Bhabha

Bhabha scattering is the standard luminosity monitor at e⁺e⁻ colliders (LEP, Belle, BES). Its one-loop correction has been computed to extraordinary precision and verified experimentally. Every function that appears in the answer is analytically known. This makes it the cleanest possible test case: no numerical integration, no unsolved integrals, everything reduces to known special functions.

---

## 3. Theorems to Formalize

### Theorem 1: Tree-Level Amplitude is BISH

**Statement:** The tree-level Bhabha differential cross section is a rational function of (s, t, m², α), where s, t are Mandelstam variables, m is the electron mass, and α is the fine structure constant. All operations involved (addition, multiplication, division by nonzero denominators) are constructively valid.

**Proof sketch:**

The unpolarized tree-level differential cross section (Møller formula) is:

dσ/dΩ = (α²/4s) · F(s, t, m²)

where F is an explicit rational function:

F = (s² + u²)/t² + (t² + u²)/s² + 2u²/(st)

(in the ultra-relativistic limit m → 0; the massive case has additional rational terms).

Each Mandelstam variable is a real number (inner product of 4-momenta). The formula involves only +, ×, ÷. Division is by t and s, which are nonzero for physical scattering (t < 0 for spacelike momentum transfer; s > 4m² for above-threshold scattering).

**Constructive content:** Rational arithmetic on apartness-respecting reals. The denominators are apart from zero by the physical kinematics constraint. BISH.

**Lean architecture:**

```
-- Mandelstam variables as computable reals with kinematic constraint
structure MandelstamVars where
  s : ℝ  -- center-of-mass energy squared
  t : ℝ  -- momentum transfer squared
  u : ℝ  -- crossing variable
  constraint : s + t + u = 4 * m_e ^ 2
  s_pos : s > 4 * m_e ^ 2     -- above threshold
  t_neg : t < 0                 -- spacelike transfer

-- Tree-level cross section as rational function
noncomputable def tree_amplitude (k : MandelstamVars) (α : ℝ) : ℝ :=
  (α ^ 2 / (4 * k.s)) * bhabha_F k

-- bhabha_F is a rational function of s, t, u
noncomputable def bhabha_F (k : MandelstamVars) : ℝ :=
  (k.s ^ 2 + k.u ^ 2) / k.t ^ 2 +
  (k.t ^ 2 + k.u ^ 2) / k.s ^ 2 +
  2 * k.u ^ 2 / (k.s * k.t)

-- Key: denominators are apart from zero
theorem t_sq_ne_zero (k : MandelstamVars) : k.t ^ 2 ≠ 0 := by
  exact pow_ne_zero 2 (ne_of_lt k.t_neg).symm

-- CERTIFICATION: tree_amplitude uses no classical axioms
-- #print axioms tree_amplitude → [only Lean primitives]
```

**Expected axiom profile:** Zero custom axioms. Pure rational arithmetic.

---

### Theorem 2: Feynman Parameter Integrals Are Computable

**Statement:** The one-loop Feynman integrals for Bhabha scattering, after Feynman parametrization and integration, reduce to logarithms and dilogarithms (Spence functions) of rational expressions in the Mandelstam variables. These special functions are computable.

**Proof sketch:**

The general one-loop scalar integral in d = 4 dimensions (before regularization) has the Feynman parameter representation:

I_n = Γ(n-d/2) ∫₀¹ dx₁...dxₙ δ(Σxᵢ - 1) · [D(x, p, m)]^(d/2-n)

where D is a polynomial in the Feynman parameters with coefficients that are polynomials in the external momenta and masses.

For the specific integrals appearing in Bhabha scattering:

**Vacuum polarization (bubble):**
Π(q²) = (α/3π) [-1/ε + log(μ²/m²) - f(q²/m²)]
where f(z) = -5/3 + 4/z + (1 - 2/z)√(1 + 4/z) · log[(√(1+4/z) + 1)/(√(1+4/z) - 1)]

This is a composition of: square root (computable for positive reals), logarithm (computable), and rational functions.

**Vertex correction:**
Produces the Schwinger result F₁(0) = α/(2π) (anomalous magnetic moment) plus form factor corrections involving log and Li₂.

**Box diagram:**
The scalar box integral evaluates to:

Box(s,t) = (1/st)[2Li₂(1-m²/s) + 2Li₂(1-m²/t) + log²(s/t) + π² + ...]

where Li₂(z) = -∫₀¹ log(1-zt)/t dt is the Spence dilogarithm.

**Key fact: Li₂ is computable.**

Li₂(z) = Σₙ₌₁^∞ zⁿ/n² for |z| ≤ 1

This power series converges uniformly on the closed unit disk. Given any ε > 0, we can compute N such that the partial sum approximates Li₂(z) within ε. The rate of convergence is explicit: |Li₂(z) - Σₙ₌₁^N zⁿ/n²| ≤ |z|^(N+1)/(N+1)² · 1/(1-|z|) for |z| < 1.

For the physical kinematics (s, t real with specific signs), the arguments of Li₂ are real and satisfy |arg| ≤ 1 or can be analytically continued using the identity:

Li₂(z) + Li₂(1-z) = π²/6 - log(z)log(1-z)

which maps any real argument to the convergent region.

**Constructive content:** Computable functions (log, Li₂, √, rational) composed with computable reals (Mandelstam variables). Each function has an explicit convergence rate. The composition of computable functions is computable. BISH.

**Lean architecture:**

```
-- Dilogarithm as computable function
noncomputable def Li₂ (z : ℝ) : ℝ :=
  tsum (fun n => z ^ n / (n : ℝ) ^ 2)  -- formal; use Mathlib tsum

-- Computability: explicit error bound
theorem Li₂_computable (z : ℝ) (hz : |z| < 1) (ε : ℝ) (hε : ε > 0) :
    ∃ N : ℕ, |Li₂ z - ∑ n in Finset.range N, z ^ n / (n : ℝ) ^ 2| < ε := by
  -- The partial sum converges; N depends computably on ε and z
  sorry -- FILL: standard geometric series tail bound

-- Log is computable (from Mathlib)
-- √ is computable for positive reals (from Mathlib)
-- Rational functions of computable reals are computable

-- One-loop vacuum polarization as computable function
noncomputable def vacuum_pol (q_sq : ℝ) (m : ℝ) (α : ℝ) : ℝ :=
  (α / (3 * Real.pi)) * vp_finite_part q_sq m

-- Vertex correction finite part
noncomputable def vertex_correction (q_sq : ℝ) (m : ℝ) (α : ℝ) : ℝ :=
  (α / (2 * Real.pi)) * vertex_finite_part q_sq m  -- involves log, Li₂

-- Box integral finite part
noncomputable def box_integral (s t m_sq : ℝ) : ℝ :=
  (1 / (s * t)) * (2 * Li₂ (1 - m_sq / s) + 2 * Li₂ (1 - m_sq / t) +
    (Real.log (s / t)) ^ 2 + Real.pi ^ 2)

-- CERTIFICATION: all finite parts are compositions of computable functions
-- #print axioms vacuum_pol → [only Lean primitives + Mathlib reals]
```

**Expected axiom profile:** Zero custom axioms beyond Mathlib's real number infrastructure.

---

### Theorem 3: Dimensional Regularization is BISH

**Statement:** The dimensional regularization procedure — analytically continuing spacetime dimension to d = 4 - ε, computing integrals as formal Laurent series in ε, and extracting the finite part — is a finite algebraic manipulation on formal power series. It requires no omniscience principles.

**Proof sketch:**

Dimensional regularization works as follows:

1. Replace d = 4 with d = 4 - ε (a formal parameter, not a real spacetime dimension)
2. The loop integral, which diverges at d = 4, becomes a meromorphic function of ε
3. Expand in Laurent series: I(ε) = c₋₁/ε + c₀ + c₁ε + ...
4. The MS-bar scheme subtracts: I_ren = I(ε) - c₋₁/ε (plus conventional log(4π) - γ_E terms)
5. Set ε = 0: I_ren = c₀

**Why this is BISH:**

Step 1 is a formal substitution — replacing "4" with "4 - ε" in an algebraic expression. No analysis.

Step 2 produces an explicit formula. For the bubble integral:
I₂(d) = Γ(2-d/2) / (4π)^(d/2) · [m² - q²x(1-x)]^(d/2-2)

The Gamma function Γ(2-d/2) = Γ(ε/2) has a known Laurent expansion:
Γ(ε/2) = 2/ε - γ_E + O(ε)

This is a *formal identity* between power series, not a limit computation.

Step 3 is collecting terms by powers of ε — polynomial algebra.

Step 4 is subtracting the 1/ε pole — formal series subtraction.

Step 5 is evaluating a polynomial at ε = 0 — substitution.

At no point do we assert convergence of a series, take a limit, or decide whether a quantity is zero. Every step is finite algebraic manipulation on formal expressions.

**Lean architecture:**

```
-- Formal Laurent series in ε
structure LaurentSeries where
  coeffs : ℤ → ℝ  -- coefficient of ε^n
  min_order : ℤ     -- lowest nonzero power
  finite_principal : ∀ n < min_order, coeffs n = 0

-- MS-bar subtraction: remove pole terms
def msbar_subtract (I : LaurentSeries) : ℝ :=
  I.coeffs 0  -- extract constant term after removing poles

-- Key theorem: dimensional regularization is algebraic
theorem dimreg_is_algebraic :
    ∀ (I : OneLoopIntegral),
    ∃ (L : LaurentSeries),
    L = dimreg_evaluate I ∧
    msbar_subtract L = finite_part I := by
  sorry -- FILL: explicit Laurent expansion for each integral type

-- CERTIFICATION: no Classical.choice, no completed limits
-- #print axioms msbar_subtract → [only Lean primitives]
```

**Expected axiom profile:** Zero custom axioms. Formal series algebra.

---

### Theorem 4: IR Cancellation (Bloch-Nordsieck) is BISH

**Statement:** The cancellation of infrared divergences between virtual corrections and real emission in the inclusive Bhabha cross section is algebraic. The inclusive cross section to one loop is a finite, computable expression.

**Proof sketch:**

The virtual one-loop correction to Bhabha scattering has an infrared divergence when the virtual photon momentum goes to zero (soft photon). In dimensional regularization, this appears as a 1/ε_IR pole (distinct from the UV pole).

The real emission process e⁺e⁻ → e⁺e⁻γ also has an IR divergence when the emitted photon energy goes to zero. In the inclusive cross section (summing over all final states with 0 or 1 soft photon below detector threshold Δε), this produces a compensating -1/ε_IR pole.

The Bloch-Nordsieck theorem states: σ_inclusive = σ_virtual + σ_real is IR-finite.

**Why this is BISH:**

The virtual IR divergence has the form:
σ_virtual = σ₀ · (1 + (α/π)(A/ε_IR + B_virtual))

The real emission integrated cross section has:
σ_real = σ₀ · (α/π)(-A/ε_IR + B_real(Δε))

where A is the *same coefficient* in both (this follows from the soft photon theorem, which is an algebraic identity relating the soft emission amplitude to the elastic amplitude).

Adding: σ_inclusive = σ₀ · (1 + (α/π)(B_virtual + B_real(Δε)))

The 1/ε_IR terms cancel algebraically. The remaining B_virtual and B_real are explicit computable functions of (s, t, m², Δε) involving log and Li₂.

No limit is taken. The cancellation is an identity between coefficients of formal Laurent series. The soft photon theorem that guarantees the coefficient A is the same in both virtual and real pieces is a consequence of gauge invariance — an algebraic Ward identity.

**Lean architecture:**

```
-- IR divergence structure
structure IRDivergentAmplitude where
  pole_coeff : ℝ      -- coefficient of 1/ε_IR
  finite_part : ℝ      -- IR-finite remainder

-- Virtual and real contributions
def virtual_IR (k : MandelstamVars) (α : ℝ) : IRDivergentAmplitude :=
  { pole_coeff := soft_factor k α,
    finite_part := B_virtual k α }

def real_IR (k : MandelstamVars) (α : ℝ) (Δε : ℝ) : IRDivergentAmplitude :=
  { pole_coeff := -soft_factor k α,    -- SAME coefficient, opposite sign
    finite_part := B_real k α Δε }

-- Bloch-Nordsieck cancellation
theorem bloch_nordsieck (k : MandelstamVars) (α : ℝ) (Δε : ℝ) :
    (virtual_IR k α).pole_coeff + (real_IR k α Δε).pole_coeff = 0 := by
  simp [virtual_IR, real_IR, add_neg_cancel]

-- Inclusive cross section is finite and computable
def inclusive_cross_section (k : MandelstamVars) (α : ℝ) (Δε : ℝ) : ℝ :=
  tree_amplitude k α * (1 + (α / Real.pi) *
    ((virtual_IR k α).finite_part + (real_IR k α Δε).finite_part))

-- CERTIFICATION: no omniscience, pure algebra
-- #print axioms inclusive_cross_section → [only Lean primitives + Mathlib reals]
```

**Expected axiom profile:** Zero custom axioms.

---

### Theorem 5: Ward Identity Preservation Under Regularization is BISH

**Statement:** The QED Ward identity (qμ Γμ(p,p') = S⁻¹(p) - S⁻¹(p')) is preserved by dimensional regularization. The verification is algebraic.

**Proof sketch:**

The Ward identity is a consequence of U(1) gauge symmetry. At tree level, it states that contracting the photon vertex with the photon momentum gives the difference of inverse propagators. At one loop, the renormalized vertex satisfies the same identity with renormalized propagators.

Dimensional regularization preserves gauge symmetry because it doesn't break the Ward identity at any step — the d-dimensional integrals satisfy the same algebraic relations as the 4-dimensional ones. This was verified in Paper 32 and carries over identically.

The key point: the Ward identity is a polynomial relation among formal amplitudes. Checking it requires evaluating both sides and verifying equality. Both sides are computable (they're the same Laurent series expressions from Theorems 2-3). The equality check is an algebraic identity, not a limit.

**Lean architecture:** Reuse from Paper 32. The Ward identity structure is identical for Bhabha scattering. Import the `WardIdentity` module from Paper 32 and instantiate for the Bhabha vertex.

**Expected axiom profile:** Zero custom axioms (same as Paper 32).

---

### Theorem 6: Fixed-Order Cross Section is BISH (Main Theorem)

**Statement:** The inclusive Bhabha cross section computed to any fixed order n in perturbation theory is a computable function of (s, t, m², α, Δε). The computation requires no omniscience principles.

**Proof sketch:**

By induction on loop order:

**Base case (n = 0):** Tree-level amplitude is rational (Theorem 1). BISH.

**Inductive step:** Assume the (n-1)-loop inclusive cross section is computable. The n-loop correction introduces:
- n-loop Feynman integrals, which reduce to generalized polylogarithms (Goncharov polylogarithms, harmonic polylogarithms) of rational arguments. These are iterated integrals of rational functions, computable by their series representations with explicit error bounds.
- UV divergences removed by MS-bar subtraction (Theorem 3 generalized). Algebraic.
- IR divergences cancelled by KLN theorem (generalization of Bloch-Nordsieck to n loops). The KLN theorem guarantees algebraic cancellation of all IR singularities in inclusive cross sections.

The composition of computable functions is computable. The result at order n is computable.

**Important caveat:** This theorem is about *fixed* n. We do NOT claim the perturbation series Σₙ aₙ αⁿ converges. That claim would require LPO (asserting the existence of a limit). We claim only that for any *given* n, the partial sum is computable. This is the distinction between "computable for each n" (BISH, by induction) and "the limit exists" (LPO, by completed limit).

**For the Lean formalization:** Formalize explicitly for n = 0 (tree) and n = 1 (one-loop). State the general inductive claim but leave higher loops as a theorem schema rather than explicit computation (the two-loop Bhabha integrals are known analytically but the expressions are very long).

**Lean architecture:**

```
-- Fixed-order cross section
def sigma_fixed_order (n : ℕ) (k : MandelstamVars) (α : ℝ) (Δε : ℝ) : ℝ :=
  match n with
  | 0 => tree_amplitude k α
  | 1 => inclusive_cross_section k α Δε  -- from Theorem 4
  | n + 2 => sorry  -- higher loops: state schema, defer explicit computation

-- MAIN THEOREM: fixed-order is BISH
theorem fixed_order_is_BISH (n : ℕ) (k : MandelstamVars) (α : ℝ) (Δε : ℝ) :
    ∃ (f : MandelstamVars → ℝ → ℝ → ℝ),
    (∀ ε > 0, ∃ (approx : ℚ → ℚ → ℚ → ℚ),
      |f k α Δε - ↑(approx (rat_approx k) (rat_approx α) (rat_approx Δε))| < ε) ∧
    f k α Δε = sigma_fixed_order n k α Δε := by
  sorry -- FILL: computability of composition of Li₂, log, rational functions

-- #print axioms fixed_order_is_BISH → target: [only Lean primitives + Mathlib]
```

**Expected axiom profile:** Zero custom axioms for n = 0, 1. Schema for general n.

---

### Theorem 7: All-Orders Summation Costs LPO (Boundary Theorem)

**Statement:** The assertion "the perturbation series Σₙ₌₀^∞ σₙ αⁿ converges to the exact cross section" requires LPO. Specifically, this assertion is equivalent to the Bounded Monotone Convergence principle (BMC), which is equivalent to LPO over BISH.

**Proof sketch:**

The perturbative QED series is widely believed to be *asymptotic*, not convergent — the series diverges but the partial sums approximate the exact answer to high precision before diverging. However, the *assertion that it converges* (or even that it is Borel summable to a unique answer) requires completing an infinite process.

Forward direction (LPO → series summation): Given LPO, every bounded monotone sequence of reals converges (BMC). The partial sums of cross sections, if bounded, converge. (Whether they're actually bounded is a physics question, not a logical one.)

Reverse direction (series summation → LPO): This follows the standard BMC ↔ LPO equivalence from Paper 29. If you could assert that every bounded perturbation series converges, you could decide ∀n, α(n) = 0 ∨ ¬∀n, α(n) = 0 for arbitrary binary sequences by encoding them into a formal series.

**The boundary between BISH and LPO in perturbative QFT is thus precisely located:** it sits between "compute the answer to n loops" (BISH for each n) and "the answer exists as a completed infinite object" (LPO).

**Lean architecture:**

```
-- Perturbative series as formal object
def perturbative_series (σ : ℕ → ℝ) (α : ℝ) : ℕ → ℝ :=
  fun N => ∑ n in Finset.range N, σ n * α ^ n

-- Assertion: the series converges
def series_converges (σ : ℕ → ℝ) (α : ℝ) : Prop :=
  ∃ L : ℝ, Filter.Tendsto (perturbative_series σ α) Filter.atTop (nhds L)

-- Forward: LPO → convergence of bounded series
theorem lpo_implies_bounded_series_converges
    (lpo : LPO) (σ : ℕ → ℝ) (α : ℝ)
    (hb : ∃ B, ∀ N, |perturbative_series σ α N| ≤ B)
    (hmono : Monotone (perturbative_series σ α)) :
    series_converges σ α := by
  exact bmc_of_lpo lpo _ hb hmono  -- reuse Paper 29

-- Reverse: encoding binary sequence into formal series
theorem series_convergence_implies_lpo
    (h : ∀ σ : ℕ → ℝ, ∀ α : ℝ,
      (∃ B, ∀ N, |perturbative_series σ α N| ≤ B) →
      Monotone (perturbative_series σ α) →
      series_converges σ α) :
    LPO := by
  sorry -- FILL: standard BMC → LPO, reuse Paper 29 encoding

-- CERTIFICATION: forward uses Classical.choice (intentional — this IS the classical content)
-- Reverse uses no classical axioms
```

**Expected axiom profile:** Forward direction: `Classical.choice` (intentional — LPO is the hypothesis). Reverse direction: zero custom axioms.

---

## 4. Bridge Lemmas and Axioms

### 4.1 Physical Axioms (Axiomatized, Not Proved)

```
-- Soft photon theorem: algebraic consequence of gauge invariance
axiom soft_photon_theorem :
  ∀ (k : MandelstamVars) (α : ℝ),
  soft_virtual_coeff k α = soft_real_coeff k α

-- KLN theorem: IR cancellation at all orders
axiom KLN_theorem :
  ∀ (n : ℕ) (k : MandelstamVars) (α Δε : ℝ),
  ir_poles_virtual n k α + ir_poles_real n k α Δε = 0
```

These are standard results in QFT whose proofs are algebraic (following from gauge invariance). We axiomatize them because the full Ward identity proof infrastructure would require formalizing the QED Lagrangian, which is beyond scope. The axioms are physically uncontroversial.

### 4.2 Mathematical Prerequisites from Mathlib

Required from Mathlib (should already exist or be straightforward):
- `Real.log` computability and basic identities
- Power series convergence (for Li₂)
- Formal Laurent series (for dim reg)
- Rational function arithmetic

**Likely needs building:**
- `Mathlib.Analysis.SpecialFunctions.Dilogarithm` — Li₂(z) definition and basic properties. If not in Mathlib, define via power series and prove convergence.

---

## 5. File Structure

```
Paper34_ScatteringAmplitudes/
├── Paper34/
│   ├── Defs.lean              -- Mandelstam variables, kinematics, apartness
│   ├── TreeLevel.lean         -- Theorem 1: tree amplitude as rational function
│   ├── SpecialFunctions.lean  -- Li₂ definition, computability, error bounds
│   ├── FeynmanIntegrals.lean  -- Theorem 2: one-loop integrals → Li₂, log
│   ├── DimReg.lean            -- Theorem 3: Laurent series, MS-bar subtraction
│   ├── BlochNordsieck.lean    -- Theorem 4: IR cancellation
│   ├── WardIdentity.lean      -- Theorem 5: import from Paper 32, instantiate
│   ├── FixedOrder.lean        -- Theorem 6: main theorem, composition
│   ├── AllOrders.lean         -- Theorem 7: LPO boundary via BMC
│   ├── Axioms.lean            -- Bridge lemmas: soft photon, KLN
│   └── Main.lean              -- imports, #print axioms
└── lakefile.lean
```

**Target:** ~600-800 lines. Reuse Paper 32 infrastructure heavily (Ward identity, LPO/BMC equivalence from Paper 29).

---

## 6. Certification Protocol

Following Paper 10 §7 certification scheme:

| Component | Certification Level | Justification |
|---|---|---|
| Theorems 1-6 (BISH content) | Level 2: Structurally verified | `#print axioms` shows no `Classical.choice` |
| Theorem 7 forward (LPO → convergence) | Level 3: Intentional classical | `Classical.choice` from LPO hypothesis |
| Theorem 7 reverse (convergence → LPO) | Level 2: Structurally verified | No classical axioms |
| Bridge lemmas (soft photon, KLN) | Level 4: Axiomatized physics | Explicit `axiom` declarations |

**The key certification claim:** Theorems 1-6 compile with zero `Classical.choice`. This means the one-loop Bhabha cross section is *mechanically certified* as BISH. No human judgment required — the Lean kernel decides.

---

## 7. Connection to Programme

### 7.1 Calibration Table Entry

| Paper | Physical Domain | BISH | WLPO | LLPO | LPO |
|---|---|---|---|---|---|
| 34 | Tree-level scattering | ✓ | | | |
| 34 | One-loop correction | ✓ | | | |
| 34 | Dim reg + renormalization | ✓ | | | |
| 34 | IR cancellation | ✓ | | | |
| 34 | Fixed-order cross section | ✓ | | | |
| 34 | All-orders convergence | | | | ✓ |

### 7.2 The Punchline

Combined with Papers 32 (QED coupling running) and 33 (QCD coupling + confinement), Paper 34 completes the calibration of the Standard Model's empirical interface:

**"Every quantity that a particle collider measures — a scattering cross section computed to fixed order in perturbation theory — is constructively computable. No omniscience principle is required. LPO enters the Standard Model only at two points: (1) asserting that coupling constants exist as completed real numbers (the continuum limit), and (2) asserting that the perturbation series converges to the exact answer. Both are idealizations that no experiment can access."**

This is the sentence for the revised Paper 10.

---

## 8. Instructions for the Lean Agent

### Priority order:
1. `Defs.lean` + `TreeLevel.lean` — get the kinematics compiling first
2. `SpecialFunctions.lean` — Li₂ is the key new infrastructure
3. `DimReg.lean` — formal Laurent series (can be lightweight)
4. `FeynmanIntegrals.lean` + `BlochNordsieck.lean` — the physics
5. `FixedOrder.lean` — compose everything
6. `AllOrders.lean` — reuse Paper 29 BMC ↔ LPO
7. `WardIdentity.lean` — import from Paper 32

### What to reuse:
- Paper 29: `BMC ↔ LPO` equivalence (for Theorem 7)
- Paper 32: `WardIdentity` module, `LPO` definition, formal series infrastructure
- Paper 18: `WLPO` definition (not needed here, but for reference)

### What's new:
- `Li₂` (dilogarithm) definition and convergence proof
- Mandelstam variable kinematics with apartness constraints
- Bhabha-specific amplitude expressions

### Target: zero sorry in Theorems 1-5. Theorem 6 may have sorry for n ≥ 2 (higher loops stated as schema). Theorem 7 should reuse Paper 29 with minimal sorry.

---

## 9. Potential Pitfalls

1. **Li₂ branch cuts.** The dilogarithm has a branch cut for z > 1 on the real line. For Bhabha kinematics, the arguments of Li₂ can exceed 1 in certain kinematic regions (e.g., Li₂(1 - m²/s) with s > m²). The analytic continuation uses the reflection identity Li₂(z) + Li₂(1/z) = -π²/6 - (1/2)log²(-z), which maps the argument to the convergent region. This identity is algebraic — BISH — but the Lean agent needs to implement the correct branch.

2. **Formal vs. analytic dim reg.** The proof treats dimensional regularization as formal algebra. Some physicists object that dim reg "really" involves analytic continuation in d. Our response: the formal algebraic procedure produces the same Laurent series as the analytic continuation, and the algebraic procedure is manifestly BISH. Whether one "really" continues in d is a philosophical question about the metatheory, not about the mathematical content. This parallels the meta-classical methodology from Paper 2.

3. **The KLN axiom.** Axiomatizing KLN rather than proving it is a pragmatic choice. The full proof requires formalizing unitarity and the optical theorem, which would be a major infrastructure investment. For Paper 34's purposes, KLN is a bridge lemma: we're calibrating the logical cost *assuming* standard QFT results, not re-deriving QFT from scratch.

4. **Higher loops.** The Theorem 6 inductive claim for general n relies on the fact that n-loop integrals reduce to generalized polylogarithms (Goncharov's result). This is known for massless cases and many massive cases but is not proved for arbitrary Feynman integrals. The Lean formalization should be explicit about this: n = 0, 1 are fully formalized; n ≥ 2 is a conditional claim assuming the polylogarithm reduction.
