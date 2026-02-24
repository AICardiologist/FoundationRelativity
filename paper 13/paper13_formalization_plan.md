# Paper 13 Formalization Plan: The Event Horizon as a Logical Boundary

## Theorem Statement

**Main Result.** Over BISH, geodesic incompleteness in the Schwarzschild interior (the assertion that a radial timelike geodesic reaches r = 0 in finite proper time) is equivalent to LPO.

```
theorem schwarzschild_interior_geodesic_incompleteness_iff_LPO :
  SchwarzschildInteriorGeodesicIncompleteness ↔ LPO
```

This establishes that the event horizon at r = 2M is simultaneously a causal boundary (classical GR) and a logical boundary (constructive reverse mathematics): the exterior geometry is BISH, the interior's singularity assertion is LPO.

---

## Assumed Infrastructure (from Paper 6 / FoundationRelativity)

The following already exist in the codebase and should be imported, not rebuilt:

- **Schwarzschild metric components**: `g_tt`, `g_rr`, `g_θθ`, `g_φφ` as functions of `(M r θ : ℝ)`
- **Exterior domain predicate**: `Exterior M r θ` packaging `r > 2M`, `sin θ ≠ 0`, `M > 0`
- **Christoffel symbols**: `Γ` computed from metric, verified for exterior
- **Riemann tensor, Ricci tensor**: verified `R_μν = 0` (vacuum) for exterior
- **Kretschner scalar**: `K = 48 * M^2 / r^6`, verified constructively for `r > 0`
- **Axiom calibration infrastructure**: `#print axioms` methodology, Height certificates
- **LPO definition and equivalence machinery**: from Papers 7-8 (Ising model LPO equivalence)

---

## New Lean Code: Module Structure

### Module 1: Interior Domain (`GR/Interior/Domain.lean`)
**~80-120 lines**

Define the interior domain predicate mirroring the exterior one.

```lean
/-- Interior domain: 0 < r < 2M, M > 0 -/
structure Interior (M r : ℝ) : Prop where
  mass_pos : M > 0
  r_pos : r > 0
  r_inside : r < 2 * M
```

Key facts to prove:
- In the interior, `g_tt` and `g_rr` swap sign (the signature flip)
- `1 - 2M/r < 0` for `r < 2M` (makes `g_tt > 0` in signature `(-+++)`, i.e., r-direction becomes timelike)
- The metric components remain well-defined and finite for `0 < r < 2M`
- Kretschner scalar `K = 48M²/r⁶` is constructively computable for any `r` satisfying `Interior M r` (reuse existing exterior proof with weakened domain hypothesis — it only needs `r > 0`)

### Module 2: Radial Geodesic Equation (`GR/Interior/RadialGeodesic.lean`)
**~150-250 lines**

Formalize the radial timelike geodesic equation for a freely falling particle in the interior.

For a radial geodesic (θ = π/2, dθ/dτ = dφ/dτ = 0) of a massive particle with energy parameter E, the equation of motion is:

```
(dr/dτ)² = E² - (1 - 2M/r)
```

In the interior (r < 2M), the factor `(1 - 2M/r) < 0`, so `(dr/dτ)² = E² + |1 - 2M/r| > 0`. The particle necessarily moves in r (r is timelike). For infall, `dr/dτ < 0`.

Define:
```lean
/-- The radial geodesic equation in Schwarzschild interior.
    For a freely falling particle with energy parameter E ≥ 1 (dropped from rest at infinity),
    the proper time derivative of r satisfies this ODE. -/
def radial_geodesic_ODE (M E r : ℝ) : ℝ :=
  E^2 - (1 - 2 * M / r)

/-- dr/dτ is negative (infall) and bounded away from zero in the interior -/
theorem radial_velocity_negative (M E r : ℝ) (h_int : Interior M r) (h_E : E ≥ 1) :
  radial_geodesic_ODE M E r > 0 := by
  -- Since 1 - 2M/r < 0 in the interior, E² - (1 - 2M/r) = E² + |2M/r - 1| > 0
  sorry -- TO FORMALIZE
```

Key property: `r(τ)` is a **monotonically decreasing** function of proper time, bounded below by 0.

```lean
/-- Along an ingoing radial geodesic in the interior, r is monotonically
    decreasing as a function of proper time. -/
theorem r_monotone_decreasing (M E : ℝ) (h_M : M > 0) (h_E : E ≥ 1)
    (r : ℝ → ℝ) (h_geodesic : IsRadialGeodesic M E r)
    (h_interior : ∀ τ ∈ Set.Ioo τ₀ τ₁, Interior M (r τ)) :
  StrictAntiOn r (Set.Ioo τ₀ τ₁) := by
  sorry -- TO FORMALIZE

/-- r is bounded below by 0 along any geodesic -/
theorem r_bounded_below (r : ℝ → ℝ) (h_geodesic : IsRadialGeodesic M E r) :
  ∀ τ, r τ ≥ 0 := by
  sorry -- TO FORMALIZE: follows from r being a spatial coordinate
```

### Module 3: Geodesic Incompleteness Statement (`GR/Interior/Incompleteness.lean`)
**~50-80 lines**

State geodesic incompleteness precisely as a completed-limit assertion.

```lean
/-- Geodesic incompleteness: there exists a finite proper time τ* at which r = 0.
    This is the singularity assertion. -/
def GeodesicIncompleteness (M E : ℝ) (r : ℝ → ℝ) : Prop :=
  ∃ τ_star : ℝ, τ_star > 0 ∧ r τ_star = 0

/-- Alternative formulation via infimum: the bounded monotone sequence r(τ)
    attains its infimum 0 in finite parameter time. -/
def GeodesicIncompleteness' (M E : ℝ) (r : ℝ → ℝ) : Prop :=
  ∃ τ_star : ℝ, τ_star > 0 ∧ ∀ ε > 0, ∃ τ < τ_star, r τ < ε
```

The key insight: asserting `GeodesicIncompleteness` for a monotonically decreasing function bounded below by 0 is precisely **Bounded Monotone Convergence** — the assertion that a bounded monotone sequence converges to a definite limit.

### Module 4: LPO Equivalence — Forward Direction (`GR/Interior/LPO_Forward.lean`)
**~100-150 lines**

**GeodesicIncompleteness → LPO**

Strategy: Given the geodesic incompleteness assertion, construct an LPO oracle.

```lean
/-- If geodesic incompleteness holds for all Schwarzschild interiors,
    then LPO holds. -/
theorem geodesic_incompleteness_implies_LPO :
  (∀ M E r, M > 0 → E ≥ 1 → IsRadialGeodesic M E r →
    Interior M (r 0) → GeodesicIncompleteness M E r) → LPO := by
  sorry -- TO FORMALIZE
```

Proof sketch:
1. Given a binary sequence `α : ℕ → Bool`, construct a specific Schwarzschild interior geodesic whose convergence behavior encodes whether `∃ n, α n = true`.
2. Use the technique from the Ising LPO equivalence: embed the sequence into the rate of approach to r = 0.
3. If geodesic incompleteness holds (r reaches 0 in finite time), extract the LPO decision.

This is structurally identical to the forward direction in Paper 8. The monotone function changes from free energy per particle to radial coordinate, but the encoding technique is the same.

### Module 5: LPO Equivalence — Reverse Direction (`GR/Interior/LPO_Reverse.lean`)
**~80-120 lines**

**LPO → GeodesicIncompleteness**

```lean
/-- LPO implies geodesic incompleteness in the Schwarzschild interior. -/
theorem LPO_implies_geodesic_incompleteness (h_LPO : LPO) :
  ∀ M E r, M > 0 → E ≥ 1 → IsRadialGeodesic M E r →
    Interior M (r 0) → GeodesicIncompleteness M E r := by
  sorry -- TO FORMALIZE
```

Proof sketch:
1. With LPO, Bounded Monotone Convergence holds.
2. `r(τ)` is monotonically decreasing and bounded below by 0.
3. By BMC, `r(τ)` converges to some limit `L ≥ 0`.
4. Show `L = 0` using the geodesic equation: if `L > 0`, the velocity `|dr/dτ|` remains bounded away from zero (from Module 2), contradicting convergence to `L`.
5. The closed-form solution gives explicit `τ* = πM` (for `E = 1`), establishing finite proper time.

### Module 6: BISH Content — Exterior and Finite-Parameter Interior (`GR/Interior/BISH_Content.lean`)
**~80-100 lines**

Demonstrate that the physical content — curvature computations and geodesic focusing over finite parameter intervals — is BISH.

```lean
/-- The Kretschner scalar is constructively computable for any r > 0,
    whether interior or exterior. Already proved for exterior; extend domain. -/
theorem kretschner_computable_interior (M r : ℝ) (h_int : Interior M r) :
  K M r = 48 * M^2 / r^6 := by
  -- Reuse existing exterior proof; only needs r > 0
  sorry -- TO FORMALIZE (should be near-trivial adaptation)

/-- Geodesic focusing over any finite proper time interval is BISH.
    Given r(τ₀) in the interior, r(τ₁) is constructively computable
    for any τ₁ > τ₀ such that r remains positive on [τ₀, τ₁]. -/
theorem finite_interval_geodesic_BISH (M E : ℝ) (r : ℝ → ℝ)
    (h_geodesic : IsRadialGeodesic M E r) (τ₀ τ₁ : ℝ) (h_lt : τ₀ < τ₁)
    (h_pos : ∀ τ ∈ Set.Icc τ₀ τ₁, r τ > 0) :
  -- r(τ₁) is constructively computable from r(τ₀), M, E
  ∃ v : ℝ, r τ₁ = v ∧ v > 0 := by
  sorry -- TO FORMALIZE

/-- The BISH error bound: for any ε > 0, there exists a finite proper time
    interval on which |r(τ) - 0| < ε, constructively. -/
theorem approaching_singularity_BISH (M E : ℝ) (r : ℝ → ℝ)
    (h_geodesic : IsRadialGeodesic M E r) (h_int : Interior M (r 0))
    (ε : ℝ) (h_ε : ε > 0) :
  ∃ τ : ℝ, τ > 0 ∧ r τ < ε := by
  sorry -- TO FORMALIZE: uses explicit ODE solution, no omniscience needed
```

This module establishes the BISH dispensability: the empirical content (curvature at any specified finite r, geodesic position at any finite proper time) requires no omniscience. Only the *completed* assertion "r reaches exactly 0" costs LPO.

### Module 7: Axiom Certificates (`GR/Interior/Certificates.lean`)
**~40-60 lines**

```lean
/-- Certificate: Kretschner scalar computation is Height 0 (BISH) -/
#print axioms kretschner_computable_interior
-- Expected: propext, Quot.sound only (no Classical.choice)

/-- Certificate: Finite-interval geodesic is Height 0 (BISH) -/
#print axioms finite_interval_geodesic_BISH
-- Expected: propext, Quot.sound only

/-- Certificate: LPO equivalence uses Classical.choice only through LPO -/
#print axioms geodesic_incompleteness_implies_LPO
-- Expected: propext, Quot.sound, + any axioms in LPO definition

#print axioms LPO_implies_geodesic_incompleteness
-- Expected: propext, Quot.sound, Classical.choice (via LPO hypothesis)
```

---

## Estimated Line Counts

| Module | Lines | Difficulty |
|--------|-------|------------|
| 1. Interior Domain | 80-120 | Easy (mirror exterior) |
| 2. Radial Geodesic | 150-250 | Medium (ODE formalization) |
| 3. Incompleteness Statement | 50-80 | Easy (definitions) |
| 4. LPO Forward | 100-150 | Medium (encoding technique from Paper 8) |
| 5. LPO Reverse | 80-120 | Medium (BMC application) |
| 6. BISH Content | 80-100 | Easy-Medium (adapt existing proofs) |
| 7. Certificates | 40-60 | Easy (print axioms) |
| **Total** | **580-880** | |

---

## Key Technical Decisions for the Agent

### 1. Reuse vs. Rebuild
- **REUSE** the metric components, Christoffel symbols, and Kretschner scalar from the exterior formalization. These algebraic expressions are the same for `r > 0`; only the domain predicate changes.
- **REUSE** the LPO definition and the Bounded Monotone Convergence ↔ LPO equivalence from the Ising papers (Papers 7-8). The encoding technique transfers directly.
- **REBUILD** nothing from scratch. This paper's value is connecting existing infrastructure.

### 2. Handling the Geodesic ODE
The radial geodesic has a closed-form solution (cycloid parametrization for E = 1):

```
r(η) = M(1 + cos η)
τ(η) = M(η + sin η)
```

where η ∈ [0, π] maps r from 2M down to 0, with τ* = πM.

Two options:
- **Option A (recommended):** Work with the closed-form solution directly. Define `r` and `τ` as explicit functions of the parameter η. This avoids formalizing ODE existence/uniqueness theory, which would be a massive detour. The monotonicity, boundedness, and convergence properties are all explicit from the trigonometric parametrization.
- **Option B:** Formalize the ODE abstractly and invoke existence/uniqueness. This is cleaner mathematically but requires ODE infrastructure that may not exist in the codebase. Avoid unless already available.

### 3. The LPO Encoding
The forward direction (GeodesicIncompleteness → LPO) requires encoding a binary sequence into a geodesic. The standard technique from Paper 8:

Given `α : ℕ → Bool`, define a modified monotone decreasing function that "stalls" at a positive value unless `∃ n, α n = true`. If geodesic incompleteness asserts this function reaches 0, we can decide `∃ n, α n = true` vs `∀ n, α n = false`.

Concretely: construct a sequence that decreases like the geodesic when α is identically false, but receives an extra "kick" toward 0 whenever α n = true. The geodesic incompleteness assertion then decides LPO.

### 4. What NOT to Formalize
- Do NOT formalize the full Penrose singularity theorem. That requires trapped surfaces, energy conditions, and global hyperbolicity — massive infrastructure for a different paper.
- Do NOT formalize Kruskal-Szekeres coordinates. The coordinate singularity at r = 2M is irrelevant; the result is about the physical content at r = 0.
- Do NOT formalize quantum gravity corrections. The paper's claim is about classical GR.

---

## File Layout

```
GR/
├── Interior/
│   ├── Domain.lean              -- Module 1
│   ├── RadialGeodesic.lean      -- Module 2
│   ├── Incompleteness.lean      -- Module 3
│   ├── LPO_Forward.lean         -- Module 4
│   ├── LPO_Reverse.lean         -- Module 5
│   ├── BISH_Content.lean        -- Module 6
│   └── Certificates.lean        -- Module 7
├── Height0/
│   └── Schwarzschild.lean       -- Existing exterior formalization
└── ... (existing infrastructure)
```

---

## Success Criteria

The formalization is complete when:

1. `#print axioms geodesic_incompleteness_implies_LPO` shows only constructive axioms + LPO-related imports
2. `#print axioms LPO_implies_geodesic_incompleteness` shows Classical.choice only through the LPO hypothesis
3. `#print axioms kretschner_computable_interior` shows no Classical.choice (Height 0)
4. `#print axioms finite_interval_geodesic_BISH` shows no Classical.choice (Height 0)
5. Zero `sorry` in all seven modules
6. Full build completes without errors

---

## Paper Punchline

The event horizon at r = 2M is not only the boundary of the causal region from which light cannot escape — it is the boundary of the constructive region where physical predictions require no omniscience principle. Outside: BISH. Inside: the physics (geodesic focusing, curvature growth) remains BISH, but the singularity assertion (geodesic termination at r = 0) is exactly LPO. The horizon demarcates not just what can communicate with infinity, but what can be asserted without surveying an infinite set.
