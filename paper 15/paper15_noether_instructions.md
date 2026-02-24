# Paper 15: Noether's Theorem and the Logical Cost of Global Conservation Laws
## Coding Agent Instructions — Lean 4 Formalization

**Author:** P.C.K. Lee
**Date:** February 2026
**Status:** Build — the pencil-and-paper check confirms the split

---

## 0. Executive Summary

**Thesis:** Noether's theorem — the most fundamental structural principle in physics — splits cleanly across the constructive hierarchy. Local conservation (∂μJμ = 0) is BISH. Global energy (E = lim E_R) is LPO. The idealization enters not in the symmetry principle itself but in the integration over all of space.

**Strategy:** Avoid infinite-dimensional function spaces entirely. Work with a **1+1 dimensional scalar field on a finite lattice** as the concrete model. The lattice keeps everything finite-dimensional. The energy density is a sum of squared terms (positive definite, guaranteeing monotonicity). The infinite-volume limit N → ∞ is structurally identical to the Ising thermodynamic limit (Paper 8) and the decoherence limit (Paper 14).

**What makes this work:** The math agent confirmed that the sign of the conserved density is the critical variable. Energy density T⁰⁰ ≥ 0 gives bounded monotone convergence → LPO. Charge density J⁰ (signed) gives oscillatory convergence → messy, not BMC. We formalize energy, not charge.

---

## 1. The Physics

### 1.1 The Model: Scalar Field on a 1D Lattice

Configuration: N sites on a line, indexed by i ∈ {1, ..., N}. Field values φ_i ∈ ℝ at each site. Conjugate momenta π_i ∈ ℝ.

Lattice Lagrangian (with spacing a = 1 for simplicity):

  L_N = Σ_{i=1}^{N} [ ½ π_i² - ½ (φ_{i+1} - φ_i)² - V(φ_i) ]

where V(φ) ≥ 0 is a non-negative potential (e.g., V(φ) = ½ m² φ² or V(φ) = λ φ⁴).

Equations of motion (discrete Euler-Lagrange):

  φ̇_i = π_i
  π̇_i = (φ_{i+1} - 2φ_i + φ_{i-1}) - V'(φ_i)

with boundary conditions (free or periodic — choose periodic for cleanliness).

### 1.2 The Symmetry: Time Translation

The Lagrangian has no explicit time dependence. By Noether's theorem, the conserved quantity is the energy:

  E_N = Σ_{i=1}^{N} [ ½ π_i² + ½ (φ_{i+1} - φ_i)² + V(φ_i) ]

This is a sum of non-negative terms (critical for monotonicity).

### 1.3 The Three-Level Structure

**Level 1 — Local conservation (BISH):** For any solution of the equations of motion, dE_N/dt = 0. This is an algebraic identity: differentiate, substitute the equations of motion, everything cancels by telescoping. Pure finite arithmetic.

**Level 2 — Finite-volume energy (BISH):** For any finite N, E_N is a computable real number. Given field values and momenta to finite precision, E_N is computed by a finite sum of squares.

**Level 3 — Infinite-volume energy (LPO):** Define the energy of an infinite system as E = lim_{N→∞} E_N where E_N is the energy of the first N sites. Since each term in the sum is non-negative:

  E_{N+1} = E_N + [½ π_{N+1}² + ½ (φ_{N+2} - φ_{N+1})² + V(φ_{N+1})] ≥ E_N

So {E_N} is monotone increasing. If the system is physically bounded (finite total energy), then {E_N} is bounded above. Asserting E = lim E_N exists is BMC → LPO.

### 1.4 The Physical Interpretation

Every conservation law in the Standard Model has this structure:
- **Local** (∂μJμ = 0): BISH — algebraic identity at each spacetime point
- **Finite-volume** (Q_R = ∫_{B_R} J⁰ d³x for finite R): BISH — finite computation
- **Global** (Q = lim Q_R): LPO for positive-definite densities (energy, probability), messy for signed densities (electric charge)

The paper formalizes this for energy on the lattice as the concrete example.

---

## 2. Formalization Architecture

### 2.1 Module Structure

```
Paper15_Noether/
├── Defs.lean                  -- Lattice field definitions
│                                 (field config, momenta, Lagrangian, energy)
├── EulerLagrange.lean         -- Discrete equations of motion
├── LocalConservation.lean     -- dE_N/dt = 0 (the algebraic identity)
│                                 THIS IS THE NOETHER CONTENT
├── FiniteEnergy.lean          -- E_N is computable, non-negative
├── Monotonicity.lean          -- E_{N+1} ≥ E_N (from positivity of terms)
├── CauchyModulus.lean         -- If decay rate given, explicit ε-bound (BISH)
├── GlobalEnergy.lean          -- E = lim E_N ↔ BMC ↔ LPO
├── Main.lean                  -- Assembly, #print axioms, documentation
└── Papers.lean                -- Module imports
```

Estimated total: 500–800 lines.

### 2.2 Key Design Decisions

**Lattice, not continuum.** We never touch function spaces, Sobolev spaces, distributions, or PDEs. Everything is finite sums over Fin N. This is both physically honest (lattice field theory is how physics is actually computed) and Lean-practical (finite types, decidable equality, norm_num).

**Periodic boundary conditions.** Set φ_{N+1} = φ_1 for the finite system. This makes the equations of motion uniform across sites and simplifies the conservation proof (no boundary terms).

**Parametric N.** The finite-volume energy is defined for arbitrary N : ℕ. The monotonicity is proven for the sequence N ↦ E_N as N grows (adding sites).

**Important subtlety: two meanings of "N → ∞".**

There are two different infinite limits in play:
1. **Time evolution** of a fixed N-site system: E_N is conserved (dE_N/dt = 0). This is the Noether content. BISH.
2. **Infinite-volume limit** as the number of sites grows: E = lim_{N→∞} E_N. This is the global charge. LPO.

The paper proves both. They are logically independent results with different axiom costs.

### 2.3 Dependencies on Existing Infrastructure

**From Paper 8 (Ising/BMC ↔ LPO):**
- `BMC_iff_LPO` — the equivalence (axiomatised, same as Paper 14)
- The bounded monotone convergence pattern

**From Paper 14 (Decoherence):**
- `abc_iff_bmc` — antitone bounded convergence ↔ BMC (if needed; energy is monotone increasing, so we use BMC directly)
- The general pattern: finite computation at BISH, completed limit at LPO

**New infrastructure needed:**
- Lattice field configuration as `Fin N → ℝ`
- Discrete Lagrangian and energy as `Finset.sum`
- Discrete equations of motion
- The conservation identity (algebraic cancellation)

---

## 3. Detailed Proof Plan

### Part A: Definitions and Setup (100–150 lines)

#### 3.1 Lattice Field Configuration

```lean
/-- A lattice field configuration: field values at N sites -/
abbrev FieldConfig (N : ℕ) := Fin N → ℝ

/-- Conjugate momenta -/
abbrev Momenta (N : ℕ) := Fin N → ℝ

/-- A state of the lattice field: configuration + momenta -/
structure LatticeState (N : ℕ) where
  φ : FieldConfig N
  π : Momenta N
```

#### 3.2 Energy Density and Total Energy

```lean
/-- Kinetic energy density at site i -/
def kineticDensity (s : LatticeState N) (i : Fin N) : ℝ :=
  (1/2) * (s.π i)^2

/-- Gradient energy density at site i (periodic BC: φ_{N} wraps to φ_0) -/
def gradientDensity (s : LatticeState N) (i : Fin N) : ℝ :=
  (1/2) * (s.φ (i.succ_mod N) - s.φ i)^2
  -- Note: need to handle the index wrapping for periodic BC

/-- Potential energy density at site i.
    V : ℝ → ℝ is the potential, assumed non-negative. -/
def potentialDensity (V : ℝ → ℝ) (s : LatticeState N) (i : Fin N) : ℝ :=
  V (s.φ i)

/-- Energy density at site i -/
def energyDensity (V : ℝ → ℝ) (s : LatticeState N) (i : Fin N) : ℝ :=
  kineticDensity s i + gradientDensity s i + potentialDensity V s i

/-- Total energy of an N-site system -/
def totalEnergy (V : ℝ → ℝ) (s : LatticeState N) : ℝ :=
  Finset.sum Finset.univ (energyDensity V s)
```

#### 3.3 Non-negativity of Energy Density

```lean
/-- Each term in the energy is non-negative -/
theorem energyDensity_nonneg (V : ℝ → ℝ) (hV : ∀ x, 0 ≤ V x)
    (s : LatticeState N) (i : Fin N) :
    0 ≤ energyDensity V s i := by
  unfold energyDensity kineticDensity gradientDensity potentialDensity
  positivity  -- or: apply add_nonneg; apply add_nonneg; all use sq_nonneg and hV
```

This is the theorem that makes the whole paper work. Positivity of energy density → monotonicity of partial sums → BMC → LPO. Without positivity (e.g., for charge density), the argument fails.

### Part B: Local Conservation — Noether's Theorem (150–200 lines)

#### 3.4 Equations of Motion

Define the discrete equations of motion as a predicate on time-dependent states:

```lean
/-- The discrete equations of motion (Euler-Lagrange on the lattice) -/
def satisfiesEOM (V : ℝ → ℝ) (φ : ℝ → FieldConfig N) (π : ℝ → Momenta N) : Prop :=
  ∀ t : ℝ, ∀ i : Fin N,
    -- φ̇_i = π_i
    HasDerivAt (fun t => φ t i) (π t i) t ∧
    -- π̇_i = discrete Laplacian - V'(φ_i)
    HasDerivAt (fun t => π t i)
      (φ t (i.succ_mod N) - 2 * φ t i + φ t (i.pred_mod N) - deriv V (φ t i)) t
```

**Lean note:** `HasDerivAt` from Mathlib handles the time derivatives. The discrete Laplacian is explicit finite arithmetic. `deriv V` for the potential derivative — if V is a polynomial (e.g., V(x) = ½m²x²), the derivative is explicit.

**Simplification option:** Instead of continuous-time derivatives, work with **discrete time steps** (Δt). Then the equations of motion are recurrence relations, avoiding Mathlib's calculus entirely. This would make the entire paper purely algebraic. The conservation law becomes E(t+Δt) = E(t) (energy is invariant under one time step of the discrete dynamics). This is the **symplectic integrator** perspective and may be much easier to formalise.

#### 3.5 The Conservation Theorem

```lean
/-- Noether's theorem on the lattice: energy is conserved along solutions -/
theorem energy_conserved (V : ℝ → ℝ) (φ : ℝ → FieldConfig N) (π : ℝ → Momenta N)
    (hEOM : satisfiesEOM V φ π) :
    ∀ t : ℝ, HasDerivAt (fun t => totalEnergy V ⟨φ t, π t⟩) 0 t := by
  sorry
```

**Proof strategy:**
1. Differentiate totalEnergy with respect to t
2. Apply the chain rule to each term in the Finset.sum
3. Substitute the equations of motion
4. The kinetic terms produce π_i · π̇_i = π_i · (Δφ_i - V'(φ_i))
5. The gradient terms produce (φ_{i+1} - φ_i) · (φ̇_{i+1} - φ̇_i) = (φ_{i+1} - φ_i)(π_{i+1} - π_i)
6. The potential terms produce V'(φ_i) · φ̇_i = V'(φ_i) · π_i
7. Sum over i: the gradient contributions telescope (periodic BC), the V'π terms cancel between kinetic and potential
8. Result: dE/dt = 0

This is the algebraic heart of Noether's theorem. Every step is finite arithmetic. BISH.

**Discrete-time alternative:** If using discrete time steps, the proof is even simpler — verify E(t+Δt) = E(t) by direct computation. No derivatives needed.

### Part C: Monotonicity and the Infinite-Volume Limit (100–150 lines)

#### 3.6 Partial Sums are Monotone

Now switch perspective: fix a field configuration on ℕ (an infinite lattice) and consider partial energies.

```lean
/-- Field configuration on the infinite lattice -/
abbrev InfiniteFieldConfig := ℕ → ℝ
abbrev InfiniteMomenta := ℕ → ℝ

/-- Energy of the first N sites -/
noncomputable def partialEnergy (V : ℝ → ℝ) (φ : InfiniteFieldConfig) (π : InfiniteMomenta)
    (N : ℕ) : ℝ :=
  Finset.sum (Finset.range N) fun i =>
    (1/2) * (π i)^2 + (1/2) * (φ (i+1) - φ i)^2 + V (φ i)
```

```lean
/-- Partial energy is monotone increasing in N -/
theorem partialEnergy_mono (V : ℝ → ℝ) (hV : ∀ x, 0 ≤ V x)
    (φ : InfiniteFieldConfig) (π : InfiniteMomenta) :
    Monotone (partialEnergy V φ π) := by
  intro m n hmn
  unfold partialEnergy
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono hmn
  · intro i _ _
    -- each summand is non-negative (sum of squares + non-negative V)
    positivity
```

#### 3.7 Boundedness

```lean
/-- If the total energy is physically bounded, partialEnergy is bounded above -/
theorem partialEnergy_bounded (V : ℝ → ℝ) (hV : ∀ x, 0 ≤ V x)
    (φ : InfiniteFieldConfig) (π : InfiniteMomenta)
    (M : ℝ) (hM : ∀ N, partialEnergy V φ π N ≤ M) :
    BddAbove (Set.range (partialEnergy V φ π)) := by
  exact ⟨M, by rintro _ ⟨N, rfl⟩; exact hM N⟩
```

### Part D: The LPO Equivalence (150–200 lines)

#### 3.8 Global Energy Exists ↔ BMC ↔ LPO

```lean
/-- The assertion that global energy exists for all bounded field configurations
    is equivalent to BMC, hence to LPO -/
theorem global_energy_iff_LPO :
    (∀ (V : ℝ → ℝ) (hV : ∀ x, 0 ≤ V x)
       (φ : InfiniteFieldConfig) (π : InfiniteMomenta)
       (M : ℝ) (hM : ∀ N, partialEnergy V φ π N ≤ M),
       ∃ E, Filter.Tendsto (partialEnergy V φ π) Filter.atTop (nhds E))
    ↔ LPO := by
  sorry
```

**Proof strategy for the reverse direction (global energy → LPO):**

Given an arbitrary bounded monotone increasing sequence {a_n}, we need to encode it as a partial energy sequence.

**Encoding:** Given a_n monotone increasing, 0 ≤ a_n ≤ M, define:
- Set V = 0 (free field)
- Set φ_i = 0 for all i (zero field configuration)
- Define π_i = √(2(a_{i+1} - a_i)) for i ≥ 0

Then:
  partialEnergy(N) = Σ_{i=0}^{N-1} ½ π_i²
                   = Σ_{i=0}^{N-1} (a_{i+1} - a_i)
                   = a_N - a_0

So partialEnergy(N) = a_N - a_0, which converges iff {a_n} converges.

This encoding maps an arbitrary bounded monotone sequence to a partial energy sequence. If global energy always exists, then every bounded monotone sequence converges, which is BMC, which is LPO.

```lean
/-- Encoding: any bounded monotone sequence is a partial energy sequence -/
theorem encode_monotone_as_energy (a : ℕ → ℝ) (ha_mono : Monotone a)
    (ha_nonneg : ∀ n, 0 ≤ a n) (M : ℝ) (ha_bdd : ∀ n, a n ≤ M) :
    ∃ (φ : InfiniteFieldConfig) (π : InfiniteMomenta),
      ∀ N, partialEnergy (fun _ => 0) φ π N = a N - a 0 := by
  sorry
```

**This encoding is the key lemma.** It's the analogue of the variable-angle encoding in Paper 14 (but cleaner — no arccos, no products, just square roots of increments).

#### 3.9 Forward Direction (LPO → Global Energy)

Standard: LPO → BMC (axiomatised from Paper 8). The partial energy sequence is bounded and monotone, so BMC gives convergence.

---

## 4. Axiom Certificate Requirements

Same standard as Papers 8, 13, 14:

**BISH content (Parts A–B):**
- Local conservation theorem: NO classical axioms beyond Mathlib infrastructure
- Finite energy computation: NO classical axioms
- Monotonicity of partial energy: NO classical axioms
- Positivity of energy density: NO classical axioms

**LPO content (Part D):**
- `global_energy_iff_LPO`: uses axiomatised `bmc_of_lpo` / `lpo_of_bmc`
- Forward direction uses LPO hypothesis
- Reverse direction (encoding) must be BISH — no classical axioms

---

## 5. Priority Order for Implementation

### Step 1: Definitions and Energy (Defs.lean + FiniteEnergy.lean)

Define lattice field configuration, energy density, total energy. Prove non-negativity of each term. This is pure `Finset.sum` over `Fin N` with `sq_nonneg` and `positivity`. Should compile quickly.

**Decision point:** Choose between continuous-time derivatives (more physical, harder Lean) and discrete-time symplectic steps (more algebraic, easier Lean). Recommend **discrete time** for the first pass — it avoids `HasDerivAt` entirely and makes everything purely algebraic. You can always add the continuous-time version later.

### Step 2: Local Conservation (LocalConservation.lean)

The Noether content. Prove dE/dt = 0 (or E(t+Δt) = E(t) for discrete time). This is the algebraic cancellation by telescoping sums over Fin N with periodic boundary conditions.

This is the most important theorem in the paper conceptually. It should have a clean `#print axioms`.

### Step 3: Monotonicity (Monotonicity.lean)

Prove partialEnergy is monotone increasing in N. This follows from non-negativity of each summand plus `Finset.sum_le_sum_of_subset_of_nonneg`. Short and clean.

### Step 4: The Encoding (GlobalEnergy.lean)

The reverse direction: arbitrary bounded monotone sequence → partial energy sequence. Define π_i = √(2(a_{i+1} - a_i)), verify the telescoping sum, conclude BMC → LPO.

### Step 5: Assembly (Main.lean)

Import everything. `#print axioms` for all exported theorems. Document certification levels.

---

## 6. What Could Go Wrong

### 6.1 Periodic boundary conditions and indexing

`Fin N` arithmetic with wrapping (i.succ_mod, i.pred_mod) can be fiddly in Lean. The telescoping sum in the conservation proof needs every boundary term to cancel. Periodic BC guarantees this, but the index arithmetic requires care.

**Mitigation:** Define a helper `wrap : ℤ → Fin N` or use `ZMod N` if Mathlib supports it cleanly.

### 6.2 Square roots in the encoding

The encoding uses π_i = √(2(a_{i+1} - a_i)). Need a_{i+1} ≥ a_i (from monotonicity) to ensure the argument is non-negative. Then `Real.sqrt` from Mathlib handles it. But verifying ½(√x)² = x/2 · 2 = x requires `Real.sq_sqrt` and careful arithmetic.

**Mitigation:** Alternatively, skip the square root entirely. Set the potential V(φ) = φ and the field value φ_i = a_{i+1} - a_i ≥ 0 (which is non-negative by monotonicity). Then V(φ_i) = a_{i+1} - a_i and the partial sum telescopes directly. This avoids square roots at the cost of a less physical model (V(φ) = φ is not a standard potential, but the mathematics doesn't care).

**Recommended:** Use the simpler encoding without square roots. The encoding is a mathematical construction, not a physical model. Cleanliness of the Lean code matters more than physical plausibility of the encoded configuration.

### 6.3 Continuous-time derivatives

If using `HasDerivAt` for the conservation proof, Mathlib's calculus library may require smoothness hypotheses, chain rule lemmas for Finset.sum, and other infrastructure that could be time-consuming.

**Mitigation:** Use discrete-time formulation (Step 1 decision point). Verify conservation for a single symplectic Euler step. This is purely algebraic.

### 6.4 The gradient energy term in the encoding

The partial energy includes gradient terms ½(φ_{i+1} - φ_i)². In the encoding, if we set φ = 0 everywhere, gradient terms vanish and we only need kinetic or potential terms. This simplifies the encoding considerably.

---

## 7. The Calibration Table (Updated)

| Domain | Paper | Bounded Monotone Sequence | BISH Content | LPO Content |
|--------|-------|--------------------------|--------------|-------------|
| Stat. Mech. | 8 | Free energy f_N | f_N computed, ε-bounds | f_∞ exists |
| Gen. Relativity | 13 | Radial coordinate r(τ) | r(τ) computed | r → 0 (singularity) |
| Quantum Measurement | 14 | Coherence c(N) | c(N) < ε for explicit N₀ | c → 0 (collapse) |
| **Conservation Laws** | **15** | **Partial energy E_N** | **E_N computed, dE/dt = 0** | **E = lim E_N exists** |

Four independent physical domains. Same logical structure. Same BMC ↔ LPO equivalence.

The Noether row adds something the other three don't have: the local conservation law (dE/dt = 0) is itself a BISH theorem about the *structure* of physical law, not just about a specific prediction. Papers 8, 13, 14 calibrate predictions. Paper 15 calibrates a *principle*.

---

## 8. The Punchline

Physical laws are locally constructive. The symmetry principle that generates conservation laws (Noether's theorem) is algebraic and BISH. The conserved quantities themselves — energy, momentum, angular momentum — are BISH in any finite region. The idealization enters only when you assert that the *total* conserved quantity of an infinite system exists as a definite real number. That assertion is BMC. BMC is LPO.

Every conservation law in the Standard Model has a local form (BISH) and a global form (LPO). The physics lives in the local form. The global form is a mathematical convenience — the "completed infinity" that the constructive hierarchy identifies as an idealization.

---

## 9. Instructions for the Coding Agent

### Build Order

1. **Defs.lean** — Lattice field types, energy density, total energy, non-negativity
2. **EulerLagrange.lean** — Equations of motion (discrete time recommended)
3. **LocalConservation.lean** — dE/dt = 0 or E(t+Δt) = E(t). THE NOETHER THEOREM.
4. **Monotonicity.lean** — E_{N+1} ≥ E_N from positivity
5. **CauchyModulus.lean** — If decay rate given, explicit ε-bound (BISH)
6. **GlobalEnergy.lean** — Encoding + LPO equivalence
7. **Main.lean** — Assembly + `#print axioms`

### Decision: Discrete vs Continuous Time

**Recommend discrete time.** Define a one-step map (symplectic Euler or Störmer-Verlet) and prove energy is exactly conserved under one step. This makes the conservation proof purely algebraic (no `HasDerivAt`, no chain rule, no Mathlib calculus). The physical content is identical — lattice field theory with discrete time is how physics is actually computed.

If you choose continuous time, be prepared for 200+ additional lines fighting Mathlib's derivative infrastructure.

### Decision: Encoding Strategy

**Recommend the simple encoding:** V(φ) = φ (or V(φ) = any function), set φ_i = 0, π_i = 0, and encode the monotone sequence directly into the potential values at each site. The simplest version: define a custom energy functional that sums non-negative terms d_i = a_{i+1} - a_i. The telescoping is immediate.

The physical plausibility of the encoding doesn't matter. What matters is that the encoding maps arbitrary bounded monotone sequences to partial energy sequences, proving that global energy existence implies BMC.

### What to Report Back

After each step:
1. Lines of code
2. `#print axioms` output
3. Obstacles encountered
4. Assessment of next step feasibility

### Success Criteria

**Minimum result:** Local conservation is BISH (clean axioms) + monotonicity of partial energy proven.

**Full result:** Local conservation BISH + global energy ↔ LPO equivalence. Fourth domain in the calibration table.
