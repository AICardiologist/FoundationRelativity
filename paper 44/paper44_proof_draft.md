# Paper 44: The Measurement Problem Dissolved
## Proof Draft for Lean 4 Formalization

### Status: DRAFT — for Lean formalization agent

---

## 1. Overview

This paper shows that the three major interpretations of quantum mechanics require
logically distinct constructive principles:

| Interpretation | Key assertion | Constructive principle | Equivalence |
|---|---|---|---|
| Copenhagen | Superposition → definite outcome (zero-test on coefficients) | WLPO | Theorem 3.1 |
| Many-Worlds | Completed infinite branching tree of outcomes | DC | Theorem 4.1 |
| Bohmian Mechanics | Completed particle trajectory on [0,∞) | LPO (via BMC) | Theorem 5.1 |

**Consequence:** The interpretations are not "different ways of saying the same thing."
They have provably distinct logical costs. The measurement problem is not a single problem
but three different problems requiring three different idealisations.

**Base system:** BISH (Bishop's constructive mathematics).

**Formalization target:** ~900 lines of Lean 4 (200 + 300 + 400), structurally modeled on Paper 14.

---

## 2. Mathematical Preliminaries

### 2.1 Constructive Principles (import from programme library)

```
-- These should already exist in the CRM library from prior papers

def LPO : Prop :=
  ∀ (f : ℕ → Bool), (∃ n, f n = true) ∨ (∀ n, f n = false)

def WLPO : Prop :=
  ∀ (f : ℕ → Bool), (¬¬ ∃ n, f n = true) ∨ (∀ n, f n = false)

-- Equivalently: ∀ (f : ℕ → Bool), (∀ n, f n = false) ∨ ¬(∀ n, f n = false)

def BMC : Prop :=  -- Bounded Monotone Convergence
  ∀ (a : ℕ → ℝ), Monotone a → BddAbove (Set.range a) → ∃ L, Filter.Tendsto a Filter.atTop (nhds L)

def DC : Prop :=  -- Dependent Choice
  ∀ (α : Type) (R : α → α → Prop),
    (∀ x, ∃ y, R x y) → ∀ x₀, ∃ f : ℕ → α, f 0 = x₀ ∧ ∀ n, R (f n) (f (n + 1))
```

### 2.2 Known equivalence (from Paper programme)

```
-- BMC ↔ LPO is established in earlier papers (Papers 29-31)
theorem BMC_iff_LPO : BMC ↔ LPO
```

---

## 3. Copenhagen Interpretation: WLPO

### 3.1 Physical setup

A quantum system in superposition |ψ⟩ = α|0⟩ + β|1⟩ with |α|² + |β|² = 1.

Copenhagen postulate: measurement yields definite outcome. This requires determining
whether α = 0 (system is in state |1⟩) or α ≠ 0 (system has a |0⟩ component).

### 3.2 Formal model

```
-- A qubit state is a pair (α, β) of complex amplitudes with |α|² + |β|² = 1
structure QubitState where
  α : ℂ
  β : ℂ
  norm_eq : Complex.normSq α + Complex.normSq β = 1

-- The Copenhagen measurement postulate for a qubit:
-- Given |ψ⟩ = α|0⟩ + β|1⟩, measurement yields outcome 0 with prob |α|²
-- and outcome 1 with prob |β|².
-- The assertion that measurement produces a DEFINITE outcome
-- (i.e., we can determine whether outcome 0 is possible or impossible)
-- requires deciding: α = 0 ∨ α ≠ 0.

-- But constructively, for a general real number r, deciding r = 0 ∨ r ≠ 0 is not available.
-- The weaker statement ¬¬(r ≠ 0) ∨ r = 0 is exactly WLPO.
```

### 3.3 Reduction to zero-test

```
-- Encode a binary sequence f : ℕ → Bool into a real number
-- via the standard construction: r_f = Σ f(n) · 2^{-(n+1)}
-- Then: r_f = 0 ↔ ∀ n, f n = false
--       r_f ≠ 0 ↔ ∃ n, f n = true

-- WLPO for f is: (∀ n, f n = false) ∨ ¬(∀ n, f n = false)
-- Which is: r_f = 0 ∨ ¬(r_f = 0)
-- Which is: r_f = 0 ∨ ¬¬(r_f ≠ 0)

-- Construct qubit state with α = r_f / √(r_f² + 1), β = 1 / √(r_f² + 1)
-- (This always satisfies |α|² + |β|² = 1)
-- Then: α = 0 ↔ r_f = 0 ↔ ∀ n, f n = false
```

### 3.4 Theorems to prove

```
-- Forward direction: Copenhagen measurement postulate → WLPO
theorem copenhagen_implies_WLPO :
  (∀ (ψ : QubitState), ψ.α = 0 ∨ ¬¬(ψ.α ≠ 0)) → WLPO := by
  intro h f
  -- Construct qubit state from f using the encoding
  -- Apply h to get α = 0 ∨ ¬¬(α ≠ 0)
  -- Translate back to (∀ n, f n = false) ∨ ¬(∀ n, f n = false)
  sorry

-- Reverse direction: WLPO → Copenhagen measurement postulate
theorem WLPO_implies_copenhagen :
  WLPO → (∀ (ψ : QubitState), ψ.α = 0 ∨ ¬¬(ψ.α ≠ 0)) := by
  intro wlpo ψ
  -- Encode ψ.α as a binary sequence (or use WLPO on reals directly)
  -- This direction may require the real-number form of WLPO:
  -- ∀ r : ℝ, r = 0 ∨ ¬(r = 0)... but that's actually LEM for equality.
  -- More carefully: WLPO gives ¬¬(r ≠ 0) ∨ r = 0 for Cauchy reals
  -- encoded from binary sequences. Need to verify this lifts.
  sorry

-- Combined equivalence
theorem copenhagen_iff_WLPO :
  (∀ (ψ : QubitState), ψ.α = 0 ∨ ¬¬(ψ.α ≠ 0)) ↔ WLPO := by
  exact ⟨copenhagen_implies_WLPO, WLPO_implies_copenhagen⟩
```

### 3.5 Notes for Lean agent

- The encoding of binary sequences into reals is standard and should exist in the CRM library from earlier papers. If not, Paper 14 has the pattern.
- The key subtlety in the reverse direction: WLPO is a statement about binary sequences, but we need it for arbitrary complex amplitudes. The standard move is to show that arbitrary Cauchy reals can encode binary sequences. This is well-established in constructive analysis.
- Estimated size: ~200 lines including the encoding infrastructure.

---

## 4. Many-Worlds Interpretation: DC

### 4.1 Physical setup

In Many-Worlds, measurement doesn't collapse the wavefunction. Instead, the universe
branches: each possible outcome is realized in a separate branch. A sequence of
measurements produces a branching tree of worlds.

### 4.2 Formal model

```
-- A measurement event with finitely many outcomes
structure Measurement where
  outcomes : Finset ℕ
  nonempty : outcomes.Nonempty

-- An Everettian branching history is an infinite sequence of measurements
-- together with a choice of outcome at each step.
-- The "world" an observer inhabits is a path through this tree.

-- A branching structure: at each step n, the available outcomes may depend
-- on all previous choices (the "history so far").
structure BranchingStructure where
  measurement : (n : ℕ) → (Fin n → ℕ) → Measurement
  -- At step n, given history (choices at steps 0..n-1), what measurement occurs?

-- A world (complete branch) is a function choosing an outcome at each step,
-- consistent with the branching structure.
def World (B : BranchingStructure) : Type :=
  { f : ℕ → ℕ // ∀ n, f n ∈ (B.measurement n (fun i => f i.val)).outcomes }
```

### 4.3 The role of Dependent Choice

```
-- The existence of a complete world (infinite path through the tree)
-- requires choosing at each step based on prior choices.
-- This is exactly Dependent Choice.

-- Define the "one-step extension" relation:
-- A partial history of length n can be extended to length n+1
-- by choosing any valid outcome of the n-th measurement.

-- Key insight: the choices are NOT independent. The measurement at step n
-- depends on the history, so the available outcomes at step n depend on
-- all choices at steps 0..n-1. This is why we need DC, not just countable choice.

-- HOWEVER: If the branching structure is UNIFORM (measurement at step n
-- does not depend on history), then the choices are independent and
-- Countable Choice suffices. This is an important subtlety.

-- For the general Many-Worlds interpretation (where later measurements
-- depend on earlier outcomes, e.g., adaptive experiments), DC is required.
```

### 4.4 Theorems to prove

```
-- A BranchingStructure is "history-dependent" if later measurements
-- genuinely depend on earlier outcomes
def HistoryDependent (B : BranchingStructure) : Prop :=
  ∃ n (h₁ h₂ : Fin n → ℕ), h₁ ≠ h₂ ∧
    B.measurement n h₁ ≠ B.measurement n h₂

-- Forward: existence of worlds in all branching structures → DC
theorem manyworlds_implies_DC :
  (∀ B : BranchingStructure, Nonempty (World B)) → DC := by
  intro h α R hR x₀
  -- Construct a branching structure where:
  --   outcomes at step 0 = {y : R x₀ y}
  --   outcomes at step n+1 given history (x₀,x₁,...,xₙ) = {y : R xₙ y}
  -- A world in this structure IS a DC sequence.
  sorry

-- Reverse: DC → existence of worlds
theorem DC_implies_manyworlds :
  DC → (∀ B : BranchingStructure, Nonempty (World B)) := by
  intro dc B
  -- Apply DC with:
  --   α = Σ n, (Fin n → ℕ)  (partial histories)
  --   R (n, h) (n+1, h') iff h' extends h by a valid outcome
  -- DC gives an infinite path, which is a World.
  sorry

-- Combined equivalence
theorem manyworlds_iff_DC :
  (∀ B : BranchingStructure, Nonempty (World B)) ↔ DC := by
  exact ⟨manyworlds_implies_DC, DC_implies_manyworlds⟩
```

### 4.5 Important subtlety: when is DC actually needed?

```
-- If all measurements are identical and history-independent:
structure UniformBranching where
  M : Measurement  -- same measurement at every step

-- Then worlds exist by Countable Choice (weaker than DC):
-- At each step, independently choose from M.outcomes.
-- This is Π_{n:ℕ} M.outcomes, which exists without DC
-- (it's a function out of ℕ into a fixed nonempty finite set).

-- So: Uniform Many-Worlds needs only the axiom that ℕ → Fin k is inhabited
-- for all k > 0, which is trivially BISH-provable.

-- DC is needed precisely when the branching is history-dependent:
-- the measurement at step n depends on outcomes at steps 0..n-1.
-- This corresponds to adaptive measurement protocols in quantum mechanics
-- (e.g., quantum error correction, adaptive quantum computing).

-- PAPER SHOULD DISCUSS: Which physical scenarios actually require DC vs CC?
-- This strengthens the result by showing exactly when Many-Worlds
-- has a genuine logical cost beyond BISH.
```

### 4.6 Notes for Lean agent

- The forward direction (Many-Worlds → DC) is the harder direction and requires careful encoding of an arbitrary DC instance as a branching structure.
- The type theory of dependent histories (Fin n → ℕ) requires care with universe levels and decidability. Consider using `Vector ℕ n` instead of `Fin n → ℕ` for better Lean ergonomics.
- The uniform case (where DC is NOT needed) should be formalized as a separate theorem to sharpen the result.
- Estimated size: ~300 lines. The encoding is the main work.

---

## 5. Bohmian Mechanics: LPO (via BMC)

### 5.1 Physical setup

In Bohmian mechanics, particles have definite positions guided by the wavefunction.
The guidance equation is dx/dt = v^B(x,t) where v^B = (ℏ/m) Im(∂ₓψ/ψ).

We use the simplest possible system: a free Gaussian wave packet on ℝ.

### 5.2 The explicit solution

The Gaussian wave packet (free particle, 1D):

```
ψ(x,t) = (2πσ_t²)^{-1/4} exp(-(x - x₀ - v₀t)² / (4σ_t²) + i(k₀x - ωt))

where σ_t² = σ₀² + ℏ²t² / (4m²σ₀²)
```

The Bohmian velocity field:

```
v^B(x,t) = v₀ + (ℏt / (2mσ₀²σ_t²)) · (x - x₀ - v₀t)
```

The guidance equation dx/dt = v^B(x,t) in the co-moving frame y = x - x₀ - v₀t:

```
dy/dt = α(t) · y   where  α(t) = ℏt / (2mσ₀²σ_t²)
```

This is a linear ODE with explicit solution:

```
y(t) = y(0) · σ_t / σ₀

Therefore: x(t) = x₀ + v₀t + (x(0) - x₀) · σ_t / σ₀
```

### 5.3 Formal model

```
-- Physical parameters (packaged for cleanliness)
structure BohmianParams where
  σ₀ : ℝ   -- initial width
  v₀ : ℝ   -- group velocity
  x₀ : ℝ   -- initial center
  m  : ℝ   -- mass
  ℏ  : ℝ   -- reduced Planck constant
  σ₀_pos : 0 < σ₀
  m_pos  : 0 < m
  ℏ_pos  : 0 < ℏ

-- The spreading width
noncomputable def σ (p : BohmianParams) (t : ℝ) : ℝ :=
  Real.sqrt (p.σ₀^2 + p.ℏ^2 * t^2 / (4 * p.m^2 * p.σ₀^2))

-- The explicit Bohmian trajectory
noncomputable def bohmian_trajectory (p : BohmianParams) (x_init : ℝ) (t : ℝ) : ℝ :=
  p.x₀ + p.v₀ * t + (x_init - p.x₀) * σ p t / p.σ₀

-- The Bohmian velocity field
noncomputable def bohmian_velocity (p : BohmianParams) (x t : ℝ) : ℝ :=
  p.v₀ + (p.ℏ * t / (2 * p.m * p.σ₀^2 * (σ p t)^2)) * (x - p.x₀ - p.v₀ * t)
```

### 5.4 Verification: trajectory satisfies the ODE

```
-- This is pure calculus. Differentiate bohmian_trajectory with respect to t
-- and verify it equals bohmian_velocity evaluated at (bohmian_trajectory, t).

theorem trajectory_satisfies_ODE (p : BohmianParams) (x_init : ℝ) :
  ∀ t : ℝ, HasDerivAt (bohmian_trajectory p x_init) 
    (bohmian_velocity p (bohmian_trajectory p x_init t) t) t := by
  intro t
  -- Expand definitions
  -- d/dt [x₀ + v₀t + (x_init - x₀) · σ_t/σ₀]
  -- = v₀ + (x_init - x₀) · (dσ_t/dt) / σ₀
  -- Need: dσ_t/dt = ℏ²t / (4m²σ₀²σ_t)    [chain rule on sqrt]
  -- Then verify this equals v^B(x(t), t)
  -- = v₀ + (ℏt / (2mσ₀²σ_t²)) · (x_init - x₀) · σ_t/σ₀
  -- = v₀ + (x_init - x₀) · ℏt / (2mσ₀³σ_t)
  -- These match since (dσ_t/dt)/σ₀ = ℏ²t/(4m²σ₀³σ_t)
  -- and ℏt/(2mσ₀³σ_t) = ... need to verify these are equal.
  --
  -- Actually: dσ/dt = (ℏ²t)/(4m²σ₀²σ_t)  [from σ² = σ₀² + ℏ²t²/(4m²σ₀²)]
  -- So (dσ/dt)/σ₀ = ℏ²t/(4m²σ₀³σ_t)
  -- And v^B at trajectory = v₀ + ℏt/(2mσ₀²σ_t²) · (x_init-x₀)·σ_t/σ₀
  --                       = v₀ + (x_init-x₀) · ℏt/(2mσ₀³σ_t)
  -- These are equal iff ℏ²/(4m²σ₀³σ_t) = ℏ/(2mσ₀³σ_t)
  -- i.e., ℏ/(4m²) = 1/(2m), i.e., ℏ = 2m.
  -- WAIT — this is NOT generally true. Let me recheck.
  --
  -- CORRECTION: The velocity field has ℏ/m (not ℏ²/m²) from the definition
  -- v^B = (ℏ/m) Im(∂ₓψ/ψ). Let me redo this more carefully.
  --
  -- From σ_t² = σ₀² + (ℏt/(2mσ₀))², we get:
  -- 2σ_t · dσ_t/dt = 2 · ℏ²t/(4m²σ₀²) = ℏ²t/(2m²σ₀²)
  -- So dσ_t/dt = ℏ²t/(4m²σ₀²σ_t)
  --
  -- Trajectory derivative:
  -- dx/dt = v₀ + (x_init - x₀)/σ₀ · dσ_t/dt
  --       = v₀ + (x_init - x₀) · ℏ²t/(4m²σ₀³σ_t)
  --
  -- Velocity field at trajectory:
  -- v^B(x(t),t) = v₀ + [ℏ²t/(2m · 2mσ₀² · σ_t²)] · (x_init-x₀)·σ_t/σ₀
  --
  -- Hmm, let me be very explicit about the velocity field derivation.
  -- For ψ Gaussian with center x₀+v₀t and width σ_t:
  -- log ψ = -(x-x₀-v₀t)²/(4σ_t²) + i(k₀x - ωt) + normalization
  -- But σ_t is complex in general! For a free particle:
  -- σ_t² = σ₀² + iℏt/(2m)   (COMPLEX, not real)
  --
  -- THIS IS THE CRITICAL ISSUE. σ_t² is complex-valued.
  -- The "width" |σ_t|² = σ₀⁴ + (ℏt/(2m))² is real,
  -- but the Gaussian exponent involves the complex σ_t².
  --
  -- Let me redo with σ_c² = σ₀² + iℏt/(2m) (complex width parameter).
  -- Then |ψ|² is Gaussian with real width |σ_c|²/σ₀
  -- The Bohmian velocity from Im(∂ₓ log ψ) picks up a term from
  -- the imaginary part of 1/σ_c².
  --
  -- Writing σ_c² = σ₀² + iℏt/(2m):
  -- 1/σ_c² = (σ₀² - iℏt/(2m)) / |σ_c|⁴    ... no wait
  -- 1/σ_c² = conj(σ_c²)/|σ_c²|² = (σ₀² - iℏt/(2m))/(σ₀⁴ + ℏ²t²/(4m²))
  --
  -- ∂ₓ log ψ = -(x - x₀ - v₀t)/(2σ_c²) + ik₀
  -- Im(∂ₓ log ψ) = -(x-x₀-v₀t)/(2) · Im(1/σ_c²) + k₀
  --              = (x-x₀-v₀t)/2 · ℏt/(2m) / (σ₀⁴ + ℏ²t²/(4m²)) + k₀
  --
  -- Let Σ² = σ₀⁴ + ℏ²t²/(4m²) = σ₀² · (σ₀² + ℏ²t²/(4m²σ₀²)) = σ₀² · σ_R²
  -- where σ_R² = σ₀² + ℏ²t²/(4m²σ₀²) is the REAL spreading width.
  --
  -- So: v^B = (ℏ/m)[k₀ + (x-x₀-v₀t)·ℏt/(4m·σ₀²·σ_R²)]
  --        = v₀ + ℏ²t/(4m²σ₀²σ_R²) · (x-x₀-v₀t)
  --   where v₀ = ℏk₀/m
  --
  -- NOW the ODE dy/dt = α(t)y with α(t) = ℏ²t/(4m²σ₀²σ_R²)
  -- and ∫α dt = (1/2)ln(σ_R²/σ₀²)  [since d(σ_R²)/dt = ℏ²t/(2m²σ₀²) = 2σ_R²·α]
  -- So y(t) = y(0)·σ_R/σ₀.  ✓
  --
  -- And dx/dt = v₀ + y(0)·(dσ_R/dt)/σ₀ = v₀ + y(0)·ℏ²t/(4m²σ₀³σ_R)
  -- While v^B(x(t),t) = v₀ + ℏ²t/(4m²σ₀²σ_R²)·y(0)·σ_R/σ₀
  --                    = v₀ + y(0)·ℏ²t/(4m²σ₀³σ_R)   ✓ MATCHES
  --
  -- So the explicit solution IS correct with the coefficient ℏ²/(4m²σ₀²)
  -- rather than ℏ/(2mσ₀²). The earlier draft in the chat had the wrong
  -- coefficient (using ℏ/m instead of ℏ²/m² from the double application).
  sorry
```

### 5.5 BISH computability at finite time

```
-- At any finite T, x(T) is computed by evaluating:
--   x₀ + v₀T + (x_init - x₀) · σ_R(T)/σ₀
-- where σ_R(T) = √(σ₀² + ℏ²T²/(4m²σ₀²))
-- This involves: addition, multiplication, division, square root of a known positive number.
-- All BISH-computable operations on ℝ.

theorem finite_time_BISH (p : BohmianParams) (x_init : ℝ) (T : ℝ) :
  -- The trajectory value x(T) is computable from the parameters
  -- (This is essentially: the function bohmian_trajectory is defined by
  -- BISH-computable operations, so its evaluation at any concrete T is computable)
  -- In Lean, this is trivially true since we gave an explicit definition.
  -- The content is that NO non-constructive principle was used.
  True := trivial
  -- NOTE: The real content here is a meta-theorem about the definition.
  -- The Lean agent should verify that bohmian_trajectory uses only
  -- operations available in BISH (field operations + sqrt of positive reals).
  -- This can be stated more formally if desired.
```

### 5.6 The infinite-time limit requires LPO

```
-- As t → ∞, σ_R(t) ~ ℏt/(2mσ₀), so:
-- x(t) ~ x₀ + v₀t + (x_init - x₀) · ℏt/(2mσ₀²)
--       = x₀ + [v₀ + (x_init - x₀)·ℏ/(2mσ₀²)] · t
--
-- The particle approaches asymptotic velocity:
-- v_∞ = v₀ + (x_init - x₀) · ℏ/(2mσ₀²)
--
-- More precisely, define the "velocity function":
-- v(t) = dx/dt = v₀ + (x_init - x₀) · ℏ²t/(4m²σ₀³σ_R(t))
--
-- As t → ∞: v(t) → v_∞ monotonically from below (for x_init > x₀)
-- or from above (for x_init < x₀), with v(t) bounded.
--
-- The assertion that lim_{t→∞} v(t) exists is:
-- a bounded monotone sequence converges — this is BMC — this is LPO.

-- For the formal encoding, we discretize: define a_n = v(n) for n ∈ ℕ.
-- {a_n} is bounded and monotone. Its convergence is equivalent to BMC.

-- More precisely: we encode a binary sequence f into the parameters
-- and show that convergence of the discretized velocity sequence
-- decides f.

-- Encoding: Given f : ℕ → Bool, define
-- x_init(f) = x₀ + σ₀ · Σ_{n} f(n) · 2^{-(n+1)}
-- (So x_init = x₀ iff ∀ n, f n = false)
--
-- Then v_∞(f) = v₀ + [Σ f(n)·2^{-(n+1)}] · ℏ/(2mσ₀)
-- and v_∞(f) = v₀ iff x_init(f) = x₀ iff ∀ n, f n = false.
--
-- If the completed trajectory exists (i.e., lim v(t) exists),
-- then v_∞ is determined, and we can test v_∞ = v₀ vs v_∞ > v₀.
-- Since v_∞ ≥ v₀ (monotone from below in this encoding),
-- we get: v_∞ = v₀ ∨ v_∞ > v₀, which gives (∀n, f n = false) ∨ (∃n, f n = true).
-- That's LPO.

theorem bohmian_implies_LPO :
  -- If every Bohmian trajectory on [0,∞) has a well-defined asymptotic velocity
  (∀ (p : BohmianParams) (x_init : ℝ),
    ∃ v_infty, Filter.Tendsto (fun t => deriv (bohmian_trajectory p x_init) t)
      Filter.atTop (nhds v_infty)) →
  LPO := by
  intro h f
  -- Construct BohmianParams and x_init encoding f
  -- Apply h to get v_∞
  -- Use BMC_iff_LPO or argue directly
  sorry

theorem LPO_implies_bohmian :
  LPO →
  (∀ (p : BohmianParams) (x_init : ℝ),
    ∃ v_infty, Filter.Tendsto (fun t => deriv (bohmian_trajectory p x_init) t)
      Filter.atTop (nhds v_infty)) := by
  intro lpo p x_init
  -- Use LPO → BMC
  -- The velocity v(t) is bounded and monotone (prove this from the explicit formula)
  -- Apply BMC
  sorry

theorem bohmian_iff_LPO :
  (∀ (p : BohmianParams) (x_init : ℝ),
    ∃ v_infty, Filter.Tendsto (fun t => deriv (bohmian_trajectory p x_init) t)
      Filter.atTop (nhds v_infty)) ↔ LPO := by
  exact ⟨bohmian_implies_LPO, LPO_implies_bohmian⟩
```

### 5.7 Notes for Lean agent

**CRITICAL CORRECTION from drafting process:** The Bohmian velocity field coefficient is ℏ²/(4m²σ₀²), NOT ℏ/(2mσ₀²). This arises because v^B = (ℏ/m)·Im(∂ₓ log ψ) and the imaginary part of 1/σ_c² introduces another factor of ℏ/(2m). The explicit solution x(t) = x₀ + v₀t + (x_init - x₀)·σ_R(t)/σ₀ is correct regardless, but the ODE verification must use the correct coefficient. See the detailed calculation in §5.4.

- The ODE verification (§5.4) is the technically hardest part. It requires Mathlib's `HasDerivAt` for compositions involving `Real.sqrt`. Paper 14's infrastructure should cover this.
- The monotonicity of v(t) needs a sign analysis of dv/dt. This is straightforward from the explicit formula but requires careful Lean bookkeeping.
- The encoding of f into x_init is identical in structure to encodings used in earlier papers.
- Consider stating the result via BMC directly (avoiding the discretization), using the continuous version of bounded monotone convergence if available in the library.
- Estimated size: ~400 lines. The ODE verification and monotonicity proof are the bulk.

---

## 6. Synthesis: The Dissolution

### 6.1 Main theorem (informal)

The measurement problem is not one problem but three, with distinct logical costs:

```
-- The three calibrations, collected
theorem measurement_problem_dissolved :
  -- Copenhagen: deciding superposition vs eigenstate ↔ WLPO
  ((∀ ψ : QubitState, ψ.α = 0 ∨ ¬¬(ψ.α ≠ 0)) ↔ WLPO) ∧
  -- Many-Worlds: existence of complete branches ↔ DC
  ((∀ B : BranchingStructure, Nonempty (World B)) ↔ DC) ∧
  -- Bohmian: completed trajectory with asymptotic velocity ↔ LPO
  ((∀ p x_init, ∃ v, Tendsto (deriv (bohmian_trajectory p x_init)) atTop (nhds v)) ↔ LPO) := by
  exact ⟨copenhagen_iff_WLPO, manyworlds_iff_DC, bohmian_iff_LPO⟩
```

### 6.2 Logical relationships between the principles

```
-- The three principles are distinct and ordered:
-- WLPO is strictly weaker than LPO (known)
-- DC is independent of LPO (known: neither implies the other in BISH)
-- So the three interpretations sit at genuinely different positions
-- in the constructive hierarchy.

-- WLPO < LPO (strict)
-- DC ∦ LPO (incomparable)
-- DC ∦ WLPO (incomparable)

-- These independence results are meta-theoretic and do not need
-- Lean formalization (they're established in the literature).
-- But cite: Ishihara, Bridges-Richman, etc.
```

### 6.3 Interpretive content (for paper prose, not Lean)

The paper should discuss:

1. **Copenhagen is cheapest.** WLPO is strictly weaker than LPO. So the Copenhagen interpretation requires the least logical overhead — but it also says the least (it gives up on describing what happens between measurements).

2. **Bohmian is more expensive than Copenhagen.** LPO strictly implies WLPO. The extra cost buys you continuous trajectories — but those trajectories are constructively incomplete (you can't assert their existence on all of [0,∞) without LPO).

3. **Many-Worlds is orthogonal.** DC is incomparable with both LPO and WLPO. The branching tree structure requires a fundamentally different kind of idealisation than either wavefunction collapse or trajectory completion. This is the most surprising result: Many-Worlds is not "stronger" or "weaker" than the others — it's in a different logical dimension entirely.

4. **No interpretation is free.** All three require principles beyond BISH. There is no constructively innocent interpretation of quantum mechanics (at least for these three). This is a no-go result.

5. **The "measurement problem" was a category error.** Arguing about which interpretation is correct is like arguing whether addition or multiplication is the "right" arithmetic operation. They serve different purposes and carry different costs.

---

## 7. File Structure

```
Paper44/
├── Basic.lean              -- imports, common definitions, parameters
├── Copenhagen.lean         -- QubitState, zero-test encoding, WLPO equivalence
├── ManyWorlds.lean         -- BranchingStructure, World, DC equivalence
├── Bohmian.lean            -- BohmianParams, trajectory, ODE, LPO equivalence
├── Synthesis.lean          -- measurement_problem_dissolved, collected result
└── README.md               -- build instructions, dependencies
```

## 8. Dependencies

**From CRM programme library (prior papers):**
- LPO, WLPO, BMC definitions and basic equivalences (BMC ↔ LPO)
- Binary sequence encoding into reals
- Standard constructive analysis infrastructure

**From Mathlib:**
- `Mathlib.Analysis.SpecialFunctions.Gaussian` (if available)
- `Mathlib.Analysis.Calculus.Deriv.Basic` (HasDerivAt)
- `Mathlib.Analysis.SpecialFunctions.Pow.Real` (sqrt, powers)
- `Mathlib.Topology.Order.Basic` (Filter.Tendsto, monotone convergence)
- `Mathlib.Data.Complex.Basic` (for Copenhagen section)

**New infrastructure needed:**
- Dependent Choice as a formal axiom/principle (may not exist in Mathlib; define it)
- BranchingStructure and World types (new, ~50 lines)
- Bohmian trajectory explicit definition and ODE verification (~100 lines)

## 9. Risk Assessment

| Component | Risk | Mitigation |
|---|---|---|
| Copenhagen (WLPO) | Low | Extension of Paper 14 pattern |
| Many-Worlds (DC) | Medium | DC encoding needs care; uniform case subtlety |
| Bohmian (ODE verify) | Low-Medium | Explicit solution, but sqrt derivatives in Lean can be fiddly |
| Synthesis | Low | Just collecting three results |

**Overall estimate:** 5-8 working days for a Lean-fluent agent with access to the CRM library and Mathlib.

---

## 10. Erratum from Chat Discussion

During the initial drafting conversation, the Bohmian velocity field was stated with coefficient ℏ/(2mσ₀²). The correct coefficient is ℏ²/(4m²σ₀²), arising from the complex-valued width parameter σ_c² = σ₀² + iℏt/(2m). The imaginary part of 1/σ_c² introduces the additional factor. The closed-form trajectory x(t) = x₀ + v₀t + (x_init - x₀)·σ_R/σ₀ remains correct. The Lean agent should use the corrected coefficient throughout.
