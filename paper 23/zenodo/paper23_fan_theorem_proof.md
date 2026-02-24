# The Fan Theorem and the Constructive Cost of Optimization:
# Free Energy Extrema on Compact Parameter Spaces

## Paper 23 — Proof Document for Lean 4 Formalization

### Paul C.-K. Lee
### February 2026

---

## 0. Purpose, Context, and Design Principles

### 0.1 What this paper proves

This paper establishes that the assertion "a continuous function on
a compact interval attains its extremum" — the Extreme Value Theorem
(EVT) — is equivalent to the Fan Theorem (FT) over BISH, and
instantiates this equivalence through free energy optimization in
the 1D Ising model. This is the first CRM calibration at the Fan
Theorem, and the first to calibrate a *compactness* principle
(as opposed to an omniscience or witness-extraction principle).

The paper has three parts:

- **Part A (BISH):** For any *fixed* coupling J > 0, the free
  energy f(β, J) = -log(2cosh(βJ)) is computable with explicit
  error bounds. Finite optimization over a finite grid of J values
  is BISH. No FT needed.

- **Part B (FT calibration):** The assertion "the continuous
  function J ↦ f(β, J) attains its minimum on the compact interval
  [J_min, J_max]" is equivalent to the Fan Theorem over BISH.

- **Part C (Hierarchy placement):** FT is independent of the
  omniscience chain (LLPO, WLPO, LPO) and independent of Markov's
  Principle. The calibration table extends to a third independent
  branch.

### 0.2 What is the Fan Theorem?

The Fan Theorem (FT): every bar on Cantor space is uniform.

A **bar** on {0,1}^ℕ is a set B of finite binary strings such that
every infinite sequence α has an initial segment in B. The bar is
**uniform** if there exists N such that for every α, some initial
segment of α of length ≤ N is in B.

Equivalently (the form we use): every pointwise continuous function
on a compact complete metric space is uniformly continuous.

Most usefully for us, FT is equivalent to:

**Extreme Value Theorem (EVT):** Every continuous function
f : [a, b] → ℝ attains its maximum (and minimum).

The equivalence FT ↔ EVT is due to Berger and Bridges (2006),
building on earlier work by Julian and Richman.

**Status in constructive mathematics:** FT is a Brouwerian
principle — accepted in intuitionistic mathematics (Brouwer proved
it from the continuity principle) but independent of BISH. It is
also independent of LPO, WLPO, LLPO, and MP. FT is a *continuity/
compactness* principle, not a decidability or witness-extraction
principle. It occupies a genuinely different dimension of the
constructive landscape.

### 0.3 The key physical insight

Physics uses optimization constantly: minimizing free energy to
find equilibrium states, maximizing entropy, minimizing action
(Hamilton's principle), finding ground state energies. All of these
involve asserting that a continuous functional attains its extremum
on some domain.

For finite systems, optimization is finite search — BISH. For
infinite systems, the domain is typically infinite-dimensional,
and optimization requires compactness arguments. The Fan Theorem
is the constructive content of these compactness arguments.

The 1D Ising model provides the cleanest instance: the free energy
f(β, J) = -log(2cosh(βJ)) is a continuous function of the coupling
J on any compact interval [J_min, J_max]. Asserting that f attains
its minimum on this interval is EVT, which is FT.

### 0.4 Relationship to existing papers

- **Paper 8:** Proved LPO ↔ BMC for 1D Ising free energy
  convergence (thermodynamic limit). This paper adds a new
  question about the same free energy: does it attain its
  extremum on a compact parameter space?

- **Paper 20:** Proved WLPO ↔ phase classification (magnetization
  zero-test). Same Ising model, yet another logical cost.

- **Paper 22:** Proved MP ↔ eventual decay. First branch off the
  main chain. This paper adds a second branch (FT), confirming
  the partial order structure.

The 1D Ising model now exhibits FOUR distinct logical costs:
1. Finite-volume computation: BISH (Paper 8, Part A)
2. Thermodynamic limit existence: LPO (Paper 8, Part B)
3. Phase classification: WLPO (Paper 20)
4. Parameter-space optimization: FT (Paper 23)

### 0.5 Dependencies

This paper is **self-contained**. It uses the free energy formula
f(β, J) = -log(2cosh(βJ)) from Paper 8 but does not import Paper 8's
Lean code. The EVT ↔ FT equivalence is the core mathematical content;
the Ising model is the physical instantiation.

### 0.6 What the coding agent should NOT do

- Do NOT import Classical.em or Classical.byContradiction in Part A.
- Do NOT attempt to formalize the full Fan Theorem in terms of bars
  and fans. Use the EVT characterization exclusively.
- Do NOT formalize compactness of [a,b] from first principles. Use
  the EVT ↔ FT equivalence as an interface axiom.
- Do NOT re-derive the Ising free energy formula. Take
  f(β, J) = -log(2cosh(βJ)) as a definition.

---

## 1. Mathematical Setup

### 1.1 The free energy as a function of coupling

For fixed inverse temperature β > 0, the 1D Ising free energy per
site in the thermodynamic limit is:

  f(β, J) = -log(2 · cosh(β · J))

This is a function of the coupling constant J. For J > 0:
- f is continuous in J (composition of continuous functions)
- f is strictly decreasing in J (since cosh is increasing on [0,∞)
  and log is increasing)
- f < 0 for all J > 0 (since 2cosh(βJ) > 2 > 1 for βJ > 0)

### 1.2 Optimization on a compact interval

For 0 < J_min < J_max, consider the continuous function:

  g : [J_min, J_max] → ℝ
  g(J) = f(β, J) = -log(2 · cosh(β · J))

The **Extreme Value Theorem** asserts: g attains its minimum and
maximum on [J_min, J_max]. That is:

  ∃ J* ∈ [J_min, J_max], ∀ J ∈ [J_min, J_max], g(J*) ≤ g(J)
  ∃ J** ∈ [J_min, J_max], ∀ J ∈ [J_min, J_max], g(J) ≤ g(J**)

For this specific function, since g is strictly decreasing, the
minimum is attained at J_max and the maximum at J_min. So the EVT
is "trivially true" for this monotone function — BUT the coding
agent must be careful: the EVT equivalence with FT requires the
statement for *arbitrary* continuous functions, not just monotone
ones.

### 1.3 The generalized optimization assertion

To get a genuine FT equivalence, we need the EVT for arbitrary
continuous functions on [a, b], not just for the specific monotone
free energy. The physical assertion is:

**FreeEnergyOptimization:** For every continuous function
g : [J_min, J_max] → ℝ (representing a generalized free energy
functional parameterized by coupling), g attains its minimum.

The physical motivation: in more complex models (multi-parameter
Hamiltonians, competing interactions), the free energy as a function
of coupling constants is NOT monotone and finding the optimal
coupling requires the full EVT.

```lean
/-- The optimization assertion: every continuous function on a
    compact interval attains its minimum. -/
def CompactOptimization : Prop :=
  ∀ (a b : ℝ) (hab : a < b) (f : ℝ → ℝ),
    ContinuousOn f (Set.Icc a b) →
    ∃ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, f x ≤ f y
```

### 1.4 The Fan Theorem (EVT form)

```lean
/-- The Fan Theorem in its EVT form: every continuous function
    on [0,1] attains its maximum. -/
def FanTheorem_EVT : Prop :=
  ∀ (f : ℝ → ℝ), ContinuousOn f (Set.Icc 0 1) →
    ∃ x ∈ Set.Icc 0 1, ∀ y ∈ Set.Icc 0 1, f y ≤ f x
```

Note: EVT on [0,1] is equivalent to EVT on any [a,b] by
affine rescaling. We use [0,1] for the canonical form and
[J_min, J_max] for the physical instantiation.

### 1.5 Equivalence of min and max forms

EVT-max (attains maximum) and EVT-min (attains minimum) are
equivalent: apply EVT-max to -f to get EVT-min. So we can use
either form freely.

```lean
theorem evt_min_of_evt_max (hmax : FanTheorem_EVT) :
    CompactOptimization := by
  sorry
  -- Apply FanTheorem_EVT to -f, rescale [a,b] to [0,1]
```

---

## 2. Part A: BISH Computability of Finite Optimization

### 2.1 Statement

**Theorem (Part A).** For any finite grid
{J₁, J₂, ..., J_N} ⊂ [J_min, J_max], the minimum of f(β, ·)
over the grid is computable. No FT needed.

### 2.2 Proof

Finite minimization over a finite set is a decidable computation.
For each J_k, compute f(β, J_k) = -log(2cosh(βJ_k)) (computable
since β, J_k are computable reals). Compare the N values and
return the minimum. This is a finite loop — pure BISH.

```lean
/-- Finite-grid optimization is BISH. -/
theorem finite_grid_opt (β : ℝ) (hβ : 0 < β)
    (grid : Finset ℝ) (hne : grid.Nonempty)
    (hpos : ∀ J ∈ grid, 0 < J) :
    ∃ J_star ∈ grid, ∀ J ∈ grid,
      isingFreeEnergy β J_star ≤ isingFreeEnergy β J := by
  sorry
  -- Use Finset.exists_min_image
```

### 2.3 Approximation quality

For a uniform grid with spacing δ = (J_max - J_min)/N and a
function with modulus of continuity ω, the grid minimum
approximates the true minimum within ω(δ). For the Ising free
energy, which has bounded derivative on [J_min, J_max]:

  |f'(β, J)| = β · tanh(βJ) ≤ β

So the modulus of continuity is ω(δ) = β · δ, and the grid
approximation is within β · (J_max - J_min)/N of the true minimum.
This bound is explicit and computable — BISH.

The FT content is precisely the step from "the grid minimum
approximates the true minimum for any N" to "the true minimum
is attained at some J* ∈ [J_min, J_max]."

### 2.4 Axiom audit for Part A

All Part A theorems should show:
  [propext, Classical.choice, Quot.sound]

No custom axioms (no fan_theorem, no evt_axiom).

---

## 3. Part B: Fan Theorem Calibration

### 3.1 The interface axiom

The equivalence FT ↔ EVT is a known result
(Berger 2005, Bridges–Vîță 2006, Julian–Richman 2002). We
axiomatize one direction:

```lean
/-- FT (in bar/fan form) implies EVT.
    Standard (Berger 2005, Bridges-Vîță 2006). -/
axiom evt_of_fan_theorem :
  FanTheorem → FanTheorem_EVT
```

where `FanTheorem` is the bar-theoretic form and `FanTheorem_EVT`
is the max-attainment form on [0,1].

Actually, for cleanliness, we can axiomatize the EVT form directly
as the interface, since it's the equivalent we use:

```lean
/-- The Fan Theorem in EVT form, axiomatized.
    Equivalent to bar-form FT (Berger 2005). -/
axiom fan_theorem_evt :
  FanTheorem_EVT
-- This axiom is equivalent to the bar-induction form of FT.
-- We use it only in the forward direction.
```

**Wait — this won't give a proper equivalence.** Let me rethink.

The structure should be:

- Define `FreeEnergyOptimization` as the physical assertion
- Prove: FT_EVT → FreeEnergyOptimization (forward)
- Prove: FreeEnergyOptimization → FT_EVT (backward)
- Axiomatize: FT (bar form) ↔ FT_EVT (known equivalence)

So the calibration is:

  FT ↔ FT_EVT ↔ FreeEnergyOptimization

with the first ↔ axiomatized and the second ↔ proved.

Actually, let me simplify further. Since EVT is the standard
characterization, let's just work with EVT throughout:

```lean
/-- The Extreme Value Theorem for [0,1]. -/
def EVT : Prop :=
  ∀ (f : ℝ → ℝ), ContinuousOn f (Set.Icc 0 1) →
    ∃ x ∈ Set.Icc 0 1, ∀ y ∈ Set.Icc 0 1, f y ≤ f x

/-- Physical optimization assertion. -/
def IsingOptimization (β : ℝ) : Prop :=
  ∀ (a b : ℝ) (hab : a < b) (g : ℝ → ℝ),
    ContinuousOn g (Set.Icc a b) →
    ∃ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, g x ≤ g y

/-- The Fan Theorem (bar form) implies EVT.
    Axiomatized, standard result. -/
axiom fan_theorem_implies_evt : FanTheorem → EVT

/-- EVT implies the Fan Theorem (bar form).
    Axiomatized, standard result. -/  
axiom evt_implies_fan_theorem : EVT → FanTheorem
```

Hmm, but then the equivalence FT ↔ physical assertion is just
FT ↔ EVT ↔ EVT-on-[a,b], and the second step is just rescaling.
The physical content becomes thin.

### 3.2 Rethinking the physical content

The issue is that EVT for arbitrary continuous functions on [a,b]
is just EVT — it doesn't have specifically *physical* content
unless we restrict to physically motivated functions.

**Better approach:** Don't use arbitrary continuous functions.
Use the specific family of Ising free energies, but with a
parameterization that makes the EVT content non-trivial.

**Physical assertion:** Consider a system with competing
interactions parameterized by θ ∈ [0, 2π]. The free energy is:

  F(θ) = -log(2cosh(β(J₁cos(θ) + J₂sin(θ))))

where J₁, J₂ > 0 are two coupling constants and θ parameterizes
their relative weight. This is a continuous function of θ on
the compact interval [0, 2π]. It is NOT monotone (it has maxima
and minima as θ varies). The assertion that F attains its minimum
on [0, 2π] — i.e., there exists an optimal mixing angle θ* — is
EVT applied to a specific physical free energy.

**This is physically natural:** finding the optimal ratio of
competing interactions is a standard problem in condensed matter
physics. The ground state of a frustrated magnet depends on the
relative strengths of competing couplings, and the optimal
parameters are found by minimizing the free energy over a compact
parameter space.

Actually, let me simplify even further. This is getting
over-engineered. The core mathematical content is:

  EVT ↔ FT (known, axiomatize)
  EVT is used in physics for optimization
  Part A: finite-dimensional optimization is BISH
  Part B: infinite / continuous optimization requires EVT = FT

The physical instantiation is illustrative, not constitutive.
The paper's contribution is calibrating FT as the exact cost
of compact optimization, with the Ising model as an example.

### 3.3 Revised structure: direct EVT ↔ FT calibration

Let me restructure. The equivalence we prove is:

  FT ↔ CompactMinimization

where CompactMinimization is: every continuous function on [a,b]
has a minimizer.

Forward: FT → EVT → CompactMinimization (rescale from [0,1])
Backward: CompactMinimization → EVT (restrict to [0,1])

The backward direction is trivial (CompactMinimization on
general [a,b] specializes to [0,1]). The forward direction
uses rescaling.

But this is just saying "EVT on [0,1] ↔ EVT on [a,b]" which
is boring.

**The real content needs a different backward direction.** Let me
reconsider.

### 3.4 Better backward direction: encoding binary sequences

For a genuine calibration, the backward direction should encode
binary sequences into continuous functions on [0,1] such that the
existence of a maximizer forces a decision about the sequence.

**Construction:**

Given α : ℕ → Bool, define:

  g_α(x) = Σ_{n=0}^{∞} (if α(n) = true then φ_n(x) else 0)

where φ_n are continuous bump functions on [0,1] with:
- supp(φ_n) ⊂ [a_n, b_n] (disjoint supports)
- max(φ_n) = 2^{-n} (heights decrease geometrically)
- The intervals [a_n, b_n] are packed into [0,1]

Then g_α is continuous on [0,1] (uniform limit of continuous
functions with geometrically decreasing heights).

The maximum of g_α on [0,1] is:
- max(g_α) = 2^{-n*} where n* = min{n : α(n) = true}
  (if such exists)
- max(g_α) = 0 if ∀n, α(n) = false

If EVT holds, g_α attains its maximum at some x* ∈ [0,1].
The value g_α(x*) is the maximum. Can we extract LLPO, WLPO,
or FT-specific information from x*?

**⚠ PROBLEM:** The encoding gives us the maximizer x*, from
which we can determine which bump function x* is in, hence
which α(n) = true. But this gives LPO-type information (finding
a witness), which is too strong — FT is independent of LPO.

**The issue:** A direct "encode sequence into bump functions"
approach tends to give LPO content, not FT content. This is
because finding the maximum of a function with isolated peaks
is essentially a search problem.

### 3.5 The correct approach: FT as uniform continuity

FT is equivalent to: every pointwise continuous function on
[0,1] (or Cantor space) is uniformly continuous. This is NOT
about finding maxima per se — it's about the *uniformity* of
continuity.

**Revised physical assertion:**

**UniformContinuityOnCompact:** For every pointwise continuous
function f : [0,1] → ℝ, f is uniformly continuous on [0,1].
That is: ∀ε > 0, ∃δ > 0, ∀x,y ∈ [0,1], |x-y| < δ → |f(x)-f(y)| < ε.

Physical content: the free energy f(β, J), viewed as a function
of J on a compact coupling interval, has a uniform modulus of
continuity. For the specific Ising free energy, this modulus is
explicitly computable (bounded derivative → Lipschitz → uniform
continuity with explicit modulus). But for a general free energy
functional — one defined as a thermodynamic limit of a
parameterized family — the uniform continuity on the compact
parameter space requires FT.

### 3.6 The clean encoding: FT via Cantor space

Let me go back to basics. The Fan Theorem in its canonical form
is about Cantor space {0,1}^ℕ, which is compact (in the
constructive sense, this IS the Fan Theorem).

**Revised approach:** Encode binary sequences into *points* of
Cantor space and define a functional on Cantor space whose
uniform continuity is FT.

**Physical functional on Cantor space:**

Define a "generalized Ising model" parameterized by an infinite
sequence of coupling signs σ ∈ {0,1}^ℕ:

  H(σ) = Σ_{n=0}^{∞} (-1)^{σ(n)} · J · 2^{-n}

This is a continuous function on Cantor space (equipped with the
product topology). FT says this function is uniformly continuous
— i.e., there exists N such that H(σ) depends (up to ε) only on
σ(0), ..., σ(N-1).

But this is trivially uniformly continuous because the tail
Σ_{n≥N} |J · 2^{-n}| ≤ J · 2^{-N+1} → 0. So the uniform
modulus is explicit: N = ⌈log₂(J/ε)⌉ + 1. No FT needed.

**⚠ The problem recurs:** For *specific* continuous functions on
Cantor space that we can write down, the uniform continuity
modulus tends to be explicit (BISH). FT is needed only for
*arbitrary* continuous functions whose modulus is not given.

### 3.7 Stepping back: what FT really calibrates

The core issue is that FT is about ABSTRACT compactness — the
passage from "every open cover has a finite subcover" or "every
sequence has a convergent subsequence" or "every continuous
function is uniformly continuous" — for ARBITRARY continuous
functions, not specific ones.

In physics, we rarely encounter truly arbitrary continuous
functions. The free energies, partition functions, and
observables we compute are always specific and have explicit
regularity. FT enters physics when we make GENERAL arguments
about classes of systems — "for every Hamiltonian in this class,
the partition function has such-and-such property on compact
parameter spaces."

**Revised proposal: FT ↔ the Heine-Borel property for
parameter spaces.**

Define:

  **HeineBorelOptimization:** For all a < b and all f continuous
  on [a,b], f attains its maximum on [a,b].

This is EVT, which is equivalent to FT. The physical content:
optimization over compact parameter spaces is always achievable.

For the backward direction, we need:

  HeineBorelOptimization → FT

This is where we encode binary sequences. The standard proof
(Berger 2005, Theorem 5.1) constructs, from a bar B on
{0,1}^ℕ, a continuous function f_B on [0,1] whose maximum
is attained iff B is uniform. The construction uses the
binary representation of [0,1] and the bar condition.

**This is the standard mathematical proof, not a physics encoding.**
And that's fine — the paper's contribution is:

1. Proving EVT ↔ FT (via the standard encoding, possibly
   axiomatized)
2. Showing that finite optimization is BISH (Part A)
3. Observing that the step from finite to continuous optimization
   requires FT
4. Instantiating with the Ising free energy as physical example
5. Placing FT in the calibration table as independent of the
   omniscience chain and MP

### 3.8 Final structure decision

OK, I think the cleanest paper structure is:

**Part A (BISH):** Finite-grid optimization is BISH. For the
Ising free energy f(β, J) = -log(2cosh(βJ)), optimization over
any finite grid {J₁,...,J_N} ⊂ [a,b] is constructive. Moreover,
for the specific Ising free energy, the derivative bound
|f'| ≤ β gives an explicit modulus of continuity, so uniform
continuity on [a,b] is BISH for this specific function.

**Part B (FT):** The GENERAL assertion — every continuous function
on [a,b] is uniformly continuous / attains its extremum — is
equivalent to FT. Forward: FT → EVT (axiomatize as known).
Backward: EVT → FT (axiomatize as known, OR prove the standard
Berger encoding).

**Part C:** FT is independent of LLPO, WLPO, LPO, MP. The
calibration table is now a genuine partial order with three
branches.

The paper's contribution is NOT a new equivalence (FT ↔ EVT is
known) but the PHYSICAL INTERPRETATION and the CALIBRATION TABLE
PLACEMENT. The paper says: the step from "this specific free
energy is well-behaved on [a,b]" (BISH) to "every free energy
is well-behaved on compact parameter spaces" (FT) has a precise
constructive cost, and that cost is independent of the omniscience
principles that calibrate other physical assertions.

**⚠ HONESTY NOTE FOR THE PAPER:** The backward direction
(physics → FT) is essentially the standard EVT → FT proof
from constructive analysis, instantiated through the Ising model.
The novelty is in the calibration-table placement and the physical
interpretation, not in the encoding technique. The paper should
be transparent about this.

---

## 4. Lean Formalization

### 4.1 Definitions

```lean
/-- The Extreme Value Theorem (max form) on [0,1]. -/
def EVT_max : Prop :=
  ∀ (f : ℝ → ℝ), ContinuousOn f (Set.Icc 0 1) →
    ∃ x ∈ Set.Icc 0 1, ∀ y ∈ Set.Icc 0 1, f y ≤ f x

/-- The Extreme Value Theorem (min form) on [0,1]. -/
def EVT_min : Prop :=
  ∀ (f : ℝ → ℝ), ContinuousOn f (Set.Icc 0 1) →
    ∃ x ∈ Set.Icc 0 1, ∀ y ∈ Set.Icc 0 1, f x ≤ f y

/-- Compact optimization on arbitrary [a,b]. -/
def CompactOptimization : Prop :=
  ∀ (a b : ℝ), a < b →
    ∀ (f : ℝ → ℝ), ContinuousOn f (Set.Icc a b) →
    ∃ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, f x ≤ f y

/-- Uniform continuity on compact intervals. -/
def UniformContinuityCompact : Prop :=
  ∀ (f : ℝ → ℝ), ContinuousOn f (Set.Icc 0 1) →
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ Set.Icc 0 1, ∀ y ∈ Set.Icc 0 1,
      |x - y| < δ → |f x - f y| < ε

/-- The 1D Ising free energy as function of coupling. -/
noncomputable def isingFreeEnergy (β J : ℝ) : ℝ :=
  -Real.log (2 * Real.cosh (β * J))
```

### 4.2 Part A: BISH content

```lean
/-- The Ising free energy is continuous in J. -/
theorem isingFreeEnergy_continuous (β : ℝ) (hβ : 0 < β) :
    Continuous (isingFreeEnergy β) := by
  sorry
  -- Composition of continuous functions: cosh, mul, log, neg

/-- The Ising free energy has bounded derivative. -/
theorem isingFreeEnergy_deriv_bound (β : ℝ) (hβ : 0 < β)
    (J : ℝ) (hJ : 0 < J) :
    |deriv (isingFreeEnergy β) J| ≤ β := by
  sorry
  -- f'(β, J) = -β · tanh(βJ), |tanh| ≤ 1

/-- The Ising free energy is Lipschitz on [J_min, J_max]. -/
theorem isingFreeEnergy_lipschitz (β : ℝ) (hβ : 0 < β)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    LipschitzOnWith ⟨β, le_of_lt hβ⟩
      (isingFreeEnergy β) (Set.Icc a b) := by
  sorry
  -- From bounded derivative

/-- Finite grid optimization is BISH. -/
theorem finite_opt_bish (β : ℝ) (hβ : 0 < β)
    (grid : Finset ℝ) (hne : grid.Nonempty) :
    ∃ J_star ∈ grid, ∀ J ∈ grid,
      isingFreeEnergy β J_star ≤ isingFreeEnergy β J := by
  exact Finset.exists_min_image grid (isingFreeEnergy β) hne
```

### 4.3 Part B: FT calibration

The key interface axiom:

```lean
/-- The Fan Theorem implies EVT. Standard result
    (Berger 2005, Bridges–Vîță 2006). -/
axiom fan_theorem_implies_evt : FanTheorem → EVT_max

/-- EVT implies the Fan Theorem. Standard result
    (Berger 2005, Julian–Richman 2002). -/
axiom evt_implies_fan_theorem : EVT_max → FanTheorem
```

**Design decision:** Both directions of FT ↔ EVT are axiomatized.
The backward direction (EVT → FT) involves constructing a specific
continuous function from a bar, which is technically involved and
orthogonal to the paper's contribution. The forward direction
(FT → EVT) involves the uniform continuity argument on [0,1],
also standard.

The novel content is:

1. EVT_max ↔ EVT_min (negate the function)
2. EVT on [0,1] ↔ CompactOptimization on [a,b] (rescaling)
3. Part A (BISH): specific optimization is constructive
4. Stratification: FT independent of omniscience chain + MP

```lean
/-- EVT_max implies EVT_min (apply to -f). -/
theorem evt_min_of_evt_max (h : EVT_max) : EVT_min := by
  intro f hf
  obtain ⟨x, hx_mem, hx_max⟩ := h (fun t => -f t)
    (ContinuousOn.neg hf)
  exact ⟨x, hx_mem, fun y hy => by linarith [hx_max y hy]⟩

/-- EVT on [0,1] implies CompactOptimization on [a,b]. -/
theorem compact_opt_of_evt (h : EVT_min) :
    CompactOptimization := by
  intro a b hab f hf
  sorry
  -- Rescale: define g(t) = f(a + t*(b-a)) on [0,1]
  -- Apply EVT_min to g
  -- Translate the minimizer back to [a,b]

/-- CompactOptimization implies EVT on [0,1]. -/
theorem evt_of_compact_opt (h : CompactOptimization) :
    EVT_min := by
  intro f hf
  exact h 0 1 (by norm_num) f hf

/-- Main equivalence: FT ↔ CompactOptimization. -/
theorem ft_iff_compact_opt :
    FanTheorem ↔ CompactOptimization := by
  constructor
  · intro hft
    exact compact_opt_of_evt (evt_min_of_evt_max
      (fan_theorem_implies_evt hft))
  · intro hco
    exact evt_implies_fan_theorem
      (evt_max_of_evt_min (evt_of_compact_opt hco))
-- where evt_max_of_evt_min is the reverse of evt_min_of_evt_max
```

### 4.4 Part C: Hierarchy placement

```lean
/-- FT is independent of LPO (neither implies the other).
    Standard result, stated as a remark. -/
-- FT does not imply LPO: Brouwerian models satisfy FT but not LPO.
-- LPO does not imply FT: Russian recursive models satisfy LPO but not FT.

/-- For completeness: LPO, WLPO, LLPO, MP definitions. -/
def LPO : Prop :=
  ∀ α : ℕ → Bool, (∀ n, α n = false) ∨ (∃ n, α n = true)

def WLPO : Prop :=
  ∀ α : ℕ → Bool, (∀ n, α n = false) ∨ ¬(∀ n, α n = false)

def LLPO : Prop :=
  ∀ α : ℕ → Bool, AtMostOne α →
    (∀ n, α (2 * n) = false) ∨ (∀ n, α (2 * n + 1) = false)

def MarkovPrinciple : Prop :=
  ∀ α : ℕ → Bool, ¬(∀ n, α n = false) → ∃ n, α n = true

/-- The omniscience chain. -/
theorem lpo_implies_wlpo : LPO → WLPO := by sorry
theorem wlpo_implies_llpo : WLPO → LLPO := by sorry
theorem lpo_implies_mp : LPO → MarkovPrinciple := by sorry

-- FT is independent of all of these.
-- We do NOT prove FT → LPO or LPO → FT (both are false).
-- We do NOT prove FT → MP or MP → FT (both are false).
```

### 4.5 Physical instantiation

```lean
/-- The Ising free energy attains its minimum on [J_min, J_max]
    if CompactOptimization holds. -/
theorem ising_opt_of_ft (hft : FanTheorem)
    (β : ℝ) (hβ : 0 < β)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ J_star ∈ Set.Icc a b,
      ∀ J ∈ Set.Icc a b,
        isingFreeEnergy β J_star ≤ isingFreeEnergy β J := by
  exact (compact_opt_of_evt (evt_min_of_evt_max
    (fan_theorem_implies_evt hft))) a b hab
    (isingFreeEnergy β)
    (ContinuousOn.mono (isingFreeEnergy_continuous β hβ).continuousOn
      (Set.Icc_subset_univ a b))
```

### 4.6 Stratification theorem

```lean
/-- Three-branch calibration:
    1. Omniscience chain: BISH < LLPO < WLPO < LPO
    2. Markov branch: BISH < MP, LPO → MP, MP independent of LLPO/WLPO
    3. Compactness branch: BISH < FT, FT independent of LPO/MP -/
theorem calibration_partial_order :
    (WLPO → LLPO) ∧
    (LPO → WLPO) ∧
    (LPO → MarkovPrinciple) ∧
    (FanTheorem ↔ CompactOptimization) :=
  ⟨wlpo_implies_llpo, lpo_implies_wlpo,
   lpo_implies_mp, ft_iff_compact_opt⟩
```

---

## 5. Module Structure

```
Paper23_FanTheorem/
├── Defs/
│   ├── Principles.lean          -- LPO, WLPO, LLPO, MP, FT definitions
│   ├── EVT.lean                 -- EVT_max, EVT_min, CompactOptimization
│   ├── IsingFreeEnergy.lean     -- f(β,J) = -log(2cosh(βJ))
│   └── Hierarchy.lean           -- LPO→WLPO→LLPO, LPO→MP
├── PartA/
│   ├── Continuity.lean          -- Ising f.e. continuous, Lipschitz
│   ├── FiniteOpt.lean           -- Finite grid optimization (BISH)
│   └── PartA_Main.lean          -- Part A summary
├── PartB/
│   ├── EVTEquiv.lean            -- EVT_max ↔ EVT_min, rescaling
│   ├── Forward.lean             -- FT → CompactOptimization
│   ├── Backward.lean            -- CompactOptimization → FT
│   └── PartB_Main.lean          -- FT ↔ CompactOptimization
└── Main/
    ├── PhysicalInstance.lean     -- Ising optimization from FT
    ├── Stratification.lean      -- Three-branch partial order
    └── AxiomAudit.lean          -- #print axioms
```

**Estimated lines:** ~500–650 total.

### 5.1 Mathlib dependencies

**Required:**
- `Mathlib.Analysis.SpecialFunctions.Log.Basic`
- `Mathlib.Analysis.SpecialFunctions.ExpDeriv`
- `Mathlib.Topology.ContinuousOn` — ContinuousOn, continuity
- `Mathlib.Topology.Order.Basic` — for compact sets
- `Mathlib.Order.Filter.Basic` — for limits
- `Mathlib.Data.Finset.Lattice` — Finset.exists_min_image

**Key Mathlib lemmas:**
- `ContinuousOn.neg` — negation preserves continuity
- `Finset.exists_min_image` — finite optimization
- `Real.continuous_cosh`, `Real.continuous_log` — for the Ising f.e.

### 5.2 Key formalization challenges

**Challenge 1: The rescaling [0,1] ↔ [a,b].**

The affine map t ↦ a + t(b-a) sends [0,1] to [a,b]. Proving
that this map preserves continuity, sends minimizers to minimizers,
and is invertible is routine but requires care in Lean.

```lean
def rescale (a b : ℝ) (t : ℝ) : ℝ := a + t * (b - a)

theorem rescale_maps_icc (a b : ℝ) (hab : a ≤ b)
    (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    rescale a b t ∈ Set.Icc a b := by sorry

theorem rescale_continuous (a b : ℝ) :
    Continuous (rescale a b) := by sorry
```

**Challenge 2: FanTheorem definition.**

Defining the bar-theoretic Fan Theorem in Lean requires:
- Finite binary strings (List Bool or Fin n → Bool)
- The bar condition (every infinite sequence has an initial segment in B)
- The uniformity condition (∃N, ...)

This might be verbose. Alternative: use a simpler equivalent
formulation such as the decidable bar theorem or the
König's lemma dual.

**Recommendation:** Define FanTheorem abstractly and axiomatize
both directions of FT ↔ EVT. The bar-theoretic form is not
needed for any of the proofs in the paper.

```lean
/-- The Fan Theorem (abstract). We axiomatize its equivalence
    with EVT without defining the bar-theoretic form. -/
axiom FanTheorem : Prop

axiom fan_theorem_implies_evt : FanTheorem → EVT_max
axiom evt_implies_fan_theorem : EVT_max → FanTheorem
```

This is the cleanest approach: FanTheorem is an opaque Prop
whose only interface is its equivalence with EVT.

**Challenge 3: Continuous function on Set.Icc.**

Mathlib's ContinuousOn API can be finicky. The coding agent
should use `ContinuousOn f (Set.Icc a b)` rather than trying
to work with subtypes. The `restrict` function might be useful
for converting between `ContinuousOn` and `Continuous` on subtypes.

---

## 6. Axiom Audit Specification

```lean
-- Part A: no custom axioms (BISH)
#print axioms isingFreeEnergy_continuous
-- [propext, Classical.choice, Quot.sound]

#print axioms finite_opt_bish
-- [propext, Classical.choice, Quot.sound]

-- Part B: two cited axioms (FT ↔ EVT)
#print axioms ft_iff_compact_opt
-- [propext, Classical.choice, Quot.sound,
--  fan_theorem_implies_evt, evt_implies_fan_theorem]

-- Physical instantiation: uses FT axiom
#print axioms ising_opt_of_ft
-- [propext, Classical.choice, Quot.sound,
--  fan_theorem_implies_evt]

-- Hierarchy: no custom axioms
#print axioms lpo_implies_wlpo
-- [propext] or [propext, Quot.sound]

#print axioms lpo_implies_mp
-- [propext]
```

---

## 7. Potential Weaknesses and Mitigations

### 7.1 "Both directions of FT ↔ EVT are axiomatized — where's the novel proof?"

The novel content is NOT a new equivalence. FT ↔ EVT is due to
Berger (2005). The novel content is:

(a) The calibration-table placement of FT as independent of the
omniscience chain and MP — confirming the partial order structure.

(b) The BISH/FT stratification for optimization: finite optimization
is BISH, continuous optimization on compact domains requires FT.

(c) The physical interpretation: the constructive cost of "finding
the optimal coupling" in statistical mechanics.

(d) The four-level Ising stratification (BISH, WLPO, LPO, FT) for
one physical system with four different questions.

### 7.2 "The physical content is thin"

Fair criticism. The Ising free energy f(β, J) is monotone in J,
so its minimum on [J_min, J_max] is trivially at J_max. The EVT
is overkill for this specific function. The paper should acknowledge
this and frame the Ising model as an *illustrative* instance of
the general principle: compact optimization in physics requires FT.

More compelling physical examples (mentioned in the discussion but
not formalized): optimization over compact spaces of Hamiltonians,
ground state energy problems in quantum mechanics (variational
principle on compact subsets of parameter space), optimal control
in thermodynamics (entropy maximization on compact state spaces).

### 7.3 "FT being independent of LPO — is this just stated or proved?"

The independence of FT from LPO (and vice versa) is a standard
result in constructive mathematics, established through model
theory: Brouwerian models satisfy FT but not LPO; Russian
recursive models satisfy LPO but not FT. We state the independence
as a remark with citations, not as a formalized result (formalizing
independence requires constructing models, which is a different
kind of work from proving equivalences).

### 7.4 "Two axioms instead of one"

Previous papers (8, 19, 20, 21, 22) each had exactly one custom
axiom. This paper has two (fan_theorem_implies_evt and
evt_implies_fan_theorem) because both directions of FT ↔ EVT
are axiomatized. If this is aesthetically unsatisfying, one
alternative is to take FanTheorem := EVT_max as the *definition*
(rather than axiomatizing their equivalence) and note that this
definition is equivalent to the bar-theoretic form by
Berger 2005. Then there are zero custom axioms, and the "FT
calibration" is really "EVT calibration." The paper would then
say "the constructive cost of compact optimization is EVT, which
is equivalent to the Fan Theorem."

**Recommended resolution:** Define FanTheorem := EVT_max.
Then:
- ft_iff_compact_opt has ZERO custom axioms
- The connection to the bar-theoretic FT is by citation
- The axiom audit is the cleanest of any paper in the series

```lean
/-- The Fan Theorem, defined via its EVT equivalent.
    The bar-theoretic equivalence is by Berger (2005). -/
def FanTheorem : Prop := EVT_max
```

This is the approach I recommend. It gives zero axioms in the
audit while maintaining the full intellectual content.

---

## 8. References

- Berger, J. (2005). "The Fan Theorem and uniform continuity."
  In: *Reuniting the Antipodes*. Springer. [FT ↔ EVT equivalence]
- Bridges, D., Richman, F. (1987). *Varieties of Constructive
  Mathematics*. Cambridge. [FT definition, independence results]
- Bridges, D., Vîță, L. (2006). *Techniques of Constructive
  Analysis*. Springer. [FT ↔ EVT, FT ↔ uniform continuity]
- Julian, W., Richman, F. (2002). "The constructive ascending
  chain condition." [Related EVT results]
- Lee, P.C.K. (2026). Papers 8, 19, 20, 21, 22. Zenodo.
  [Programme context]
- Ishihara, H. (2006). "Constructive reverse mathematics."
  [CRM methodology]
- Bishop, E. (1967). *Foundations of Constructive Analysis*.
  McGraw-Hill. [BISH framework]

---

## 9. Summary for the Coding Agent

**What to build:** A Lean 4 project with ~500–650 lines across
~11 modules proving that compact optimization (EVT) — defined as
the Fan Theorem — is the constructive cost of continuous optimization,
with the 1D Ising free energy as physical instance.

**The critical design decision:** Define FanTheorem := EVT_max.
This eliminates all custom axioms and gives the cleanest audit.

**The hard parts:**
1. Rescaling [0,1] ↔ [a,b] for EVT_max → CompactOptimization
2. Proving the Ising free energy is continuous and Lipschitz
3. Finset.exists_min_image for finite grid optimization

**The easy parts:**
1. EVT_max ↔ EVT_min (negate the function)
2. CompactOptimization → EVT (specialize to [0,1])
3. Hierarchy proofs (reuse from previous papers)
4. Physical instantiation (apply CompactOptimization to Ising f.e.)

**Axiom budget:** ZERO custom axioms (if FanTheorem := EVT_max).

**Success criterion:** `#print axioms` shows only
[propext, Classical.choice, Quot.sound] for all theorems.
Zero `sorry`. Compiles clean.
