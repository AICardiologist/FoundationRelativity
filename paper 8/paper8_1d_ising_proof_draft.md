# Constructive Finite-Size Bounds for the 1D Ising Free Energy

## Paper 8 — Proof Draft for Lean 4 Formalization

### Paul C.-K. Lee
### February 2026

---

## 0. Purpose and Formalization Notes

This document provides a complete, step-by-step mathematical proof that the
finite-volume free energy density of the 1D Ising model converges to the
infinite-volume free energy density with explicit, constructively valid error
bounds. Every step is intended to be formalizable in Lean 4 + Mathlib.

**Key constraint:** No use of monotone convergence theorem (which costs LPO).
No use of any omniscience principle. Every argument must be valid in BISH
(Bishop-style constructive mathematics with countable/dependent choice).

**What we show:** For every rational ε > 0 and rational inverse temperature
β > 0, we can constructively compute N₀ such that for all N ≥ N₀,
|f_N(β) - f_∞(β)| < ε, where f_N is the finite-volume free energy density
and f_∞ is the infinite-volume free energy density given in closed form.

**Why this matters:** The thermodynamic limit lim f_N(β) = f_∞(β) is
classically proved via monotone convergence (LPO-strength). We bypass this
entirely by working with the explicit closed-form solution and direct
error estimates. The empirical content — "f_N approximates f_∞ within ε
for N ≥ N₀" — is BISH-available.

---

## 1. Setup: The 1D Ising Model

### 1.1 Definitions

Fix a positive integer N (the number of spins). The configuration space is
Ω_N = {-1, +1}^N. A configuration is σ = (σ₁, σ₂, ..., σ_N) with each
σ_i ∈ {-1, +1}.

**Hamiltonian (periodic boundary conditions):**

  H_N(σ) = -J · Σ_{i=1}^{N} σ_i · σ_{i+1}

where σ_{N+1} := σ₁ (periodic), and J > 0 is the coupling constant.
For simplicity we set J = 1 throughout. (The general case follows by
rescaling β.)

So:

  H_N(σ) = - Σ_{i=1}^{N} σ_i · σ_{i+1}

**Partition function:**

  Z_N(β) = Σ_{σ ∈ Ω_N} exp(-β · H_N(σ))
          = Σ_{σ ∈ Ω_N} exp(β · Σ_{i=1}^{N} σ_i · σ_{i+1})

**Finite-volume free energy density:**

  f_N(β) = -(1/N) · log Z_N(β)

### 1.2 Constructive status

For each finite N, Z_N(β) is a finite sum of exponentials of integers
multiplied by β. Given rational β > 0, each term exp(β · k) for integer k
is a well-defined positive real number. The sum Z_N(β) is a finite sum of
positive reals, hence a positive real. The logarithm of a positive real is
well-defined constructively. Division by N is trivial.

**Conclusion:** f_N(β) is constructively computable for every finite N and
rational β > 0. No omniscience principle is needed. ∎

---

## 2. Transfer Matrix Solution

### 2.1 The transfer matrix

The key to the exact solution is the transfer matrix method.

Define the 2×2 matrix T with entries indexed by s, s' ∈ {-1, +1}:

  T(s, s') = exp(β · s · s')

Explicitly:

  T = ( exp(β)    exp(-β) )
      ( exp(-β)   exp(β)  )

Note: T(s, s') = exp(β · s · s'). When s = s', we get exp(β).
When s ≠ s', we get exp(-β).

### 2.2 Partition function via transfer matrix

**Lemma 2.1 (Transfer matrix representation).**

  Z_N(β) = Tr(T^N) = λ₊^N + λ₋^N

where λ₊, λ₋ are the eigenvalues of T.

*Proof.* We rewrite Z_N using the transfer matrix:

  Z_N(β) = Σ_{σ₁,...,σ_N} Π_{i=1}^{N} exp(β · σ_i · σ_{i+1})
          = Σ_{σ₁,...,σ_N} Π_{i=1}^{N} T(σ_i, σ_{i+1})
          = Σ_{σ₁} [T^N](σ₁, σ₁)     (by summing over σ₂,...,σ_N with σ_{N+1}=σ₁)
          = Tr(T^N)

Since T is a real symmetric 2×2 matrix, it is diagonalizable with real
eigenvalues. The trace of T^N equals the sum of the N-th powers of the
eigenvalues. ∎

### 2.3 Eigenvalues of T

**Lemma 2.2 (Eigenvalues).** The eigenvalues of T are:

  λ₊ = exp(β) + exp(-β) = 2·cosh(β)
  λ₋ = exp(β) - exp(-β) = 2·sinh(β)

*Proof.* T is the matrix:

  T = ( a  b )    where a = exp(β), b = exp(-β)
      ( b  a )

This is a symmetric matrix of the form aI + b·σ_x (up to labeling).
The eigenvalues of ( a  b ; b  a ) are a + b and a - b.

  λ₊ = exp(β) + exp(-β) = 2·cosh(β)
  λ₋ = exp(β) - exp(-β) = 2·sinh(β)

The eigenvectors are (1,1)/√2 and (1,-1)/√2 respectively. ∎

### 2.4 Properties of eigenvalues

**Lemma 2.3.** For all β > 0:
  (a) λ₊ > λ₋ > 0
  (b) λ₊ > 2 (since cosh(β) > 1 for β > 0)
  (c) 0 < λ₋/λ₊ < 1
  (d) λ₋/λ₊ = tanh(β), and 0 < tanh(β) < 1 for all β > 0

*Proof.*
(a) λ₊ - λ₋ = 2·exp(-β) > 0, and λ₋ = 2·sinh(β) > 0 for β > 0.
(b) cosh(β) = 1 + β²/2 + ... > 1 for β > 0, so 2·cosh(β) > 2.
(c) Immediate from (a).
(d) λ₋/λ₊ = 2·sinh(β)/(2·cosh(β)) = tanh(β).
    tanh(β) = (exp(β)-exp(-β))/(exp(β)+exp(-β)).
    For β > 0: numerator > 0, denominator > numerator, so 0 < tanh(β) < 1. ∎

**Constructive note:** All of the above are constructively valid. The
inequalities are strict and witnessed by explicit positive gaps. For rational
β, tanh(β) is a well-defined real number strictly between 0 and 1, and the
gap 1 - tanh(β) = 2·exp(-β)/(exp(β)+exp(-β)) > 0 is constructively
witnessed.

---

## 3. Exact Free Energy Formulas

### 3.1 Finite-volume free energy density

**Lemma 3.1.** For all N ≥ 1 and β > 0:

  f_N(β) = -log(λ₊) - (1/N)·log(1 + r^N)

where r = λ₋/λ₊ = tanh(β) ∈ (0,1).

*Proof.*

  f_N(β) = -(1/N)·log(Z_N(β))
          = -(1/N)·log(λ₊^N + λ₋^N)
          = -(1/N)·log(λ₊^N · (1 + (λ₋/λ₊)^N))
          = -(1/N)·(N·log(λ₊) + log(1 + r^N))
          = -log(λ₊) - (1/N)·log(1 + r^N)   ∎

### 3.2 Infinite-volume free energy density

**Definition.** The infinite-volume free energy density is:

  f_∞(β) := -log(λ₊) = -log(2·cosh(β))

**Constructive note:** This is not defined as a limit. It is defined as
an explicit closed-form expression. For rational β > 0, f_∞(β) is a
constructively well-defined real number. No omniscience principle is needed
to define it.

The classical route defines f_∞ = lim_{N→∞} f_N, proves the limit exists
by monotone convergence (LPO), and then computes the limit. We skip the
middle step entirely: we *define* f_∞ by closed form, and then *prove*
that f_N converges to it with explicit bounds.

---

## 4. The Main Estimate (BISH-valid)

### 4.1 The error term

**Theorem 4.1 (Finite-size bound).** For all N ≥ 1 and β > 0:

  |f_N(β) - f_∞(β)| = (1/N)·log(1 + r^N)

where r = tanh(β) ∈ (0,1).

Moreover:

  0 < (1/N)·log(1 + r^N) ≤ (1/N)·r^N < (1/N)·exp(-2βN/(exp(2β)+1))

*Proof.*

**Step 1: Exact error.**

  f_N(β) - f_∞(β) = [-log(λ₊) - (1/N)·log(1 + r^N)] - [-log(λ₊)]
                    = -(1/N)·log(1 + r^N)

Since 0 < r < 1, we have 0 < r^N < 1, so 1 < 1 + r^N < 2, hence
log(1 + r^N) > 0. Therefore:

  f_N(β) - f_∞(β) = -(1/N)·log(1 + r^N) < 0

and

  |f_N(β) - f_∞(β)| = (1/N)·log(1 + r^N) > 0

**Step 2: Upper bound via log(1+x) ≤ x.**

For all x > 0, we have log(1 + x) ≤ x. (This is a standard constructive
inequality; it follows from the concavity of log, or directly from
exp(x) ≥ 1 + x.)

Applied with x = r^N:

  log(1 + r^N) ≤ r^N

Therefore:

  |f_N(β) - f_∞(β)| ≤ (1/N)·r^N

**Step 3: Exponential decay.**

Since r = tanh(β) = 1 - 2/(exp(2β)+1), we have:

  log(r) = log(tanh(β)) < 0

and r^N = exp(N·log(r)). For a simpler bound: since r < 1, we have
r^N < 1 for all N, and r^N → 0 geometrically.

More explicitly, for any β > 0:

  r = tanh(β) < 1

  r^N ≤ exp(-N·(1-r)) = exp(-2N/(exp(2β)+1))

(using the elementary inequality r ≤ exp(-(1-r)) for 0 < r < 1,
which follows from 1-r ≤ -log(r), equivalently log(r) ≤ r-1,
which is the same log(1+x) ≤ x with x = r-1.)

Wait — let me be more careful.

We want: r^N ≤ exp(-cN) for explicit c > 0.

  r^N = exp(N · log r)

  -log(r) = -log(tanh(β)) = log(cosh(β)/sinh(β)) = log(1/tanh(β))

For β > 0, -log(tanh(β)) > 0. Set c(β) = -log(tanh(β)).

Then r^N = exp(-c(β)·N).

For the explicit bound: 1 - tanh(β) = 2·exp(-β)/(exp(β)+exp(-β))
                                     = 2/(exp(2β)+1) =: δ(β)

Using -log(1-δ) ≥ δ for 0 < δ < 1:

  c(β) = -log(tanh(β)) = -log(1-δ(β)) ≥ δ(β) = 2/(exp(2β)+1)

So:

  r^N ≤ exp(-N · 2/(exp(2β)+1))

**Step 4: Combined bound.**

  |f_N(β) - f_∞(β)| ≤ (1/N) · exp(-N · c(β))

where c(β) = -log(tanh(β)) > 0.

For the weaker but cleaner bound:

  |f_N(β) - f_∞(β)| ≤ (1/N) · exp(-2N/(exp(2β)+1))   ∎

### 4.2 Constructive computability of N₀

**Corollary 4.2.** For every rational β > 0 and rational ε > 0, there
exists a constructively computable N₀ ∈ ℕ such that for all N ≥ N₀:

  |f_N(β) - f_∞(β)| < ε

*Proof.*

We need (1/N)·r^N < ε, i.e., r^N < N·ε.

Since r^N = exp(-c(β)·N) and this decreases exponentially while N·ε
grows linearly, the inequality is eventually satisfied.

Constructively, we can find N₀ by bounded search (no omniscience needed,
because we are searching for a *witness* to an inequality involving
constructively computable reals):

For each candidate N = 1, 2, 3, ..., compute the rational upper bound
(1/N)·tanh(β)^N and check whether it is less than ε. Since tanh(β)^N
decreases exponentially to 0, there exists a first N₀ where this holds,
and it can be found by finite search.

More explicitly: we need exp(-c(β)·N) < N·ε. Taking logs:
  -c(β)·N < log(N) + log(ε)
  N·c(β) > -log(ε) - log(N)
  N > (-log(ε) - log(N))/c(β)

For N ≥ max(1, ⌈-2·log(ε)/c(β)⌉), this is satisfied (since log(N) grows
much slower than N·c(β)). So:

  N₀ := max(1, ⌈-2·log(ε)/c(β)⌉ + 1)

works (with some room to spare). A tighter bound is possible but
unnecessary. ∎

---

## 5. The Dispensability Theorem

### 5.1 Main result

**Theorem 5.1 (LPO-dispensability for 1D Ising empirical content).**
For the 1D Ising model with periodic boundary conditions, the following
is provable in BISH (no omniscience principle required):

For every rational β > 0 and rational ε > 0, there exists N₀ ∈ ℕ
(constructively computable from β and ε) such that for all N ≥ N₀:

  |f_N(β) - f_∞(β)| < ε

where f_N(β) = -(1/N)·log(Tr(T^N)) and f_∞(β) = -log(2·cosh(β)).

*Proof.* This is the content of Theorem 4.1 and Corollary 4.2. Every
step uses only:
- Arithmetic of rational and real numbers (BISH)
- Finite sums and products (BISH)
- Properties of exp and log (constructive, available in Mathlib)
- The inequality log(1+x) ≤ x for x > 0 (constructive)
- The inequality -log(1-δ) ≥ δ for 0 < δ < 1 (constructive)
- Bounded search on ℕ (no omniscience needed — the search terminates
  because we have an explicit a priori upper bound on N₀)

No use of:
- Monotone convergence theorem (LPO)
- Bolzano-Weierstrass (LPO)
- Any omniscience principle (WLPO, LPO, LLPO)
- Axiom of choice beyond countable/dependent choice  ∎

### 5.2 What this means

The classical proof that f_N(β) → f_∞(β) uses the following route:

  1. Show {f_N} is bounded and monotone (uses subadditivity)
  2. Apply monotone convergence theorem (costs LPO)
  3. Identify the limit as -log(2·cosh(β)) by separate calculation

Our proof replaces steps 1-2 with a direct computation:

  1'. Define f_∞(β) = -log(2·cosh(β)) by closed form
  2'. Compute |f_N - f_∞| = (1/N)·log(1 + tanh(β)^N) explicitly
  3'. Bound the error using elementary inequalities

The empirical content — "for large enough N, f_N approximates f_∞
within ε" — is the same. But the logical cost is BISH instead of LPO.

The LPO-level monotone convergence theorem was never needed for the
*empirical prediction*. It was needed only for the *existence of the
limit as a completed infinite object*. The physical content (finite-system
approximation with error bounds) was BISH-available all along.

---

## 6. Lean 4 Formalization Guide

### 6.1 Suggested structure

```
Paper8_1DIsingBISH/
├── Basic/
│   ├── TransferMatrix.lean     -- Definition of T, eigenvalues
│   ├── Eigenvalues.lean        -- λ₊ = 2cosh(β), λ₋ = 2sinh(β)
│   └── EigenvalueProps.lean    -- λ₊ > λ₋ > 0, tanh properties
├── PartitionFunction/
│   ├── Definition.lean         -- Z_N, f_N definitions
│   ├── TraceFormula.lean       -- Z_N = Tr(T^N) = λ₊^N + λ₋^N
│   └── FreeEnergy.lean         -- f_N = -log(λ₊) - (1/N)log(1+r^N)
├── Bounds/
│   ├── LogBound.lean           -- log(1+x) ≤ x for x > 0
│   ├── ErrorBound.lean         -- |f_N - f_∞| ≤ (1/N)·r^N
│   ├── ExponentialDecay.lean   -- r^N ≤ exp(-c(β)·N)
│   └── ComputeN0.lean         -- Constructive N₀ from β, ε
└── Main/
    └── Dispensability.lean     -- Main theorem: BISH-validity
```

### 6.2 Key Mathlib dependencies

The formalization will need:

1. **Real.exp, Real.log** — exponential and logarithm on ℝ
2. **Real.cosh, Real.sinh, Real.tanh** — hyperbolic functions
   (check Mathlib availability; may need to define as
   cosh x = (exp x + exp(-x))/2)
3. **Matrix.trace** — trace of a matrix (available in Mathlib)
4. **Matrix.eigenvalues** — for 2×2 symmetric matrices
   (may be easier to prove eigenvalue formulas directly for
   the specific matrix T, rather than using general spectral theory)
5. **Real.log_le_sub_one_of_le** or similar — for log(1+x) ≤ x
6. **Finset.sum** — finite sums over {-1,+1}^N

### 6.3 Potential pain points

**Issue 1: Configuration space.** Representing {-1,+1}^N as a type and
summing over it. Options:
- Use Fin N → Bool (or Fin N → ZMod 2)
- Use Fin N → {-1, 1} as a subtype of ℤ
- Recommended: Fin N → Bool, with a coercion to ±1 for the Hamiltonian

**Issue 2: Transfer matrix trace formula.** The identity Z_N = Tr(T^N)
is a standard result but requires careful handling of the periodic boundary
condition. The cleanest approach:
- Define T as Matrix (Fin 2) (Fin 2) ℝ
- Show Z_N = Σ_{s ∈ Fin 2} (T^N)(s, s) by expanding the sum
- This requires the associativity of matrix multiplication applied N times

**Issue 3: Eigenvalue computation.** For the specific 2×2 matrix T,
computing eigenvalues can be done directly:
- T = a·I + b·σ_x where a = cosh(β), b = sinh(β) (after rescaling)
  Actually: T(0,0) = T(1,1) = exp(β), T(0,1) = T(1,0) = exp(-β)
- Eigenvalues of (a b; b a) are a+b and a-b
- Prove this by direct computation: T · v = λ · v for v = (1,1) and (1,-1)

**Issue 4: Positivity of tanh.** Need to show 0 < tanh(β) < 1 for β > 0.
This follows from sinh(β) > 0 and cosh(β) > sinh(β) for β > 0.

**Issue 5: The bound log(1+x) ≤ x.** This may already be in Mathlib as
`Real.add_one_le_exp` (which states 1 + x ≤ exp(x), equivalent to
log(1+x) ≤ x for x > -1) or as `Real.log_le_sub_one_of_le`. Check
Mathlib search.

### 6.4 Suggested formalization order

1. Define cosh, sinh, tanh if not in Mathlib. Prove basic properties.
2. Define T as a concrete 2×2 matrix. Prove its eigenvalues.
3. Prove Z_N = λ₊^N + λ₋^N (this is the main algebraic content).
4. Define f_N and f_∞. Prove f_N - f_∞ = -(1/N)·log(1 + r^N).
5. Prove log(1+x) ≤ x. Derive |f_N - f_∞| ≤ (1/N)·r^N.
6. Prove the exponential decay bound.
7. Construct N₀ from β, ε. Prove the main theorem.

### 6.5 Alternative: bypass transfer matrix

If the transfer matrix formalization proves too heavy (matrix powers,
trace), there is a simpler approach for the 1D Ising model:

**Direct computation for periodic chain:**

Z_N(β) counts configurations by the number of "domain walls" (adjacent
anti-aligned spins). If there are k domain walls in a periodic chain of
N spins, the energy is -N + 2k (since each aligned pair contributes -1
and each anti-aligned pair contributes +1). Domain walls in a periodic
chain must come in even numbers. So:

  Z_N(β) = Σ_{k=0}^{⌊N/2⌋} C(N, 2k) · exp(β(N - 2·2k))
          ... this gets complicated.

Actually, the transfer matrix approach is cleaner. The key identity
Z_N = λ₊^N + λ₋^N can also be proved by induction:

**Induction approach (possibly simpler to formalize):**

Define a_N = Σ_{σ₂,...,σ_N} T(+1,σ₂)·T(σ₂,σ₃)···T(σ_{N-1},σ_N)·T(σ_N,+1)
       b_N = Σ_{σ₂,...,σ_N} T(+1,σ₂)·T(σ₂,σ₃)···T(σ_{N-1},σ_N)·T(σ_N,-1)

(a_N = amplitude for path starting and ending at +1)
(b_N = amplitude for path starting at +1 and ending at -1)

Then Z_N = a_N + (similar term starting at -1) = 2·a_N by symmetry.

Wait, more carefully: Z_N = Tr(T^N). If we write T^N in terms of its
eigendecomposition:

  T = λ₊ · P₊ + λ₋ · P₋

where P₊ = (1/2)(I + σ_x), P₋ = (1/2)(I - σ_x) are the projectors.
Then T^N = λ₊^N · P₊ + λ₋^N · P₋, and Tr(T^N) = λ₊^N + λ₋^N since
Tr(P₊) = Tr(P₋) = 1.

This decomposition is probably the cleanest thing to formalize:
prove T = λ₊·P₊ + λ₋·P₋ by explicit matrix computation, then
T^N = λ₊^N·P₊ + λ₋^N·P₋ by induction (using P₊² = P₊, P₋² = P₋,
P₊·P₋ = 0), then take the trace.

---

## 7. Precise Statement for Lean

The final theorem to formalize, stated precisely:

```
theorem ising_1d_bish_bound
  (β : ℝ) (hβ : 0 < β) (ε : ℝ) (hε : 0 < ε) :
  ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    |-(1 / (N : ℝ)) * Real.log ((2 * Real.cosh β) ^ N + (2 * Real.sinh β) ^ N)
     - (-(Real.log (2 * Real.cosh β)))| < ε := by
  sorry
```

Or more readably, with definitions:

```
noncomputable def transferEigenPlus (β : ℝ) : ℝ := 2 * Real.cosh β
noncomputable def transferEigenMinus (β : ℝ) : ℝ := 2 * Real.sinh β

noncomputable def partitionFn (β : ℝ) (N : ℕ) : ℝ :=
  (transferEigenPlus β) ^ N + (transferEigenMinus β) ^ N

noncomputable def freeEnergyDensity (β : ℝ) (N : ℕ) (hN : 0 < N) : ℝ :=
  -(1 / (N : ℝ)) * Real.log (partitionFn β N)

noncomputable def freeEnergyInfVol (β : ℝ) : ℝ :=
  -Real.log (transferEigenPlus β)

theorem ising_1d_dispensability
  (β : ℝ) (hβ : 0 < β) (ε : ℝ) (hε : 0 < ε) :
  ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N → (hN : 0 < N) →
    |freeEnergyDensity β N hN - freeEnergyInfVol β| < ε := by
  sorry
```

### 7.1 Key intermediate lemmas to formalize

```
-- Eigenvalue properties
lemma eigenPlus_pos (β : ℝ) (hβ : 0 < β) :
    0 < transferEigenPlus β := by sorry

lemma eigenMinus_pos (β : ℝ) (hβ : 0 < β) :
    0 < transferEigenMinus β := by sorry

lemma eigenPlus_gt_eigenMinus (β : ℝ) (hβ : 0 < β) :
    transferEigenMinus β < transferEigenPlus β := by sorry

-- Ratio property
lemma eigenRatio_eq_tanh (β : ℝ) (hβ : 0 < β) :
    transferEigenMinus β / transferEigenPlus β = Real.tanh β := by sorry

lemma tanh_pos (β : ℝ) (hβ : 0 < β) : 0 < Real.tanh β := by sorry
lemma tanh_lt_one (β : ℝ) (hβ : 0 < β) : Real.tanh β < 1 := by sorry

-- Free energy decomposition
lemma freeEnergy_decomp (β : ℝ) (hβ : 0 < β) (N : ℕ) (hN : 0 < N) :
    freeEnergyDensity β N hN =
      -Real.log (transferEigenPlus β)
      - (1 / (N : ℝ)) * Real.log (1 + (Real.tanh β) ^ N) := by sorry

-- Error bound
lemma freeEnergy_error (β : ℝ) (hβ : 0 < β) (N : ℕ) (hN : 0 < N) :
    |freeEnergyDensity β N hN - freeEnergyInfVol β| =
      (1 / (N : ℝ)) * Real.log (1 + (Real.tanh β) ^ N) := by sorry

-- log(1+x) ≤ x bound
lemma log_one_add_le (x : ℝ) (hx : 0 < x) :
    Real.log (1 + x) ≤ x := by sorry

-- Main error estimate
lemma freeEnergy_error_bound (β : ℝ) (hβ : 0 < β) (N : ℕ) (hN : 0 < N) :
    |freeEnergyDensity β N hN - freeEnergyInfVol β| ≤
      (1 / (N : ℝ)) * (Real.tanh β) ^ N := by sorry
```

---

## 8. What Comes Next

If this formalization succeeds, we have:

**Paper 8 result:** The empirical content of the 1D Ising thermodynamic
limit is BISH-derivable. The LPO-level monotone convergence theorem is
dispensable for finite-system predictions with explicit error bounds.

**Calibration landscape update:**
- BISH: finite-volume physics AND finite-size approximations (calibrated)
- WLPO ↔ bidual-gap witness (calibrated)
- LPO: thermodynamic limit as completed object (route-costed, and now
  shown to be dispensable for empirical content in at least one model)

**Next target (Paper 9?):** Attempt the LPO equivalence (Candidate 2 from
the roadmap). If free energy convergence for *general* translation-invariant
Hamiltonians is equivalent to LPO, we'd have three calibrated rungs.

---

## Appendix: Elementary Inequalities Needed

For reference, the constructive inequalities used in the proof:

**A1.** For x > 0: log(1 + x) ≤ x.
*Proof:* Equivalent to 1 + x ≤ exp(x). The Taylor series
exp(x) = 1 + x + x²/2 + ... ≥ 1 + x for x > 0. ∎

**A2.** For 0 < δ < 1: -log(1 - δ) ≥ δ.
*Proof:* Equivalent to A1 with x = δ/(1-δ)... actually, more directly:
log(1-δ) ≤ -δ is equivalent to 1-δ ≤ exp(-δ), which is equivalent to
exp(δ) ≤ 1/(1-δ) = 1 + δ + δ² + .... Since exp(δ) = 1 + δ + δ²/2 + ...
and 1/(1-δ) = 1 + δ + δ² + δ³ + ..., we need δ^n/n! ≤ δ^n for all n ≥ 1,
which is not quite right.

Better: A2 is equivalent to exp(δ) ≥ 1/(1-δ) for 0 < δ < 1. Hmm, that's
the wrong direction.

Let me redo. We want: -log(1-δ) ≥ δ, i.e., log(1-δ) ≤ -δ.
Equivalently: 1 - δ ≤ exp(-δ).
This is just A1 applied to exp: exp(-δ) ≥ 1 + (-δ) = 1 - δ. ✓

So A2 follows from exp(x) ≥ 1 + x for all x ∈ ℝ (applied with x = -δ).

**A3.** For 0 < r < 1 and N ≥ 1: r^N ≤ exp(-N·(1-r)).
*Proof:* r = 1-(1-r). Set δ = 1-r > 0. Then r = 1-δ ≤ exp(-δ) by A1
(applied as exp(δ) ≥ 1+δ, so 1-δ ≤ exp(-δ)). Hence r^N ≤ exp(-δ)^N
= exp(-Nδ) = exp(-N(1-r)). ∎

All three inequalities are constructively valid (they follow from the
constructive Taylor series expansion of exp).
