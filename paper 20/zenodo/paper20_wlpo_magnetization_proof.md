# WLPO Equivalence via Ising Magnetization Phase Classification

## Paper 20 — Proof Document for Lean 4 Formalization

### Paul C.-K. Lee
### February 2026

---

## 0. Purpose, Context, and Design Principles

### 0.1 What this paper proves

This paper establishes that the phase classification of the 1D Ising
model — deciding whether the infinite-volume magnetization equals zero
or not — is equivalent to WLPO (Weak Limited Principle of Omniscience)
over BISH. This is the first paper in the CRM programme to calibrate
WLPO against a physical observable, and the first to demonstrate
**observable-dependent logical cost** within a single physical system:
the same 1D Ising model whose free energy convergence costs LPO
(Paper 8) has a magnetization zero-test that costs exactly WLPO.

The paper has three parts:

- **Part A (BISH):** For any finite volume N, external field h, and
  inverse temperature β > 0, the magnetization m(N, β, h) is
  computable with explicit error bounds. No omniscience principles.

- **Part B (WLPO calibration):** The assertion "m(∞, β, h) = 0 or
  m(∞, β, h) ≠ 0" — phase classification in the thermodynamic limit
  — is equivalent to WLPO over BISH.

- **Part C (Stratification):** Combined with Paper 8, the 1D Ising
  model exhibits stratified logical cost: free energy convergence
  costs LPO, phase classification costs WLPO, finite-volume
  computation is BISH. Three levels of the constructive hierarchy
  manifest in three different questions about one physical system.

### 0.2 The key insight

The 1D Ising model has **no spontaneous magnetization** at any
temperature (the Ising model in one dimension is paramagnetic). This
means the infinite-volume magnetization satisfies:

  m(∞, β, h) = 0  ⟺  h = 0

The external field h is the sole source of magnetization. This makes
the 1D model *ideal* for a WLPO encoding: the zero-test on the
magnetization reduces exactly to a zero-test on the field, which is
exactly what WLPO decides.

This is counterintuitive. The research plan (Project 2) proposed
using the 2D Ising model, which has genuine spontaneous symmetry
breaking, to get WLPO content. But the 2D model is vastly harder
to formalize (Onsager solution, elliptic integrals) and the WLPO
content there is entangled with the LPO content of the phase
transition itself. The 1D model, precisely because it *lacks* a
phase transition, gives a clean separation: the LPO cost (free
energy limit, Paper 8) and the WLPO cost (magnetization zero-test,
this paper) are independent.

### 0.3 Relationship to existing papers

- **Paper 7** proved WLPO ↔ non-reflexivity of S₁(H) (bidual gap).
  That was a functional analysis result. This paper proves WLPO
  equivalence for a statistical mechanics observable. Different
  physics, same principle.

- **Paper 8** proved LPO ↔ BMC for the 1D Ising free energy
  convergence. This paper extends Paper 8 by adding the
  magnetization and external field. Same model, different observable,
  different principle.

- **Paper 19** (in progress) proved LLPO ↔ IVT for WKB turning
  points. That's the third principle in the post-LPO programme.
  This paper and Paper 19 together establish that WLPO and LLPO
  both have clean physical instantiations, confirming the expanded
  toolbox is productive.

### 0.4 Dependencies on Paper 8

This formalization reuses the following from Paper 8:

- `TransferMatrix.lean` — transfer matrix definition T(β, J)
- `Eigenvalues.lean` — eigenvalue formulas λ₊, λ₋
- `EigenvalueProps.lean` — positivity, ordering, tanh properties
- `PartitionFn.lean` — Z_N definition
- `FreeEnergy.lean` — f_N, f_∞ definitions
- LPO/BMC definitions from `PartB_Defs.lean`

New modules extend this infrastructure with the external field h,
the asymmetric transfer matrix, the magnetization, and the WLPO
encoding.

### 0.5 What the coding agent should NOT do

- Do NOT import `Classical.em` or `Classical.byContradiction` in
  Part A modules. The BISH content must be verifiably
  omniscience-free.
- Do NOT use `Decidable` instances from Mathlib that import LEM
  silently. Check `#print axioms` on every theorem.
- Do NOT attempt to formalize the 2D Ising model or Onsager solution.
  Everything here is 1D with transfer matrices of size 2×2.
- Do NOT re-prove Paper 8 results. Import them or axiomatize them
  with citation.

---

## 1. Mathematical Setup

### 1.1 The 1D Ising model with external field

The Hamiltonian for the 1D Ising model on N sites with periodic
boundary conditions, coupling J > 0, and external field h ∈ ℝ is:

  H_N(σ) = -J · Σ_{i=0}^{N-1} σ_i · σ_{i+1 mod N}
            - h · Σ_{i=0}^{N-1} σ_i

where σ_i ∈ {-1, +1}.

**Lean type:**
```lean
def hamiltonian_h (N : ℕ) (J h β : ℝ) (σ : Fin N → Bool) : ℝ :=
  - J * (Finset.univ.sum fun i =>
    spin σ i * spin σ (Fin.cycle i))
  - h * (Finset.univ.sum fun i => spin σ i)
```

where `spin σ i = if σ i then (1 : ℝ) else (-1 : ℝ)` and
`Fin.cycle i` is `⟨(i.val + 1) % N, ...⟩`.

### 1.2 The transfer matrix with external field

The transfer matrix generalizes Paper 8's T(β, J) to include h:

  T(β, J, h) = ⎡ exp(βJ + βh)    exp(-βJ)      ⎤
                ⎣ exp(-βJ)         exp(βJ - βh)  ⎦

Note: this is **not symmetric** when h ≠ 0. Paper 8 used the
symmetric case h = 0.

**Lean type:**
```lean
def transferMatrix_h (β J h : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.exp (β * J + β * h), Real.exp (-(β * J));
     Real.exp (-(β * J)),       Real.exp (β * J - β * h)]
```

### 1.3 Eigenvalues of T(β, J, h)

The characteristic equation is:

  λ² - (2 · exp(βJ) · cosh(βh)) · λ + (2 · sinh(2βJ)) = 0

Wait — let me be more careful. The trace is:

  tr(T) = exp(βJ + βh) + exp(βJ - βh) = 2 · exp(βJ) · cosh(βh)

The determinant is:

  det(T) = exp(βJ + βh) · exp(βJ - βh) - exp(-βJ) · exp(-βJ)
         = exp(2βJ) - exp(-2βJ)
         = 2 · sinh(2βJ)

So the eigenvalues are:

  λ± = exp(βJ) · cosh(βh) ± √(exp(2βJ) · cosh²(βh) - 2 · sinh(2βJ))

Simplify the discriminant:

  Δ = exp(2βJ) · cosh²(βh) - 2 · sinh(2βJ)
    = exp(2βJ) · cosh²(βh) - (exp(2βJ) - exp(-2βJ))
    = exp(2βJ) · (cosh²(βh) - 1) + exp(-2βJ)
    = exp(2βJ) · sinh²(βh) + exp(-2βJ)

Therefore:

  λ± = exp(βJ) · cosh(βh) ± √(exp(2βJ) · sinh²(βh) + exp(-2βJ))

**Special case h = 0:** sinh(0) = 0, so Δ = exp(-2βJ), and
λ₊ = exp(βJ) + exp(-βJ) = 2·cosh(βJ), λ₋ = exp(βJ) - exp(-βJ) = 2·sinh(βJ).
Recovers Paper 8.

**Key properties (to be proved):**

1. **λ₊ > λ₋ > 0** for all β > 0, J > 0, h ∈ ℝ.

   Proof sketch: λ₊ - λ₋ = 2√Δ > 0 since Δ > 0 (it contains
   the term exp(-2βJ) > 0). λ₋ > 0 because:
   λ₋ = exp(βJ)·cosh(βh) - √Δ, and we need
   exp(βJ)·cosh(βh) > √Δ, i.e., exp(2βJ)·cosh²(βh) > Δ =
   exp(2βJ)·sinh²(βh) + exp(-2βJ). This simplifies to
   exp(2βJ)·(cosh²(βh) - sinh²(βh)) > exp(-2βJ), i.e.,
   exp(2βJ) > exp(-2βJ), which holds for βJ > 0. ∎

2. **λ₊(β, J, 0) = 2·cosh(βJ)** — consistency with Paper 8.

3. **Ratio bound:** λ₋/λ₊ < 1 for all β > 0, J > 0, h ∈ ℝ.
   Follows from λ₊ > λ₋ > 0.

**Lean signatures:**
```lean
def eigenPlus_h (β J h : ℝ) : ℝ :=
  Real.exp (β * J) * Real.cosh (β * h) +
  Real.sqrt (Real.exp (2 * β * J) * (Real.sinh (β * h))^2 +
             Real.exp (-(2 * β * J)))

def eigenMinus_h (β J h : ℝ) : ℝ :=
  Real.exp (β * J) * Real.cosh (β * h) -
  Real.sqrt (Real.exp (2 * β * J) * (Real.sinh (β * h))^2 +
             Real.exp (-(2 * β * J)))

theorem eigenPlus_h_pos (hβ : 0 < β) (hJ : 0 < J) (h : ℝ) :
    0 < eigenPlus_h β J h := sorry

theorem eigenMinus_h_pos (hβ : 0 < β) (hJ : 0 < J) (h : ℝ) :
    0 < eigenMinus_h β J h := sorry

theorem eigenPlus_gt_eigenMinus (hβ : 0 < β) (hJ : 0 < J) (h : ℝ) :
    eigenMinus_h β J h < eigenPlus_h β J h := sorry

theorem eigenPlus_h_zero (hβ : 0 < β) (hJ : 0 < J) :
    eigenPlus_h β J 0 = 2 * Real.cosh (β * J) := sorry
```

### 1.4 Partition function and free energy

As in Paper 8:

  Z_N(β, J, h) = λ₊(β,J,h)^N + λ₋(β,J,h)^N

  f_N(β, J, h) = -(1/N) · log(Z_N) = -log(λ₊) - (1/N)·log(1 + r^N)

where r = λ₋/λ₊ < 1.

The thermodynamic limit:

  f_∞(β, J, h) = -log(λ₊(β, J, h))

The convergence f_N → f_∞ and the error bound |f_N - f_∞| ≤ (1/N)·r^N
follow from Paper 8's machinery, generalized to h ≠ 0. The proofs
are identical — they depend only on r < 1, not on the specific form
of λ±.

---

## 2. The Magnetization

### 2.1 Finite-volume magnetization

The magnetization per site is:

  m(N, β, J, h) = (1/N) · ∂(log Z_N)/∂(βh)
                 = (1/N) · (1/Z_N) · ∂Z_N/∂(βh)

Using Z_N = λ₊^N + λ₋^N:

  ∂Z_N/∂(βh) = N · λ₊^{N-1} · (∂λ₊/∂(βh)) + N · λ₋^{N-1} · (∂λ₋/∂(βh))

So:

  m(N, β, J, h) = [λ₊^{N-1} · λ₊' + λ₋^{N-1} · λ₋'] / [λ₊^N + λ₋^N]

where λ±' = ∂λ±/∂(βh).

### 2.2 Derivatives of eigenvalues

From the eigenvalue formulas:

  ∂λ±/∂(βh) = exp(βJ) · sinh(βh) ± [exp(2βJ) · sinh(βh) · cosh(βh)] / √Δ

where Δ = exp(2βJ) · sinh²(βh) + exp(-2βJ) as before.

**Special case h = 0:**

  ∂λ₊/∂(βh)|_{h=0} = 0 + 0/√(exp(-2βJ)) = 0
  ∂λ₋/∂(βh)|_{h=0} = 0 - 0/√(exp(-2βJ)) = 0

Both vanish at h = 0 because sinh(0) = 0 appears as a factor in
every term.

Therefore: **m(N, β, J, 0) = 0 for all N.** The finite-volume
magnetization vanishes at zero field.

### 2.3 Infinite-volume magnetization

In the thermodynamic limit (N → ∞), the λ₋ terms are suppressed
(since r = λ₋/λ₊ < 1, so λ₋^{N-1}/λ₊^N → 0). The infinite-volume
magnetization is:

  m(∞, β, J, h) = λ₊'/λ₊ = ∂(log λ₊)/∂(βh)
                 = -∂f_∞/∂(βh)

Explicitly:

  m(∞, β, J, h) = [exp(βJ) · sinh(βh) + exp(2βJ) · sinh(βh) · cosh(βh) / √Δ]
                   / [exp(βJ) · cosh(βh) + √Δ]

**The crucial property:**

  m(∞, β, J, h) = 0  ⟺  h = 0

Proof:
(⟸) If h = 0, then sinh(βh) = 0 factors out of the numerator, so
m(∞, β, J, 0) = 0.

(⟹) If h ≠ 0, then sinh(βh) ≠ 0, and the numerator has the form
sinh(βh) · [positive stuff] ≠ 0, while the denominator is strictly
positive. So m(∞) ≠ 0. ∎

More precisely, for h > 0: every term in the numerator is positive,
so m(∞) > 0. For h < 0: sinh(βh) < 0, so m(∞) < 0. The
magnetization is a strictly monotone, odd function of h with
m(∞, β, J, 0) = 0 as its unique root.

### 2.4 Closed-form simplification (for Lean)

The infinite-volume magnetization has the well-known closed form:

  m(∞, β, J, h) = sinh(βh) / √(sinh²(βh) + exp(-4βJ))

**Derivation:** Start from m = ∂(log λ₊)/∂(βh). Using
λ₊ = exp(βJ)·cosh(βh) + √(exp(2βJ)·sinh²(βh) + exp(-2βJ)),
differentiate and simplify (algebraically tedious but routine).
The result is the formula above.

**Verification at h = 0:** m = 0/√(0 + exp(-4βJ)) = 0. ✓

**Verification for h ≠ 0:** The denominator √(sinh²(βh) + exp(-4βJ))
is strictly positive for all h, β, J. The numerator sinh(βh) ≠ 0
iff h ≠ 0. So m = 0 iff h = 0. ✓

**This is the formula to formalize.** It is a closed-form expression
involving only sinh, exp, and sqrt — all available in Mathlib. No
limits, no series, no functional analysis.

**Lean signature:**
```lean
def magnetization_inf (β J h : ℝ) : ℝ :=
  Real.sinh (β * h) /
  Real.sqrt ((Real.sinh (β * h))^2 + Real.exp (-(4 * β * J)))

theorem magnetization_inf_eq_zero_iff (hβ : 0 < β) (hJ : 0 < J) (h : ℝ) :
    magnetization_inf β J h = 0 ↔ h = 0 := sorry

theorem magnetization_inf_pos_of_pos (hβ : 0 < β) (hJ : 0 < J) {h : ℝ}
    (hh : 0 < h) :
    0 < magnetization_inf β J h := sorry
```

### 2.5 Finite-volume magnetization and convergence

The finite-volume magnetization also has a useful form. Using
Z_N = λ₊^N · (1 + r^N) where r = λ₋/λ₊:

  m(N, β, J, h) = [λ₊' + r^{N-1} · λ₋'] / [λ₊ · (1 + r^N)]
                   + correction terms of order r^N

The convergence m(N) → m(∞) as N → ∞ holds with exponential rate,
analogous to the free energy convergence. The error is O(r^N).

For the WLPO encoding, we need the finite-volume magnetization
only to establish that m(N, β, J, 0) = 0 for all N (which follows
from the symmetry of the h = 0 Hamiltonian under σ → -σ) and that
the convergence to m(∞) is constructively established.

**Lean signature:**
```lean
theorem magnetization_finite_zero_field (N : ℕ) (hN : 0 < N)
    (hβ : 0 < β) (hJ : 0 < J) :
    magnetization_finite N β J 0 = 0 := sorry
```

---

## 3. Part A: BISH Computability of Finite-Volume Magnetization

### 3.1 Statement

**Theorem (Part A).** For any N ≥ 1, β > 0, J > 0, h ∈ ℝ, and
ε > 0, the magnetization m(N, β, J, h) is computable: there exists
a rational approximation q with |m(N, β, J, h) - q| < ε, and this
q is constructible from N, β, J, h, ε using only BISH operations
(finite sums, elementary functions, rational arithmetic).

### 3.2 Proof

The magnetization m(N, β, J, h) = sinh(βh) / √(sinh²(βh) + exp(-4βJ))
(in the infinite-volume case) or the finite-sum expression (in the
finite-volume case) involves only:

1. Finite sums over 2^N spin configurations — BISH.
2. Real exponentials exp(x) — computable for any computable x.
3. Hyperbolic functions sinh, cosh — computable (defined via exp).
4. Square roots of positive reals — computable in BISH.
5. Division by a known-positive denominator — computable.

No limits, suprema, or infima are involved for fixed N.

**Axiom audit:** The proof uses only constructive real arithmetic.
No omniscience principles (LPO, WLPO, LLPO) appear. The only
Lean axioms should be propext, Quot.sound, and Classical.choice
(ambient metatheory). ∎

**Lean signature:**
```lean
theorem magnetization_finite_computable (N : ℕ) (hN : 0 < N)
    (β J h : ℝ) (hβ : 0 < β) (hJ : 0 < J) (ε : ℝ) (hε : 0 < ε) :
    ∃ q : ℚ, |magnetization_finite N β J h - (q : ℝ)| < ε := sorry
```

### 3.3 The h = 0 symmetry

For h = 0, the Hamiltonian is invariant under the global spin flip
σ → -σ (i.e., σ_i ↦ -σ_i for all i). This is the Z₂ symmetry
of the Ising model without external field.

Under this symmetry:
- H_N(σ) is invariant (both coupling and field terms change sign
  twice, but with h = 0 the field term vanishes)
- Z_N is invariant (sum over all configurations is re-indexed)
- The magnetization M_N(σ) = Σ σ_i changes sign

Therefore the thermal average ⟨M_N⟩ = 0 by symmetry, and
m(N, β, J, 0) = ⟨M_N⟩/N = 0.

This is a BISH result — the symmetry argument uses only the
bijection σ ↦ -σ on the finite configuration space.

**Lean approach:** Define the spin-flip map
`spinFlip : (Fin N → Bool) → (Fin N → Bool)` by
`spinFlip σ i = !(σ i)`. Prove it's a bijection on `Fin N → Bool`.
Prove `hamiltonian_h N J 0 (spinFlip σ) = hamiltonian_h N J 0 σ`.
Prove `totalMagnetization (spinFlip σ) = -totalMagnetization σ`.
Conclude `⟨M⟩ = 0` by the bijective pairing argument on the
Boltzmann sum.

```lean
def spinFlip (σ : Fin N → Bool) : Fin N → Bool := fun i => !(σ i)

theorem spinFlip_involutive : Function.Involutive (spinFlip (N := N)) := sorry

theorem hamiltonian_h_spinFlip_zero_field (N : ℕ) (J β : ℝ) (σ : Fin N → Bool) :
    hamiltonian_h N J 0 β (spinFlip σ) = hamiltonian_h N J 0 β σ := sorry

theorem totalMag_spinFlip (σ : Fin N → Bool) :
    totalMagnetization (spinFlip σ) = -totalMagnetization σ := sorry

theorem magnetization_finite_zero_field' (N : ℕ) (hN : 0 < N) (β J : ℝ)
    (hβ : 0 < β) (hJ : 0 < J) :
    magnetization_finite N β J 0 = 0 := sorry
-- Proof: pair each σ with spinFlip σ in the Boltzmann sum.
-- The magnetization contributions cancel in pairs.
```

---

## 4. Part B: WLPO Calibration

### 4.1 WLPO definition

The Weak Limited Principle of Omniscience:

  WLPO : ∀ α : ℕ → Bool, (∀ n, α n = false) ∨ ¬(∀ n, α n = false)

Equivalently: for any binary sequence, either it is identically zero,
or it is not identically zero. Note the negation in the second
disjunct — WLPO gives ¬(∀n, α(n) = 0), not ∃n (α(n) = 1). This
is strictly weaker than LPO.

**Lean definition:**
```lean
def WLPO : Prop :=
  ∀ α : ℕ → Bool, (∀ n, α n = false) ∨ ¬(∀ n, α n = false)
```

### 4.2 The encoding: binary sequence → external field

Given α : ℕ → Bool, define the encoded external field:

  h_α := Σ_{n=0}^{∞} (if α(n) = true then 2^{-(n+1)} else 0)

This is a convergent series in [0, 1] (geometric bound).

**Key property:**

  h_α = 0  ⟺  ∀n, α(n) = false

Proof:
(⟸) If all α(n) = false, every term is 0, so h_α = 0.
(⟹) If h_α = 0, then since each term is non-negative (0 or 2^{-(n+1)}),
every term must be 0, so α(n) = false for all n.

More precisely, h_α ≥ 2^{-(n+1)} whenever α(n) = true (the n-th
term alone contributes this much). So if α(n) = true for some n,
then h_α ≥ 2^{-(n+1)} > 0, hence h_α ≠ 0. Contrapositive: h_α = 0
implies ∀n, α(n) = false. ∎

**Constructive note:** The series h_α converges constructively.
The partial sums s_k = Σ_{n=0}^{k} ... form a bounded (by 1)
non-decreasing sequence, and we have explicit modulus of Cauchy
convergence: for k ≥ k₀, |h_α - s_k| ≤ 2^{-k}. This does NOT
require LPO — the convergence is by explicit geometric bound, not
by bounded monotone convergence.

**Wait — does it require LPO?**

This is a critical question. The series Σ α(n) · 2^{-(n+1)} is a
bounded monotone (non-decreasing) sequence of partial sums. In
general, bounded monotone convergence requires LPO (that's Paper 8's
result). But here the partial sums have a Cauchy modulus independent
of α: |s_m - s_k| ≤ 2^{-min(m,k)} for all α. This is because the
tail sum is bounded by a geometric series regardless of which terms
are nonzero. So the convergence is BISH — it's the explicit-rate
case where the Cauchy modulus doesn't depend on knowing which terms
are nonzero.

**Lean construction:**
```lean
noncomputable def encodedField (α : ℕ → Bool) : ℝ :=
  tsum fun n => if α n then (2 : ℝ)⁻¹ ^ (n + 1) else 0

theorem encodedField_converges (α : ℕ → Bool) :
    Summable fun n => if α n then (2 : ℝ)⁻¹ ^ (n + 1) else 0 := sorry
-- Bounded by geometric series Σ 2^{-(n+1)} = 1

theorem encodedField_nonneg (α : ℕ → Bool) :
    0 ≤ encodedField α := sorry
-- Each term is non-negative

theorem encodedField_le_one (α : ℕ → Bool) :
    encodedField α ≤ 1 := sorry
-- Bounded by Σ 2^{-(n+1)} = 1

theorem encodedField_eq_zero_iff (α : ℕ → Bool) :
    encodedField α = 0 ↔ ∀ n, α n = false := sorry
-- Forward: h = 0, each term ≥ 0, so each term = 0
-- Backward: all terms are 0, so sum is 0
```

### 4.3 Forward direction: WLPO → phase classification

**Theorem.** Assume WLPO. Then for any β > 0, J > 0, h ∈ ℝ:
either m(∞, β, J, h) = 0 or m(∞, β, J, h) ≠ 0.

**Proof.** Since m(∞, β, J, h) = 0 ↔ h = 0 (§2.4), it suffices
to decide h = 0 or h ≠ 0. This is a real-number zero-test.

Actually, WLPO as stated decides binary sequences, not real numbers.
We need the equivalence:

  WLPO ⟺ ∀ x : ℝ, x = 0 ∨ ¬(x = 0)

This is a known equivalence (see Bridges–Richman 1987, or
Bridges–Vîță 2006 Ch. 1). The forward direction (WLPO for sequences
implies WLPO for reals) uses the Cauchy representation: a real
x = 0 iff its Cauchy sequence (x_n) is eventually 0, which reduces
to a binary sequence zero-test.

**Alternative approach (cleaner for formalization):** Don't use the
general real-WLPO equivalence. Instead, directly construct the
decision for h:

Given h ∈ ℝ with Cauchy representation (q_n), define
α(n) = (if |q_n| > 2^{-(n+1)} then true else false). This is
decidable (rational comparison). Then:
- h = 0 ⟹ eventually |q_n| < 2^{-(n+1)}, so eventually α(n) = false
  ... but this doesn't give ∀n, α(n) = false.

Hmm, this approach is messy. Let's use the standard route.

**Standard route:** WLPO for reals is a known consequence of WLPO
for binary sequences. Axiomatize this as:

```lean
axiom wlpo_real_of_wlpo (hw : WLPO) (x : ℝ) : x = 0 ∨ x ≠ 0
```

with citation to Bridges–Richman. Then the forward direction is
immediate:

```lean
theorem phase_classification_of_wlpo (hw : WLPO) (hβ : 0 < β)
    (hJ : 0 < J) (h : ℝ) :
    magnetization_inf β J h = 0 ∨ magnetization_inf β J h ≠ 0 := by
  rcases wlpo_real_of_wlpo hw h with rfl | hne
  · left; exact (magnetization_inf_eq_zero_iff hβ hJ h).mpr rfl
  · right; exact fun heq => hne ((magnetization_inf_eq_zero_iff hβ hJ h).mp heq)
```

**Design decision for the coding agent:** Axiomatize `wlpo_real_of_wlpo`
rather than proving it from scratch. The equivalence between WLPO for
sequences and WLPO for reals depends on the representation of real
numbers, which varies across constructive frameworks. Axiomatizing with
citation is the same pattern used for `bmc_of_lpo` in Paper 8. The novel
content of this paper is the backward direction.

### 4.4 Backward direction: phase classification → WLPO

**Theorem.** If for every β > 0, J > 0, h ∈ ℝ one can decide
"m(∞, β, J, h) = 0 or m(∞, β, J, h) ≠ 0", then WLPO holds.

**Proof.**

Let α : ℕ → Bool be arbitrary. We must show:
(∀n, α(n) = false) ∨ ¬(∀n, α(n) = false).

**Step 1.** Construct h_α = Σ_n (if α(n) then 2^{-(n+1)} else 0).
As shown in §4.2, this converges (BISH) and h_α = 0 ⟺ ∀n, α(n) = false.

**Step 2.** Fix any β > 0, J > 0 (say β = J = 1). Compute
m(∞, 1, 1, h_α) = sinh(h_α) / √(sinh²(h_α) + exp(-4)).

**Step 3.** Apply the phase classification hypothesis: either
m(∞, 1, 1, h_α) = 0 or m(∞, 1, 1, h_α) ≠ 0.

**Step 4.** By §2.4 (magnetization_inf_eq_zero_iff):

  m(∞, 1, 1, h_α) = 0  ⟺  h_α = 0  ⟺  ∀n, α(n) = false

Therefore:
- If m(∞, 1, 1, h_α) = 0: conclude ∀n, α(n) = false. Take the
  left disjunct of WLPO.
- If m(∞, 1, 1, h_α) ≠ 0: conclude h_α ≠ 0, hence ¬(∀n, α(n) = false).
  Take the right disjunct of WLPO.

In either case, (∀n, α(n) = false) ∨ ¬(∀n, α(n) = false). ∎

**Lean proof:**
```lean
theorem wlpo_of_phase_classification
    (hpc : ∀ (β J h : ℝ), 0 < β → 0 < J →
      magnetization_inf β J h = 0 ∨ magnetization_inf β J h ≠ 0) :
    WLPO := by
  intro α
  -- Construct encoded field
  let h_α := encodedField α
  -- Apply phase classification at β = 1, J = 1
  rcases hpc 1 1 h_α one_pos one_pos with heq | hne
  · -- Case: m(∞) = 0, so h_α = 0, so ∀n, α(n) = false
    left
    exact (encodedField_eq_zero_iff α).mp
      ((magnetization_inf_eq_zero_iff one_pos one_pos h_α).mp heq)
  · -- Case: m(∞) ≠ 0, so h_α ≠ 0, so ¬(∀n, α(n) = false)
    right
    intro hall
    exact hne ((magnetization_inf_eq_zero_iff one_pos one_pos h_α).mpr
      ((encodedField_eq_zero_iff α).mpr hall))
```

### 4.5 The equivalence theorem

**Theorem (Main).** Over BISH, the following are equivalent:

1. WLPO
2. For all β > 0, J > 0, h ∈ ℝ: m(∞, β, J, h) = 0 ∨ m(∞, β, J, h) ≠ 0

**Proof.** (1) → (2) is §4.3. (2) → (1) is §4.4. ∎

```lean
theorem wlpo_iff_phase_classification :
    WLPO ↔ (∀ (β J h : ℝ), 0 < β → 0 < J →
      magnetization_inf β J h = 0 ∨ magnetization_inf β J h ≠ 0) :=
  ⟨fun hw β J h hβ hJ => phase_classification_of_wlpo hw hβ hJ h,
   fun hpc => wlpo_of_phase_classification hpc⟩
```

---

## 5. Part C: Stratification Theorem

### 5.1 Statement

**Theorem (Stratification).** The 1D Ising model with coupling J > 0
and external field h exhibits three distinct logical costs:

1. **Finite-volume computation** (any N, any β, J, h): BISH.
   Both f_N and m(N) are computable with explicit error bounds.

2. **Thermodynamic limit existence** (f_N → f_∞): LPO ↔ BMC.
   (Paper 8, cited.)

3. **Phase classification** (m(∞) = 0 or m(∞) ≠ 0): WLPO.
   (This paper.)

Moreover, these costs are strictly ordered: BISH ⊊ WLPO ⊊ LPO.
The separation WLPO ⊊ LPO is known (WLPO does not imply LPO over
BISH; LPO implies WLPO trivially since LPO gives the stronger
existential witness).

### 5.2 Interpretation

The stratification means:

- A constructive physicist working in BISH can compute finite-volume
  predictions to arbitrary accuracy.

- To assert that the limit *exists as a completed object*, they need
  LPO (equivalently, bounded monotone convergence).

- To *classify the phase* (paramagnetic vs. ferromagnetic), they need
  WLPO on top of knowing the limit exists.

The logical costs are cumulative and ordered. Each level of
physical assertion (computation → existence → classification) demands
a strictly stronger logical principle.

### 5.3 What this says about the programme

The CRM programme's calibration table now has three rows for one
model:

| Physical assertion (1D Ising)       | Constructive principle | Paper |
|--------------------------------------|------------------------|-------|
| Finite-volume observables            | BISH                   | 8 (A) |
| Thermodynamic limit (free energy)    | LPO ↔ BMC             | 8 (B) |
| Phase classification (magnetization) | WLPO                   | 20    |

The table for Paper 19 adds:

| Physical assertion (tunneling)       | Constructive principle | Paper |
|--------------------------------------|------------------------|-------|
| Specific barrier transmission coeff  | BISH                   | 19 (A)|
| General turning point existence      | LLPO ↔ IVT            | 19 (B)|
| Full semiclassical limit             | LPO                    | 19 (C)|

Together, Papers 8, 19, and 20 populate three levels of the
constructive hierarchy (LLPO, WLPO, LPO) with distinct physical
content. The programme has evolved from "one principle, many domains"
to "many principles, many domains."

---

## 6. Lean 4 Formalization Guide

### 6.1 Module structure

```
Paper20_WLPO_Magnetization/
├── Defs/
│   ├── WLPO.lean                  -- WLPO definition
│   ├── TransferMatrix_h.lean      -- T(β, J, h), extends Paper 8
│   ├── Eigenvalues_h.lean         -- λ±(β, J, h) with proofs
│   ├── Magnetization.lean         -- m(N, β, J, h) and m(∞, β, J, h)
│   └── EncodedField.lean          -- h_α construction and properties
├── PartA/
│   ├── FiniteComputable.lean      -- m(N) is BISH-computable
│   ├── SpinFlip.lean              -- Z₂ symmetry, m(N, β, J, 0) = 0
│   └── PartA_Main.lean            -- Part A main theorem
├── PartB/
│   ├── MagZeroIff.lean            -- m(∞, β, J, h) = 0 ↔ h = 0
│   ├── Forward.lean               -- WLPO → phase classification
│   ├── Backward.lean              -- phase classification → WLPO
│   └── PartB_Main.lean            -- WLPO ↔ phase classification
└── Main/
    ├── Stratification.lean        -- Combined statement with Paper 8
    └── AxiomAudit.lean            -- #print axioms for all theorems
```

**Estimated lines:** ~650–800 total.

### 6.2 Mathlib dependencies

**From Paper 8 (import or axiomatize):**
- `Real.exp`, `Real.log`, `Real.cosh`, `Real.sinh` — Mathlib
- Transfer matrix basics, eigenvalue positivity (if shared project)
- LPO, BMC definitions

**New dependencies:**
- `Real.sqrt` — `Mathlib.Analysis.SpecialFunctions.Pow.Real` or
  `Mathlib.Analysis.SpecialFunctions.Sqrt`
- `tsum` — `Mathlib.Topology.Algebra.InfiniteSum.Basic` for the
  encoded field series
- `Summable` — for convergence of the geometric series
- `Finset.sum_bij` or `Finset.sum_involution` — for the spin-flip
  cancellation in Part A
- `Bool.not_not` — for spin-flip involution

**Explicitly NOT imported:**
- `Mathlib.LinearAlgebra.Eigenspace.*` — eigenvalues are computed
  directly from the 2×2 characteristic equation
- `Mathlib.Analysis.NormedSpace.*` — no Banach space theory
- `Mathlib.MeasureTheory.*` — no measure theory

### 6.3 Key formalization challenges

**Challenge 1: The eigenvalue formulas for h ≠ 0.**

Paper 8 used the symmetric case where eigenvalues are 2·cosh(βJ)
and 2·sinh(βJ). With h ≠ 0, the transfer matrix is asymmetric
and the eigenvalues involve a square root of a discriminant. The
main challenge is proving Δ > 0 (discriminant positivity) and
λ₋ > 0. Both follow from elementary inequalities on exp, but
Lean proofs of such inequalities can be verbose.

**Recommended approach:** Prove Δ = exp(2βJ)·sinh²(βh) + exp(-2βJ)
and observe both terms are non-negative with the second strictly
positive. Then λ₋ > 0 follows from the calculation in §1.3.

**Challenge 2: The magnetization zero-iff.**

The theorem `magnetization_inf_eq_zero_iff` requires showing that
sinh(βh) / √(sinh²(βh) + exp(-4βJ)) = 0 ↔ βh = 0 ↔ h = 0
(given β > 0). The forward direction uses: quotient = 0 implies
numerator = 0 (denominator is positive), sinh(x) = 0 iff x = 0.
The backward direction substitutes h = 0. Both are elementary but
require careful handling of the division-by-positive and the sinh
injectivity.

**Lean approach:** Use `div_eq_zero_iff` and `Real.sinh_eq_zero_iff`
(check if this exists in Mathlib; if not, prove from
sinh(x) = (exp(x) - exp(-x))/2 = 0 iff exp(x) = exp(-x) iff
exp(2x) = 1 iff x = 0).

**Challenge 3: The encoded field series.**

The series h_α = Σ (if α(n) then 2^{-(n+1)} else 0) requires
`tsum` and `Summable`. Summability follows from comparison with
the geometric series Σ 2^{-(n+1)} = 1. The zero-iff property
requires: tsum of non-negative terms = 0 iff each term = 0.
This should be available in Mathlib as `tsum_eq_zero_iff` or
similar (for non-negative summable functions).

**Challenge 4: The spin-flip cancellation (Part A).**

The proof that m(N, β, J, 0) = 0 uses the involution σ ↦ spinFlip σ
on the configuration space. In Lean, this requires showing:

1. `spinFlip` is an involution (self-inverse)
2. `spinFlip` preserves the Boltzmann weight at h = 0
3. `spinFlip` negates the total magnetization
4. Therefore the weighted sum of magnetization over all configs is 0

The cleanest Lean approach uses `Finset.sum_involution`:
```lean
-- Finset.sum_involution says: if g is an involution on s with
-- f(g x) = -f(x), then Σ_{x ∈ s} f(x) = 0
```

Check if this lemma exists. If not, prove it by pairing.

### 6.4 Axiom audit specification

The coding agent MUST verify the following after compilation:

```lean
-- Part A: no omniscience
#print axioms Papers.P20.partA_main
-- Expected: [propext, Classical.choice, Quot.sound]
-- MUST NOT contain: WLPO, LPO, LLPO, wlpo_real_of_wlpo

-- Part B forward: uses WLPO axiom
#print axioms Papers.P20.phase_classification_of_wlpo
-- Expected: [propext, Classical.choice, Quot.sound, wlpo_real_of_wlpo]

-- Part B backward: no axioms beyond BISH
#print axioms Papers.P20.wlpo_of_phase_classification
-- Expected: [propext, Classical.choice, Quot.sound]
-- The phase classification hypothesis appears as a hypothesis,
-- not an axiom.

-- Part B main equivalence:
#print axioms Papers.P20.wlpo_iff_phase_classification
-- Expected: [propext, Classical.choice, Quot.sound, wlpo_real_of_wlpo]
-- wlpo_real_of_wlpo is a cited axiom (Bridges–Richman 1987)
```

---

## 7. Potential Weaknesses and Mitigations

### 7.1 "The encoding is trivial"

Yes. h_α = Σ α(n)·2^{-(n+1)} is a standard binary encoding, and
the zero-iff property is immediate. The novelty is not in the
encoding technique but in:

(a) The identification that the 1D Ising magnetization's zero-locus
is exactly {h = 0}, making it a perfect vehicle for WLPO.

(b) The stratification result: same model, different observable,
different principle. This structural observation — that logical cost
is observable-dependent — is new to the CRM programme.

(c) The Lean verification, which mechanically confirms the axiom
separation.

### 7.2 "WLPO for reals is axiomatized, not proved"

Same pattern as bmc_of_lpo in Paper 8. The equivalence between
WLPO for sequences and WLPO for reals depends on the representation
of reals (Cauchy sequences, Dedekind cuts, etc.) and is a known
result in the constructive analysis literature. Proving it from
scratch in Lean would require formalizing the constructive real
number representation, which is a large infrastructure project
orthogonal to this paper's contribution. Axiomatizing with citation
is the established practice in the programme.

### 7.3 "The 1D Ising model has no phase transition"

This is a feature, not a bug. The absence of spontaneous symmetry
breaking in 1D means the magnetization zero-test is a pure field
zero-test, undistorted by phase transition effects. The WLPO content
is cleaner in 1D than it would be in 2D, where the order parameter's
behavior depends on temperature in a way that entangles WLPO with
LPO.

The paper should be explicit about this: "We deliberately use the
1D model, which lacks a phase transition, to isolate the WLPO
content of the phase classification from the LPO content of the
thermodynamic limit."

### 7.4 Convergence of h_α: does it require LPO?

No. See the note in §4.2. The partial sums of h_α have a uniform
Cauchy modulus (geometric bound) independent of α. This is the
explicit-rate case where convergence is BISH. The coding agent
should verify this by checking that `encodedField_converges` does
not print LPO or BMC in its axiom audit.

---

## 8. Non-Lean Content (for the LaTeX paper)

### 8.1 Introduction framing

The paper should open with the observation that Papers 8–18
established the BMC ↔ LPO boundary across five physics domains.
Paper 19 opened the LLPO wing. This paper opens the WLPO wing
by demonstrating that a different question about the same physical
system (1D Ising) requires a different constructive principle.

The key conceptual point: **logical cost is not a property of a
physical system but of a physical assertion about the system.**
The 1D Ising model is one system. "Does the free energy have a
limit?" costs LPO. "Is the magnetization zero?" costs WLPO. Same
Hamiltonian, different questions, different prices.

### 8.2 Discussion points

1. **Observable-dependent logical cost.** This is the main
   conceptual contribution. Prior CRM work assigned logical costs
   to systems. This paper shows the cost depends on the observable.

2. **WLPO as a weaker-than-LPO test.** WLPO decides equality
   (x = 0?) but not inequality with witness (∃n, α(n) = 1). The
   magnetization phase classification requires only the weaker
   test. This is consistent with the constructive hierarchy:
   BISH ⊊ WLPO ⊊ LPO.

3. **Connection to Paper 7.** Paper 7 proved WLPO ↔ S₁(H) bidual
   gap. This paper proves WLPO ↔ Ising phase classification.
   Both are zero-tests on infinite objects (a functional vs. a
   limit), confirming that WLPO naturally calibrates "is this
   infinite-dimensional quantity exactly zero?"

4. **Updated calibration table.** Include the full table showing
   BISH, WLPO, LLPO, LPO levels populated with physical content.

### 8.3 References

- Bridges, D., Richman, F. (1987). *Varieties of Constructive
  Mathematics*. Cambridge University Press. [WLPO definition and
  basic properties]
- Bridges, D., Vîță, L. (2006). *Techniques of Constructive
  Analysis*. Springer. [BMC ↔ LPO, cited for forward direction]
- Lee, P.C.K. (2026). Paper 7: WLPO and the bidual gap of S₁(H).
  Zenodo. [Prior WLPO calibration]
- Lee, P.C.K. (2026). Paper 8: LPO equivalence of the 1D Ising
  thermodynamic limit. Zenodo. [Infrastructure, LPO result]
- Lee, P.C.K. (2026). Paper 19: LLPO and WKB turning points. Zenodo.
  [LLPO calibration, parallel result]
- Ishihara, H. (2006). "Constructive reverse mathematics: compactness
  properties." In: *From Sets and Types to Topology and Analysis*.
  Oxford. [CRM methodology]
- Baxter, R. (1982). *Exactly Solved Models in Statistical Mechanics*.
  Academic Press. [1D Ising exact solution with external field]

---

## 9. Summary for the Coding Agent

**What to build:** A Lean 4 project with ~650–800 lines across 12
modules proving that the 1D Ising magnetization phase classification
is equivalent to WLPO over BISH.

**The hard parts:**
1. Eigenvalue formulas for the asymmetric transfer matrix (§1.3)
2. The magnetization zero-iff theorem (§2.4, Challenge 2)
3. The spin-flip cancellation for Part A (§3.3, Challenge 4)
4. The encoded field series convergence and zero-iff (§4.2, Challenge 3)

**The easy parts:**
1. WLPO definition (one line)
2. The backward direction proof (§4.4 — five lines of logic)
3. The equivalence statement (§4.5 — one iff)

**Axiom budget:**
- Part A: zero omniscience axioms
- Part B forward: one cited axiom (wlpo_real_of_wlpo)
- Part B backward: zero omniscience axioms
- Combined: one cited axiom total

**Success criterion:** `#print axioms` on all main theorems matches
the specification in §6.4. Zero `sorry`. Compiles clean.
