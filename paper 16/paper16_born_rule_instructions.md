# Paper 16: The Born Rule as a Logical Artefact
## Coding Agent Instructions — Lean 4 Formalization

**Author:** P.C.K. Lee
**Series:** Constructive Reverse Mathematics of Mathematical Physics, Paper 16
**Date:** February 2026

---

## 1. WHAT THIS PAPER PROVES

The Born rule — the foundational postulate of quantum mechanics asserting that measurement probabilities equal |⟨λ|ψ⟩|² — is an idealization. This paper calibrates its constructive cost by splitting it into two layers:

| Layer | Physical content | Logical cost |
|-------|-----------------|--------------|
| **Single-trial probability** | P(λ) = ‖P_λ ψ‖² is a computable real number | **BISH** |
| **Weak law (Chebyshev bound)** | Pr(|freq - P| > ε) ≤ σ²/(Nε²) for finite N | **BISH** |
| **Strong law (frequentist convergence)** | freq_N → P almost surely as N → ∞ | **DC_ω** |

The punchline: if you are satisfied with finite error bounds on measurement statistics (what every experimentalist actually uses), quantum probability is fully constructive. The assertion that frequencies *converge exactly* to the Born probabilities — the frequentist interpretation that undergirds the textbook formulation — requires Dependent Choice. The Born rule as practiced is BISH. The Born rule as formalized is DC.

This parallels the other quantum calibrations in the programme:
- Paper 4: approximate spectral membership is BISH, exact spectral membership costs MP
- Paper 6: preparation uncertainty is BISH, measurement uncertainty costs DC
- Paper 14: finite-time decoherence bounds are BISH, exact decoherence (completed limit) costs LPO
- **Paper 16 (this):** finite-sample frequency bounds are BISH, exact frequentist convergence costs DC

---

## 2. STRATEGIC CONTEXT

Paper 16 completes the quantum mechanics column of the calibration table. Papers 4, 6, 11, and 14 have already calibrated the spectrum, the uncertainty principle, entanglement, and the measurement problem. The Born rule is the last major unexamined piece.

The result is not surprising in isolation — constructive analysts know the strong law needs DC. The value is:
1. **Machine verification** that the split is exactly at DC (not LPO, not WLPO)
2. **Physical interpretation**: the Born rule itself is an idealization, with a measurable logical cost
3. **Table completion**: DC now appears in the quantum column alongside BISH, MP, and LPO
4. **Companion to Paper 14**: Paper 14 calibrates the *measurement problem* (decoherence → LPO), Paper 16 calibrates the *probability problem* (Born rule → DC). Together they show that different quantum idealizations land at different levels of the constructive hierarchy.

---

## 3. MATHEMATICAL PROOF — DETAILED

### 3.1 Setup: Finite-Dimensional Quantum Measurement

Work in finite dimensions throughout. Fix:
- H = ℂ^d (finite-dimensional Hilbert space, d ≥ 2)
- ψ ∈ H with ‖ψ‖ = 1 (normalized state vector)
- A : H → H a Hermitian operator (observable)
- A has eigenvalues λ₁, ..., λ_d with orthonormal eigenvectors |λ₁⟩, ..., |λ_d⟩
- Spectral decomposition: A = Σᵢ λᵢ P_λᵢ where P_λᵢ = |λᵢ⟩⟨λᵢ| are orthogonal projections

The Born rule postulates: the probability of measuring outcome λᵢ is

    p_i = ‖P_λᵢ ψ‖² = |⟨λᵢ|ψ⟩|²

### 3.2 Theorem 1: Single-Trial Born Probability is BISH

**Statement.** For a finite-dimensional Hilbert space H = ℂ^d, a normalized state ψ, and a Hermitian operator A with spectral decomposition A = Σᵢ λᵢ P_λᵢ, each Born probability p_i = ‖P_λᵢ ψ‖² is a computable real number in [0,1], and Σᵢ p_i = 1. The entire probability distribution (p₁, ..., p_d) is constructively computable.

**Proof.**

Step 1: P_λᵢ is a finite-dimensional orthogonal projection (a d×d matrix with rational or algebraic entries, given algebraic input). Applying P_λᵢ to ψ is matrix-vector multiplication — finitely many additions and multiplications of complex numbers.

Step 2: ‖P_λᵢ ψ‖² = ⟨P_λᵢ ψ, P_λᵢ ψ⟩ = ⟨ψ, P_λᵢ² ψ⟩ = ⟨ψ, P_λᵢ ψ⟩ (since P_λᵢ is a projection, P² = P and P* = P). This is a finite sum of products of complex numbers. Computable.

Step 3: Σᵢ ‖P_λᵢ ψ‖² = ⟨ψ, (Σᵢ P_λᵢ) ψ⟩ = ⟨ψ, I ψ⟩ = ⟨ψ, ψ⟩ = ‖ψ‖² = 1 by completeness of the eigenbasis.

Step 4: Each p_i ≥ 0 (it's a squared norm) and Σ p_i = 1. So (p₁,...,p_d) is a valid probability distribution over a finite set.

**No limits. No infinite sequences. No choice principles.** Every operation is finite-dimensional linear algebra. This is BISH. ∎

**Lean target:**
```lean
/-- Born probability for eigenvalue λᵢ is computable and in [0,1] -/
theorem born_probability_computable
    (d : ℕ) (hd : d ≥ 1)
    (ψ : EuclideanSpace ℂ (Fin d))
    (hψ : ‖ψ‖ = 1)
    (P : Fin d → Matrix (Fin d) (Fin d) ℂ)
    (hP_proj : ∀ i, (P i) ^ 2 = P i)
    (hP_herm : ∀ i, (P i).IsHermitian)
    (hP_orth : ∀ i j, i ≠ j → P i * P j = 0)
    (hP_complete : ∑ i, P i = 1) :
    (∀ i, 0 ≤ inner (ψ) ((P i).mulVec ψ)) ∧
    (∑ i, inner (ψ) ((P i).mulVec ψ) = 1) := by
  sorry
```

### 3.3 Theorem 2: Expectation Value is BISH

**Statement.** The expected value ⟨A⟩_ψ = ⟨ψ, Aψ⟩ = Σᵢ λᵢ pᵢ is a computable real number.

**Proof.** ⟨ψ, Aψ⟩ is a single inner product — one matrix-vector multiplication followed by one dot product. Both are finite sums of products. BISH. ∎

**Lean target:**
```lean
/-- Quantum expectation value is computable -/
theorem expectation_value_computable
    (d : ℕ) (ψ : EuclideanSpace ℂ (Fin d))
    (hψ : ‖ψ‖ = 1)
    (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) :
    ∃ (v : ℝ), (inner ψ (A.mulVec ψ) : ℂ) = ↑v := by
  sorry
```

### 3.4 Theorem 3: Variance is BISH

**Statement.** The variance Var_ψ(A) = ⟨ψ, A²ψ⟩ - ⟨ψ, Aψ⟩² is a computable non-negative real number.

**Proof.** A² is a d×d matrix (computable by matrix multiplication). Both inner products are computable (Theorem 2 applied to A and A²). The difference of two computable reals is computable. Non-negativity: Var(A) = ‖(A - ⟨A⟩I)ψ‖² ≥ 0. BISH. ∎

**Lean target:**
```lean
/-- Quantum variance is computable and non-negative -/
theorem variance_nonneg_computable
    (d : ℕ) (ψ : EuclideanSpace ℂ (Fin d))
    (hψ : ‖ψ‖ = 1)
    (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) :
    0 ≤ (inner ψ ((A * A).mulVec ψ) - inner ψ (A.mulVec ψ) ^ 2).re := by
  sorry
```

### 3.5 Theorem 4: Relative Frequency After N Measurements (BISH)

**Statement.** Given N measurement outcomes x₁, ..., x_N ∈ {λ₁, ..., λ_d}, the relative frequency of outcome λᵢ is

    freq_N(λᵢ) = (#{j : x_j = λᵢ}) / N

This is a rational number in [0,1] and is computable from the finite data.

**Proof.** Counting elements in a finite set satisfying a decidable predicate is a finite loop. Division by N is rational arithmetic. BISH. ∎

**Lean target:**
```lean
/-- Relative frequency of measurement outcome is computable rational -/
theorem relative_frequency_computable
    (d N : ℕ) (hN : N ≥ 1)
    (outcomes : Fin N → Fin d) (i : Fin d) :
    ∃ (q : ℚ), 0 ≤ q ∧ q ≤ 1 ∧
      q = (Finset.univ.filter (fun j => outcomes j = i)).card / N := by
  sorry
```

### 3.6 Theorem 5: Weak Law of Large Numbers — Chebyshev Bound (BISH)

This is the critical BISH result. It says that for any finite number of independent measurements, the frequency is *probably close* to the Born probability, with an explicit computable bound.

**Statement.** Let X₁, ..., X_N be independent random variables, each taking value 1 with probability p and 0 with probability 1-p (Bernoulli trials corresponding to "did we get outcome λᵢ?"). Let S_N = (X₁ + ... + X_N)/N be the sample mean (= relative frequency). Then for any ε > 0:

    Pr(|S_N - p| ≥ ε) ≤ p(1-p)/(Nε²) ≤ 1/(4Nε²)

**Proof (constructive — all BISH).**

Step 1: E[X_j] = p and Var(X_j) = p(1-p) for each Bernoulli trial. These are finite arithmetic computations. BISH.

Step 2: By independence, Var(S_N) = Var(X₁ + ... + X_N)/N² = N·p(1-p)/N² = p(1-p)/N. This uses only that variance of a sum of independent variables equals the sum of variances — which for finitely many variables is a finite sum. BISH.

Step 3: Chebyshev's inequality: for any random variable Y with finite variance,

    Pr(|Y - E[Y]| ≥ ε) ≤ Var(Y)/ε²

Apply to Y = S_N: Pr(|S_N - p| ≥ ε) ≤ p(1-p)/(Nε²).

Step 4: p(1-p) ≤ 1/4 for p ∈ [0,1] (AM-GM or calculus-free: (1/2 - p)² ≥ 0 implies p - p² ≤ 1/4). Hence the bound ≤ 1/(4Nε²).

**Key point:** Chebyshev's inequality is BISH. The proof is:

    E[|Y-μ|²] = ∫ |y-μ|² dP(y) ≥ ∫_{|y-μ|≥ε} |y-μ|² dP(y) ≥ ε² · Pr(|Y-μ| ≥ ε)

For a discrete random variable on a finite set (our case), the "integral" is a finite sum. No limits, no measure theory on infinite spaces, no choice. BISH.

**What this gives the physicist:** After N = 10,000 measurements, the probability that the observed frequency deviates from the Born probability by more than 0.01 is at most 1/(4 × 10000 × 0.0001) = 0.25. After N = 1,000,000 measurements, the same deviation probability is at most 0.0025. The bound is explicit, computable, and shrinks as 1/N. No physicist needs more than this.

**Lean target:**
```lean
/-- Chebyshev bound for Bernoulli sample mean (weak law) -/
theorem chebyshev_bernoulli_bound
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (N : ℕ) (hN : N ≥ 1)
    (ε : ℝ) (hε : 0 < ε) :
    -- The probability of |freq - p| ≥ ε is bounded by p(1-p)/(Nε²)
    -- Formalized as: the Chebyshev bound for the sample mean
    p * (1 - p) / (↑N * ε ^ 2) ≤ 1 / (4 * ↑N * ε ^ 2) := by
  sorry

/-- Variance of Bernoulli is bounded by 1/4 -/
theorem bernoulli_variance_bound
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    p * (1 - p) ≤ 1 / 4 := by
  sorry
```

### 3.7 Theorem 6: Strong Law of Large Numbers Requires DC_ω

This is the calibration theorem. It shows that exact frequentist convergence — the statement that relative frequencies converge almost surely to the Born probability — is *not* BISH. It requires Dependent Choice.

**Statement (informal).** The assertion

    "For almost every infinite sequence of independent Born-rule measurements, freq_N(λᵢ) → p_i as N → ∞"

is equivalent to (or at minimum requires) the axiom of Dependent Choice over ℕ (DC_ω).

**Proof structure.**

**Part A: DC_ω → Strong Law.** (The standard direction.)

The classical proof of the strong law for bounded i.i.d. random variables proceeds by:

1. **Construct the product probability space** (Ω, F, P) = (Ω₁ × Ω₂ × ..., ⊗ F_i, ⊗ P_i) where each factor is the single-measurement space {λ₁, ..., λ_d} with Born probabilities. Constructing this countable product requires DC_ω: at each stage n, you extend the finite product to stage n+1 by choosing a consistent extension. This is a dependent sequence of choices indexed by ℕ.

2. **Fourth moment method / Borel-Cantelli.** The proof that freq_N → p almost surely uses the Borel-Cantelli lemma applied to the events E_k = {|S_k - p| > ε}. Borel-Cantelli says: if Σ P(E_k) < ∞ then P(E_k infinitely often) = 0. The "infinitely often" event is lim sup E_k = ∩_n ∪_{k≥n} E_k — a countable intersection of countable unions. Manipulating this requires DC_ω to select witnesses at each stage.

3. **Almost sure convergence.** The conclusion "freq_N → p for P-almost every ω" is a statement about the behavior of infinite sequences. Extracting a convergent subsequence or proving the Cauchy criterion for a specific ω requires dependent choices along the sequence.

**Part B: Strong Law → DC_ω.** (The reverse mathematics direction — the novel content.)

This is the harder direction. The strategy:

**Claim.** If the strong law of large numbers holds for all Bernoulli processes with computable parameter p ∈ (0,1), then DC_ω holds.

**Proof sketch.**

Given a dependent choice problem: a set A ⊂ ℕ × ℕ with ∀n, ∃m, (n,m) ∈ A, we need to construct a sequence (a_n) with (a_n, a_{n+1}) ∈ A for all n.

Encode A into a quantum measurement scenario:
- Define a sequence of observables A_n, each determined by the available successors at stage n
- The Born probabilities for A_n encode the set {m : (n,m) ∈ A}
- If the strong law holds, the frequency of each outcome stabilizes, which means certain outcomes occur at least once in the infinite sequence
- The occurrence of outcome m in the measurement of A_n provides the witness for the choice at stage n
- The almost-sure convergence guarantees that all required witnesses eventually appear

**Important caveat for Lean implementation:** The full reverse direction (SLLN → DC_ω) is subtle and may require significant effort. The paper can take a two-tier approach:

- **Tier 1 (mandatory):** Prove that the standard proof of SLLN uses DC_ω (forward direction). This is done by exhibiting the DC_ω dependency in the product space construction and Borel-Cantelli argument. Audit `#print axioms` on a Lean proof of SLLN to exhibit the choice content.

- **Tier 2 (if feasible):** Prove the reverse direction, establishing an equivalence. If Tier 2 is not achieved, the paper states this as a conjecture with the proof sketch and notes that the forward direction already establishes DC_ω as a lower bound.

**Lean target (Tier 1 — axiom audit):**
```lean
/-- The strong law of large numbers for Bernoulli random variables.
    This proof INTENTIONALLY uses Dependent Choice.
    Run `#print axioms slln_bernoulli` to exhibit the DC content. -/
theorem slln_bernoulli
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    -- Dependent Choice as an explicit hypothesis
    (dc : DependentChoice)
    -- Product probability space constructed via DC
    (Ω : Type) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (X : ℕ → Ω → ℝ)
    (hX_iid : ∀ n, IsBernoulli (X n) p)
    (hX_indep : PairwiseIndependent X P) :
    -- freq_N → p almost surely
    ∀ᵐ ω ∂P, Filter.Tendsto
      (fun N => (∑ i in Finset.range N, X i ω) / N) Filter.atTop (nhds p) := by
  sorry
```

**Lean target (Tier 1 — DC_ω axiom statement):**
```lean
/-- Dependent Choice over ℕ: the axiom that the strong law requires -/
axiom DependentChoice : Prop
axiom DependentChoice.intro :
    (∀ (α : Type) (R : α → α → Prop) (a₀ : α),
      (∀ a, ∃ b, R a b) → ∃ f : ℕ → α, f 0 = a₀ ∧ ∀ n, R (f n) (f (n+1)))
    → DependentChoice

/-- Alternative: use a typeclass like HasWLPO from previous papers -/
class HasDC where
  dc : ∀ (α : Type) (R : α → α → Prop) (a₀ : α),
    (∀ a, ∃ b, R a b) → ∃ f : ℕ → α, f 0 = a₀ ∧ ∀ n, R (f n) (f (n+1))
```

### 3.8 Theorem 7: Separation — Weak Law Does NOT Require DC (BISH Certificate)

**Statement.** The Chebyshev bound (Theorem 5) is provable without DC_ω. Its `#print axioms` output contains no choice principles beyond `propext` and `Quot.sound` (or at most `Classical.choice` from Mathlib infrastructure, with a mathematical argument that the proof content is BISH — following the Paper 11 methodology).

**Proof.** By direct verification. The Lean proof of Theorem 5 uses only:
- Finite sums (Finset operations)
- Real arithmetic (field operations on ℝ)
- Basic order theory (≤ on ℝ)
- No dependent choice, no countable choice, no product measure construction

Run `#print axioms chebyshev_bernoulli_bound` and verify the axiom certificate. ∎

---

## 4. MODULE STRUCTURE

```
Papers/P16_BornRule/
├── Defs.lean              -- Core definitions
├── BornProbability.lean   -- Theorem 1: Born probability is BISH
├── Expectation.lean       -- Theorem 2: Expectation value is BISH
├── Variance.lean          -- Theorem 3: Variance is BISH
├── RelativeFreq.lean      -- Theorem 4: Relative frequency is BISH
├── WeakLaw.lean           -- Theorem 5: Chebyshev bound (BISH)
├── BernoulliVariance.lean -- Theorem 5 helper: p(1-p) ≤ 1/4
├── StrongLaw.lean         -- Theorem 6: SLLN requires DC_ω
├── Separation.lean        -- Theorem 7: Axiom audit / separation
├── DCAxiom.lean           -- DC_ω axiom definition (HasDC typeclass)
└── Main.lean              -- Assembly + #print axioms
```

### Module dependency graph:
```
Defs ← BornProbability ← Expectation ← Variance
Defs ← RelativeFreq ← WeakLaw ← BernoulliVariance
DCAxiom ← StrongLaw
WeakLaw + StrongLaw ← Separation
All ← Main
```

---

## 5. KEY DEFINITIONS (Defs.lean)

```lean
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.InnerProductSpace.Basic

/-- A spectral decomposition of a Hermitian matrix on ℂ^d -/
structure SpectralDecomp (d : ℕ) where
  eigenvalues : Fin d → ℝ
  projections : Fin d → Matrix (Fin d) (Fin d) ℂ
  is_projection : ∀ i, (projections i) ^ 2 = projections i
  is_hermitian : ∀ i, (projections i).IsHermitian
  is_orthogonal : ∀ i j, i ≠ j → projections i * projections j = 0
  is_complete : ∑ i, projections i = 1
  spectral_eq : ∀ (A : Matrix (Fin d) (Fin d) ℂ),
    A = ∑ i, (eigenvalues i : ℂ) • projections i

/-- Born probability distribution from a state and spectral decomposition -/
def bornDistribution (d : ℕ) (ψ : EuclideanSpace ℂ (Fin d))
    (spec : SpectralDecomp d) : Fin d → ℝ :=
  fun i => ‖(spec.projections i).mulVec ψ‖ ^ 2

/-- Relative frequency of outcome i in a sequence of N measurements -/
def relativeFreq (d N : ℕ) (outcomes : Fin N → Fin d) (i : Fin d) : ℚ :=
  (Finset.univ.filter (fun j => outcomes j = i)).card / N
```

---

## 6. AXIOM CERTIFICATE TARGETS

The paper's calibration claim rests on these `#print axioms` outputs:

| Theorem | Expected axioms | Constructive status |
|---------|----------------|-------------------|
| `born_probability_computable` | propext, Quot.sound | BISH |
| `expectation_value_computable` | propext, Quot.sound | BISH |
| `variance_nonneg_computable` | propext, Quot.sound | BISH |
| `relative_frequency_computable` | propext, Quot.sound | BISH |
| `chebyshev_bernoulli_bound` | propext, Quot.sound | BISH |
| `bernoulli_variance_bound` | propext, Quot.sound | BISH |
| `slln_bernoulli` | propext, Quot.sound, **Classical.choice** + **HasDC** | DC_ω |

If Mathlib's infrastructure forces `Classical.choice` into the BISH theorems (as happened in Paper 11), the paper follows Paper 11's methodology: mathematical argument that the proof content is constructive, with the `Classical.choice` being architectural (from inner product space instances), not mathematical.

---

## 7. IMPLEMENTATION NOTES

### 7.1 Mathlib-Free vs. Mathlib

**Preferred approach: Mathlib-free for Theorems 1-5, 7.** The BISH theorems are finite-dimensional linear algebra. Writing them without Mathlib avoids the `Classical.choice` contamination problem entirely. Use:
- `Matrix (Fin d) (Fin d) ℂ` (can define without Mathlib)
- `EuclideanSpace ℂ (Fin d)` or just `Fin d → ℂ`
- Hand-rolled inner product and norm
- Finset for finite sums

**Mathlib for Theorem 6 only.** The SLLN proof can lean on `Mathlib.Probability` and `Mathlib.MeasureTheory`. The DC content is *expected* here — it's what we're calibrating. The axiom audit just needs to show that `Classical.choice` (carrying the DC content) appears in Theorem 6 but not in Theorems 1-5.

### 7.2 The HasDC Typeclass

Following the HasWLPO pattern from Papers 2-4:

```lean
/-- Dependent Choice over ℕ -/
class HasDC where
  dependent_choice : ∀ {α : Type} (R : α → α → Prop) (a₀ : α),
    (∀ a, ∃ b, R a b) → ∃ f : ℕ → α, f 0 = a₀ ∧ ∀ n, R (f n) (f (n + 1))

/-- In classical logic, DC holds -/
noncomputable instance : HasDC where
  dependent_choice := by
    intro α R a₀ h
    -- Classical proof using Classical.choice at each step
    sorry
```

### 7.3 Product Measure Construction

The key DC dependency in the SLLN proof is the construction of the infinite product probability space. In `Mathlib.MeasureTheory.Measure.ProdMeasure`, the countable product `⨂ᵢ μᵢ` is built using Ionescu-Tulcea / Kolmogorov extension, which requires countable choice (a consequence of DC_ω). The coding agent should:

1. Build the finite product (BISH — this is just tensor product of finite distributions)
2. State that extending to the countable product requires DC_ω
3. Show that the SLLN conclusion (almost sure convergence) depends on this extension

### 7.4 Avoiding Mathlib.Probability Entirely (Alternative)

If Mathlib's probability library proves too heavy, the coding agent can take a self-contained approach:

1. Define Bernoulli random variable as a function `Fin 2 → ℝ` with values 0 and 1
2. Define "probability" as a finitely-additive function on `Finset (Fin 2)`
3. Prove Chebyshev directly from the definitions (no measure theory)
4. For the SLLN, state it as an axiom with `HasDC` hypothesis and prove it uses DC by construction

This avoids all Mathlib dependencies and gives the cleanest axiom certificates.

---

## 8. WHAT SUCCESS LOOKS LIKE

### Minimum viable paper (Tier 1):
- Theorems 1-5 compile with zero sorry, zero errors
- Theorem 5 (Chebyshev bound) has clean axiom certificate (no choice)
- Theorem 6 stated with `HasDC` hypothesis
- `#print axioms` shows DC dependency in Theorem 6
- Theorem 7 verifies the separation: weak law ≠ strong law in logical cost
- Total: ~400-600 lines across 10 modules

### Full paper (Tier 1 + Tier 2):
- Everything in Tier 1 plus:
- Reverse direction: SLLN → DC_ω formalized (or at least a significant fragment)
- This would be a genuine reverse mathematics result, not just an axiom audit

---

## 9. WHAT NOT TO DO

1. **Do not try to prove the full SLLN from scratch in Lean.** The standard proof is complex and already exists in Mathlib (in classical form). The paper's contribution is the *calibration* — showing where DC enters — not reproving the SLLN.

2. **Do not import Mathlib for the BISH theorems.** Keep Theorems 1-5 Mathlib-free for clean axiom certificates. If Mathlib is needed for convenience lemmas, isolate them and document the axiom contamination.

3. **Do not attempt infinite-dimensional formalization.** Everything is finite-dimensional. H = ℂ^d. Observables are d×d matrices. Probability distributions are over Fin d. The finite-dimensional restriction is the whole point — it shows the physics is BISH.

4. **Do not conflate DC_ω with full AC.** Dependent Choice is strictly weaker than the Axiom of Choice. The paper's precision comes from identifying *exactly* DC_ω, not AC or countable choice. Be careful with the logical hierarchy.

---

## 10. PHYSICAL INTERPRETATION (for the LaTeX paper, not the Lean code)

The paper should make the following argument in the introduction and discussion:

The Born rule is the foundational postulate of quantum mechanics. Every prediction flows from it. It asserts: the probability of measuring eigenvalue λ for observable A in state ψ is |⟨λ|ψ⟩|².

But "probability" is ambiguous. If it means: "the squared norm of the projected state" — that's a single computation, BISH, done. If it means: "the long-run relative frequency in repeated identical measurements" — that's an assertion about infinite sequences, and it costs DC_ω.

This is not a pedantic distinction. It separates two physical contents:
- **Quantum geometry** (BISH): the state ψ determines a distribution over outcomes. This is a fact about one vector in one Hilbert space. No measurements needed.
- **Quantum statistics** (DC_ω): repeated measurements of identically prepared systems yield frequencies that converge to the geometric distribution. This requires constructing infinite product spaces and proving convergence.

The experimentalist who runs 10,000 measurements and checks that frequencies match Born probabilities within error bars is working in BISH. The textbook that asserts "in the limit of infinitely many measurements, the frequency equals the probability" is asserting DC_ω.

This parallels every other calibration in the programme:
- The individual eigenvalue is BISH; the complete spectrum costs MP (Paper 4)
- Preparation uncertainty is BISH; measurement statistics cost DC (Paper 6)
- Finite-time decoherence bounds are BISH; exact decoherence costs LPO (Paper 14)
- The thermodynamic limit of finite-volume bounds is BISH; the completed limit costs LPO (Papers 8-9)

The pattern is uniform: physics as practiced is constructive. Physics as formalized — with its idealized infinite limits — has measurable logical costs. The Born rule is just the latest, and perhaps the most fundamental, confirmation.
