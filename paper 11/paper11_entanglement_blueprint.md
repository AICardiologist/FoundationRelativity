# Lean 4 Formalization Blueprint: Constructive Cost of Quantum Entanglement

## Paper 11 — CHSH Bound and Finite-Dimensional Entanglement Entropy

### Paul C.-K. Lee
### February 2026

---

## 0. Purpose and Context

**What this paper does.** We calibrate the logical cost of two foundational
results about quantum entanglement:

  (A) The Tsirelson bound: ⟨CHSH⟩ ≤ 2√2 for the CHSH operator on ℂ² ⊗ ℂ².
  (B) Finite-dimensional entanglement entropy: the von Neumann entropy
      S(ρ_A) = −Tr(ρ_A log ρ_A) of a partial trace of a bipartite state.

**Expected result.** Both are BISH — no omniscience or choice principles
required. This is the predicted outcome under the working hypothesis of
Paper 10: relational/compositional structure of finite quantum systems is
constructively accessible.

**Why this matters.** The calibration table in Paper 10 covers states,
limits, spectra, and uncertainty. It does not cover compositional structure
— tensor products, entanglement, correlations. Bell nonlocality is the
most distinctively quantum phenomenon. If it's BISH, the working hypothesis
survives its most natural stress test: the logical costs in Papers 2–9
come entirely from infinite-dimensional idealization, not from the
relational structure of quantum mechanics itself.

**Methodology.** CRM over Mathlib, same as Papers 6 (v2), 7, 8, 9.
All mathematical content derived from Mathlib APIs. The #print axioms
certificate verifies no classical axioms beyond those explicitly declared.

**Dependencies.** This formalization is self-contained — it does NOT
depend on any previous paper's codebase. It uses only Mathlib.

---

## 1. Mathematical Background

### 1.1 The CHSH operator

Let H = ℂ² ⊗ ℂ². The CHSH scenario involves:
- Two observables for Alice: A, A' — self-adjoint operators on ℂ² with
  eigenvalues ±1 (i.e., A² = I, (A')² = I).
- Two observables for Bob: B, B' — self-adjoint operators on ℂ² with
  eigenvalues ±1 (i.e., B² = I, (B')² = I).

The CHSH operator on H = ℂ² ⊗ ℂ² is:

  C = A ⊗ B + A ⊗ B' + A' ⊗ B − A' ⊗ B'

The Tsirelson bound states:

  ‖C‖ ≤ 2√2

where ‖·‖ is the operator norm. Equivalently, for any unit vector
ψ ∈ ℂ² ⊗ ℂ²:

  |⟨ψ, Cψ⟩| ≤ 2√2

### 1.2 The proof of the Tsirelson bound

The standard proof uses an algebraic identity. Define:

  C² = (A ⊗ B + A ⊗ B' + A' ⊗ B − A' ⊗ B')²

Expand using:
- A² = I, (A')² = I, B² = I, (B')² = I  (involutory)
- [A, A'] may be nonzero (Alice's observables don't necessarily commute)
- [B, B'] may be nonzero (Bob's observables don't necessarily commute)
- BUT operators on different subsystems commute through the tensor product:
  (A ⊗ I)(I ⊗ B) = A ⊗ B = (I ⊗ B)(A ⊗ I)

Expanding C²:

  C² = 4·I ⊗ I + [A, A'] ⊗ [B, B']

Proof of this identity:
  C² = (A⊗B)² + (A⊗B')(A⊗B) + (A'⊗B)(A⊗B) − (A'⊗B')(A⊗B)
     + (A⊗B)(A⊗B') + (A⊗B')² + (A'⊗B)(A⊗B') − (A'⊗B')(A⊗B')
     + (A⊗B)(A'⊗B) + (A⊗B')(A'⊗B) + (A'⊗B)² − (A'⊗B')(A'⊗B)
     − (A⊗B)(A'⊗B') − (A⊗B')(A'⊗B') − (A'⊗B)(A'⊗B') + (A'⊗B')²

Using (X⊗Y)(Z⊗W) = XZ ⊗ YW and A² = I etc.:

Diagonal terms: (A⊗B)² = I⊗I, (A⊗B')² = I⊗I, (A'⊗B)² = I⊗I,
(A'⊗B')² = I⊗I. Sum = 4·I⊗I.

Cross terms: collect systematically. After cancellation, the surviving
terms are:

  AA'⊗BB' − AA'⊗B'B + A'A⊗BB' − A'A⊗B'B  (from the +,+,+,− pattern)

Wait — let me be more careful. The clean approach:

Define X = A ⊗ (B + B') and Y = A' ⊗ (B − B'). Then C = X + Y.

  C² = X² + Y² + XY + YX

  X² = A² ⊗ (B+B')² = I ⊗ (B² + BB' + B'B + B'²) = I ⊗ (2I + {B,B'})
  Y² = A'² ⊗ (B-B')² = I ⊗ (B² − BB' − B'B + B'²) = I ⊗ (2I − {B,B'})

So X² + Y² = I ⊗ 4I = 4(I ⊗ I).

  XY + YX = (AA' + A'A) ⊗ (B+B')(B−B')
           = {A,A'} ⊗ (B² − BB' + B'B − B'²)
           = {A,A'} ⊗ (−[B,B'] + [B',B])  ... hmm, this isn't clean.

**Actually, the cleanest proof for formalization uses a different route.**

### 1.3 The Tsirelson bound — clean algebraic proof

**Theorem.** Let A, A' be self-adjoint operators on a Hilbert space H_A
with A² = I, A'² = I. Let B, B' be self-adjoint operators on H_B with
B² = I, B'² = I. Then for C = A⊗B + A⊗B' + A'⊗B − A'⊗B' acting on
H_A ⊗ H_B:

  C² ≤ 8·I

**Proof.** We use the operator inequality route (no explicit C² expansion).

For any unit vector ψ ∈ H_A ⊗ H_B:

  ⟨ψ, C²ψ⟩ = ‖Cψ‖²

We need to show ‖Cψ‖² ≤ 8.

Write C = A ⊗ (B + B') + A' ⊗ (B − B'). Then by the triangle inequality
for the norm:

  ‖Cψ‖ ≤ ‖(A ⊗ (B+B'))ψ‖ + ‖(A' ⊗ (B−B'))ψ‖

Since A is unitary-like (A² = I, self-adjoint, so A is an involution,
hence ‖Av‖ = ‖v‖):

  ‖(A ⊗ (B+B'))ψ‖ = ‖(I ⊗ (B+B'))ψ‖

Similarly: ‖(A' ⊗ (B−B'))ψ‖ = ‖(I ⊗ (B−B'))ψ‖

So: ‖Cψ‖ ≤ ‖(I ⊗ (B+B'))ψ‖ + ‖(I ⊗ (B−B'))ψ‖

Now apply Cauchy-Schwarz on ℝ²: for a,b ≥ 0, a + b ≤ √2 · √(a² + b²).

  ‖Cψ‖ ≤ √2 · √(‖(I⊗(B+B'))ψ‖² + ‖(I⊗(B−B'))ψ‖²)

Expand:
  ‖(I⊗(B+B'))ψ‖² + ‖(I⊗(B−B'))ψ‖²
  = ⟨ψ, (I⊗(B+B')²)ψ⟩ + ⟨ψ, (I⊗(B−B')²)ψ⟩
  = ⟨ψ, I⊗((B+B')² + (B−B')²)ψ⟩
  = ⟨ψ, I⊗(2B² + 2B'²)ψ⟩
  = ⟨ψ, I⊗(4I)ψ⟩
  = 4‖ψ‖² = 4

Therefore: ‖Cψ‖ ≤ √2 · √4 = 2√2.

Hence |⟨ψ, Cψ⟩| ≤ ‖Cψ‖ · ‖ψ‖ ≤ 2√2.  □

**Constructive note.** Every step is constructive:
- The involution property A² = I is algebraic (finite-dimensional).
- The norm preservation ‖A⊗Xψ‖ = ‖Xψ‖ uses A*A = A² = I.
- Cauchy-Schwarz on ℝ² is (a+b)² ≤ 2(a²+b²), a finite inequality.
- The expansion (B+B')² + (B−B')² = 2B² + 2B'² = 4I is algebra.
- No limits, no suprema, no infinite processes.

### 1.4 Finite-dimensional entanglement entropy

Let ρ be a density matrix on ℂ^d_A ⊗ ℂ^d_B (positive semidefinite,
Tr(ρ) = 1). The partial trace is:

  ρ_A = Tr_B(ρ) ∈ M_{d_A}(ℂ)

defined by ⟨i|ρ_A|j⟩ = Σ_k ⟨ik|ρ|jk⟩.

The von Neumann entropy is:

  S(ρ_A) = −Tr(ρ_A log ρ_A)

For a finite-dimensional positive semidefinite matrix with eigenvalues
λ₁, ..., λ_d (all ≥ 0, summing to 1):

  S(ρ_A) = −Σᵢ λᵢ log λᵢ

where 0 log 0 := 0 by convention.

**Constructive content.** Each step:
- Partial trace: finite sum of matrix entries. BISH.
- Eigenvalue computation: for d_A × d_A Hermitian matrix, eigenvalues
  are roots of the characteristic polynomial. For d_A = 2 (qubit):
  λ± = (1 ± √(1 − 4·det(ρ_A))) / 2. Constructive.
- Entropy: −Σ λᵢ log λᵢ where λᵢ are constructive reals in [0,1].
  The function x ↦ −x log x is continuous on [0,1] (with value 0 at 0).
  Applied to finitely many constructive reals. BISH.

**Key subtlety.** If an eigenvalue is 0, the convention 0 log 0 = 0
must be handled. In BISH, we cannot decide whether λᵢ = 0 or λᵢ > 0
without an omniscience principle. However, the function η(x) = −x log x
extends continuously to [0,∞) with η(0) = 0, so the entropy is well-defined
as a constructive real without case-splitting on whether eigenvalues vanish.
This is the key insight: we use continuity of η, not decidability of
equality.

**For formalization, restrict to the qubit case (d_A = 2).** This gives:
- ρ_A is a 2×2 positive Hermitian matrix with Tr = 1.
- Eigenvalues λ, 1−λ with λ ∈ [0,1].
- S(ρ_A) = −λ log λ − (1−λ) log(1−λ) = h(λ), the binary entropy.
- h is continuous on [0,1] with h(0) = h(1) = 0, h(1/2) = log 2.

For the Bell state |Ψ⁻⟩ = (|01⟩ − |10⟩)/√2:
- ρ_A = (1/2)I (maximally mixed).
- S(ρ_A) = log 2. Maximal entanglement.

---

## 2. Formalization Architecture

### 2.1 Module structure

```
Paper11_Entanglement/
├── Defs.lean              -- Core definitions (CHSH operator, involution,
│                             partial trace, binary entropy)
├── TensorBasic.lean       -- Tensor product algebra lemmas
│                             (A⊗X)(B⊗Y) = AB⊗XY, norms, etc.
├── InvolutionNorm.lean    -- ‖A⊗Xψ‖ = ‖Xψ‖ when A² = I
├── TsirelsonBound.lean    -- The main CHSH bound: |⟨ψ,Cψ⟩| ≤ 2√2
├── PartialTrace.lean      -- Partial trace for finite-dim tensor products
├── BinaryEntropy.lean     -- η(x) = −x log x, binary entropy h(λ),
│                             continuity, values at 0, 1/2, 1
├── BellState.lean         -- Bell state construction, partial trace
│                             computation, entropy = log 2
├── Main.lean              -- Assembly + #print axioms audit
└── Papers.lean            -- Module imports
```

Estimated total: 500–800 lines.

### 2.2 Mathlib dependencies

**For Part A (Tsirelson bound):**
- `Mathlib.Analysis.InnerProductSpace.Basic` — inner product, Cauchy-Schwarz
- `Mathlib.Analysis.InnerProductSpace.Adjoint` — self-adjoint operators
- `Mathlib.LinearAlgebra.TensorProduct.Basic` — tensor product of modules
- `Mathlib.Topology.Algebra.Module.FiniteDimension` — finite-dim normed spaces
- `Mathlib.Analysis.SpecialFunctions.Pow.Real` — √2

Investigate whether Mathlib's `TensorProduct` for normed spaces has:
- `TensorProduct.map` or `TensorProduct.lift` for bilinear maps
- Norm on tensor product (projective tensor norm)
- The identity ‖(A ⊗ I)v‖ = ‖v‖ when A is isometric

**IMPORTANT FALLBACK:** If Mathlib's abstract tensor product infrastructure
is too heavy, work with concrete matrices instead. For ℂ² ⊗ ℂ² ≅ ℂ⁴,
represent everything as 4×4 matrices over ℂ. The CHSH operator becomes a
concrete 4×4 matrix, and the bound becomes a norm estimate on a 4×4
self-adjoint matrix. This is less elegant but much more tractable in Lean.

**Recommended approach: Matrix formalization.**

```
-- Work in Matrix (Fin 4) (Fin 4) ℂ for the composite system
-- Alice's operators: 2×2 matrices tensored up to 4×4
-- Bob's operators: 2×2 matrices tensored up to 4×4
```

Use:
- `Mathlib.LinearAlgebra.Matrix.Hermitian` — Hermitian matrices
- `Mathlib.LinearAlgebra.Matrix.PosDef` — positive definite
- `Mathlib.Data.Matrix.Kronecker` — Kronecker product (= tensor product
  for matrices)
- `Mathlib.Analysis.Matrix` — matrix norms

The Kronecker product `Matrix.kroneckerMap` in Mathlib gives:
  (A ⊗ₖ B) * (C ⊗ₖ D) = (A * C) ⊗ₖ (B * D)

This is exactly the mixed-product property we need.

**For Part B (Entanglement entropy):**
- `Mathlib.Analysis.SpecialFunctions.Log.Basic` — Real.log
- `Mathlib.Analysis.SpecialFunctions.Log.Deriv` — continuity of log
- `Mathlib.Topology.ContinuousFunction.Basic` — continuous extension
- `Mathlib.LinearAlgebra.Matrix.Trace` — matrix trace
- `Mathlib.LinearAlgebra.Matrix.Hermitian` — eigenvalues

For the binary entropy function:
- `Mathlib.Analysis.SpecialFunctions.Log.NNReal` might be useful
- Need η(x) = −x * Real.log x, defined on [0,∞) with η(0) = 0
- This requires showing lim_{x→0⁺} x log x = 0

---

## 3. Detailed Proof — Part A: Tsirelson Bound

### 3.1 Definitions

```lean
/-- An involution: self-adjoint with A² = I -/
structure Involution (n : ℕ) where
  mat : Matrix (Fin n) (Fin n) ℂ
  sq_eq_one : mat * mat = 1
  hermitian : mat.conjTranspose = mat

/-- The CHSH operator as a 4×4 matrix.
    C = A ⊗ B + A ⊗ B' + A' ⊗ B − A' ⊗ B'
    where ⊗ is the Kronecker product -/
noncomputable def chshOperator (A A' : Involution 2) (B B' : Involution 2) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  A.mat.kroneckerMap (· * ·) B.mat
  + A.mat.kroneckerMap (· * ·) B'.mat
  + A'.mat.kroneckerMap (· * ·) B.mat
  - A'.mat.kroneckerMap (· * ·) B'.mat
```

**Lean note:** Check whether `Matrix.kroneckerMap` is the right API or
whether `Matrix.kronecker` exists. The key property needed is the
mixed-product rule: `(A.kronecker B) * (C.kronecker D) = (A*C).kronecker (B*D)`.
Search Mathlib for `kronecker_mul_kronecker` or `kroneckerMap_mul`.

### 3.2 The norm-preservation lemma

```lean
/-- For an involution A on ℂⁿ and any vector v,
    ‖(A ⊗ I) v‖ = ‖v‖.
    Proof: (A⊗I)*(A⊗I) = A²⊗I² = I⊗I, so A⊗I is an isometry. -/
lemma involution_tensor_norm_eq (A : Involution n)
    (v : EuclideanSpace ℂ (Fin (n * m))) :
    ‖(A.mat.kronecker (1 : Matrix (Fin m) (Fin m) ℂ)).mulVec v‖ = ‖v‖ := by
  -- A.mat.kronecker 1 is an isometry because its square is the identity
  -- (A*A) ⊗ (1*1) = 1 ⊗ 1 = 1
  sorry
```

**Proof strategy.** Show that M := A.mat.kronecker 1 satisfies
M.conjTranspose * M = 1 (unitary), hence mulVec M is an isometry.
- A.hermitian gives A.mat.conjTranspose = A.mat
- kronecker_conjTranspose: (A ⊗ I)* = A* ⊗ I* = A ⊗ I
- So (A⊗I)*(A⊗I) = (A⊗I)(A⊗I) = A²⊗I = I⊗I = I

### 3.3 The sum-of-squares identity

```lean
/-- (B+B')² + (B−B')² = 2B² + 2B'² = 4I when B² = I, B'² = I -/
lemma sum_sq_add_diff_sq (B B' : Involution n) :
    (B.mat + B'.mat) * (B.mat + B'.mat)
    + (B.mat - B'.mat) * (B.mat - B'.mat)
    = 4 • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  -- Expand: (B+B')² = B² + BB' + B'B + B'²  = I + BB' + B'B + I
  -- (B-B')² = B² - BB' - B'B + B'² = I - BB' - B'B + I
  -- Sum = 4I (cross terms cancel)
  ring_nf
  simp [B.sq_eq_one, B'.sq_eq_one]
  ring
```

**Lean note:** The `ring` tactic should handle most of this after
`sq_eq_one` is substituted. But matrix algebra over ℂ with `ring` can
be unpredictable. May need `ext` to go entry-wise, or use `Matrix.mul_add`,
`Matrix.add_mul`, etc.

### 3.4 The Cauchy-Schwarz step on ℝ²

```lean
/-- For a, b ≥ 0: (a + b)² ≤ 2(a² + b²) -/
lemma add_sq_le_two_mul_sum_sq (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  nlinarith [sq_nonneg (a - b)]
```

This is the ℝ² Cauchy-Schwarz inequality (a+b)² ≤ 2(a²+b²), equivalent
to (a-b)² ≥ 0. The `nlinarith` tactic with hint `sq_nonneg (a - b)`
should close this immediately.

### 3.5 Main theorem assembly

```lean
/-- The Tsirelson bound: for any involutions A, A', B, B' and
    unit vector ψ, |⟨ψ, CHSH·ψ⟩| ≤ 2√2.

    Proof outline:
    1. Write C = (A⊗(B+B')) + (A'⊗(B−B'))
    2. ‖Cψ‖ ≤ ‖A⊗(B+B')ψ‖ + ‖A'⊗(B−B')ψ‖   (triangle ineq)
    3.        = ‖(B+B')ψ‖ + ‖(B−B')ψ‖          (involution norm)
    4.        ≤ √2 · √(‖(B+B')ψ‖² + ‖(B−B')ψ‖²)  (Cauchy-Schwarz ℝ²)
    5.        = √2 · √4 = 2√2                    (sum-of-squares identity)
    6. |⟨ψ,Cψ⟩| ≤ ‖Cψ‖ ≤ 2√2                  (Cauchy-Schwarz inner prod)
-/
theorem tsirelson_bound (A A' : Involution 2) (B B' : Involution 2)
    (ψ : EuclideanSpace ℂ (Fin 4)) (hψ : ‖ψ‖ = 1) :
    ‖inner ψ ((chshOperator A A' B B').mulVec ψ)‖ ≤ 2 * Real.sqrt 2 := by
  sorry
```

**Proof steps for the formalization agent:**

Step 1. Rewrite `chshOperator` as sum of two terms:
  `C = (A.mat.kronecker (B.mat + B'.mat)) + (A'.mat.kronecker (B.mat - B'.mat))`
This requires showing the Kronecker product distributes over addition:
  `A ⊗ B + A ⊗ B' = A ⊗ (B + B')`
Search Mathlib: `kroneckerMap_add_right` or similar.

Step 2. Apply triangle inequality for `mulVec`:
  `‖C.mulVec ψ‖ ≤ ‖(A⊗(B+B')).mulVec ψ‖ + ‖(A'⊗(B-B')).mulVec ψ‖`
Use `norm_add_le`.

Step 3. Apply involution norm preservation (§3.2):
  `‖(A⊗M).mulVec ψ‖ = ‖(I⊗M).mulVec ψ‖`
This is the key structural lemma.

Step 4. Apply Cauchy-Schwarz on ℝ² (§3.4).

Step 5. Compute the sum of norms squared using §3.3:
  `‖(I⊗(B+B')).mulVec ψ‖² + ‖(I⊗(B-B')).mulVec ψ‖² = 4`
This uses (B+B')²+(B-B')² = 4I and ‖ψ‖ = 1.

Step 6. Conclude 2√2 · 1 = 2√2.

**Constructive note.** No step uses excluded middle, choice, or any
omniscience principle. The proof is: tensor product algebra (BISH),
norm triangle inequality (BISH), Cauchy-Schwarz on ℝ² (BISH), algebraic
identity (BISH). #print axioms should show only [propext, Quot.sound]
— the minimal Lean kernel axioms. NO Classical.choice.

---

## 4. Detailed Proof — Part B: Entanglement Entropy

### 4.1 Definitions

```lean
/-- The binary entropy function h(p) = -p log p - (1-p) log (1-p)
    Defined on [0,1] using the convention 0 log 0 = 0 via the
    continuous extension of η(x) = -x log x. -/
noncomputable def binaryEntropy (p : ℝ) : ℝ :=
  -(p * Real.log p) - ((1 - p) * Real.log (1 - p))

/-- The η function: η(x) = -x log x, with η(0) = 0.
    This is the building block for von Neumann entropy.
    We define it via the continuous extension. -/
noncomputable def eta (x : ℝ) : ℝ :=
  if x = 0 then 0 else -(x * Real.log x)
```

**Lean note on η(0) = 0.** The issue is that `Real.log 0 = 0` in Mathlib
(since log is defined on all of ℝ with log x = 0 for x ≤ 0). So actually
`0 * Real.log 0 = 0 * 0 = 0` and the conditional is unnecessary. Check
whether Mathlib's `Real.log_zero` gives `Real.log 0 = 0`. If so, we can
define eta simply as `fun x => -(x * Real.log x)` without case split.

**This is a significant simplification for constructivity.** If Mathlib
defines Real.log 0 = 0 (which it does by convention), then η(x) = -x log x
is a single expression with no case split, hence no decidability issue.

### 4.2 Properties of η

```lean
/-- η is continuous on [0, ∞) -/
lemma eta_continuous : ContinuousOn eta (Set.Ici 0) := by
  -- η(x) = -x log x is continuous on (0,∞) by continuity of x and log x
  -- At x = 0: lim_{x→0⁺} x log x = 0, so η extends continuously
  sorry

/-- η(0) = 0 -/
lemma eta_zero : eta 0 = 0 := by
  simp [eta, Real.log_zero]

/-- η(1) = 0 -/
lemma eta_one : eta 1 = 0 := by
  simp [eta, Real.log_one]

/-- η(1/2) = (log 2) / 2 -/
lemma eta_half : eta (1/2) = Real.log 2 / 2 := by
  simp [eta, Real.log_inv]
  ring
```

**Lean note.** The continuity proof at 0 requires `tendsto_mul_log_zero`
or equivalent from Mathlib. Search for:
- `Real.tendsto_log_mul_rpow_nhds_zero` or
- `Filter.Tendsto.mul` combined with `Real.tendsto_log_nhdsWithin_zero_top`

**IMPORTANT FALLBACK.** If the limit proof is difficult, axiomatize:
```lean
axiom eta_continuousOn : ContinuousOn (fun x : ℝ => -(x * Real.log x)) (Set.Ici 0)
```
Mark this as a bridge lemma (AxCal style) and note in the paper.
The constructive status is unaffected — continuity of η is a BISH fact,
and the axiom is mathematically uncontroversial.

### 4.3 Binary entropy properties

```lean
/-- h(p) = η(p) + η(1-p) -/
lemma binaryEntropy_eq_eta (p : ℝ) :
    binaryEntropy p = eta p + eta (1 - p) := by
  simp [binaryEntropy, eta]
  ring

/-- h(1/2) = log 2 (maximal entropy for a qubit) -/
lemma binaryEntropy_half : binaryEntropy (1/2) = Real.log 2 := by
  rw [binaryEntropy_eq_eta]
  simp [eta_half]
  ring

/-- h(0) = 0 (pure state) -/
lemma binaryEntropy_zero : binaryEntropy 0 = 0 := by
  rw [binaryEntropy_eq_eta, eta_zero, eta_one, add_zero]

/-- h(1) = 0 (pure state) -/
lemma binaryEntropy_one : binaryEntropy 1 = 0 := by
  rw [binaryEntropy_eq_eta, eta_one, eta_zero, zero_add]
```

### 4.4 Partial trace (qubit case)

For the formalization, we work with 4×4 matrices (ℂ² ⊗ ℂ² ≅ ℂ⁴) and
define the partial trace over the second subsystem explicitly.

```lean
/-- Partial trace over the second qubit.
    For ρ : Matrix (Fin 4) (Fin 4) ℂ representing a state on ℂ²⊗ℂ²,
    the partial trace over B gives a 2×2 matrix:
    (Tr_B ρ)_{ij} = ρ_{i0,j0} + ρ_{i1,j1}
    where we use the index mapping (i,k) ↦ 2i+k. -/
def partialTraceB (ρ : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => ρ (Fin.mk (2 * i.val) (by omega)) (Fin.mk (2 * j.val) (by omega))
           + ρ (Fin.mk (2 * i.val + 1) (by omega)) (Fin.mk (2 * j.val + 1) (by omega))
```

**Lean note.** The index arithmetic `(i,k) ↦ 2i+k` mapping
Fin 2 × Fin 2 → Fin 4 needs careful handling. An alternative is to
define ρ on `(Fin 2 × Fin 2)` from the start and use `Finset.sum` over
the traced-out index.

### 4.5 Bell state computation

```lean
/-- The Bell state |Ψ⁻⟩ = (|01⟩ - |10⟩)/√2 as a unit vector in ℂ⁴ -/
noncomputable def bellStateMinus : EuclideanSpace ℂ (Fin 4) :=
  (1 / Real.sqrt 2) • (EuclideanSpace.single 1 1 - EuclideanSpace.single 2 1)
  -- Index 1 = |01⟩, Index 2 = |10⟩ in the standard basis

/-- The density matrix of the Bell state -/
noncomputable def bellDensityMatrix : Matrix (Fin 4) (Fin 4) ℂ :=
  -- |Ψ⁻⟩⟨Ψ⁻| as an explicit 4×4 matrix
  -- Only nonzero entries: ρ_{11} = 1/2, ρ_{12} = -1/2,
  --                       ρ_{21} = -1/2, ρ_{22} = 1/2
  -- (in 0-indexed: positions (1,1), (1,2), (2,1), (2,2))
  Matrix.of fun i j =>
    if (i = 1 ∧ j = 1) ∨ (i = 2 ∧ j = 2) then (1/2 : ℂ)
    else if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then (-1/2 : ℂ)
    else 0

/-- The partial trace of the Bell state density matrix is (1/2)I -/
theorem bellState_partialTrace :
    partialTraceB bellDensityMatrix = (1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [partialTraceB, bellDensityMatrix, Matrix.of] <;> norm_num

/-- The entanglement entropy of the Bell state is log 2 -/
theorem bellState_entropy :
    binaryEntropy (1/2 : ℝ) = Real.log 2 := binaryEntropy_half
```

**The Bell state computation is the flagship result.** It shows:
1. We can construct bipartite entangled states (BISH).
2. We can compute partial traces (BISH — finite sum).
3. We can compute entropy (BISH — continuous function evaluated at 1/2).
4. The answer log 2 (maximal qubit entanglement) is constructive.

### 4.6 Entropy for general qubit states

```lean
/-- For a 2×2 density matrix with eigenvalues λ and 1-λ,
    the von Neumann entropy is h(λ) = binaryEntropy(λ). -/
theorem vonNeumann_entropy_qubit (ρ_A : Matrix (Fin 2) (Fin 2) ℂ)
    (hpos : ρ_A.PosSemidef) (htr : ρ_A.trace = 1)
    (λ₁ : ℝ) (hλ : 0 ≤ λ₁ ∧ λ₁ ≤ 1)
    (heig : -- λ₁ and 1-λ₁ are eigenvalues of ρ_A
            ρ_A.IsHermitian ∧ sorry) :
    -- S(ρ_A) = h(λ₁)
    binaryEntropy λ₁ = binaryEntropy λ₁ := by rfl
```

**Lean note.** The eigenvalue computation for 2×2 Hermitian matrices
is the trickiest part to formalize cleanly. The characteristic polynomial
is λ² − (Tr ρ_A)λ + det ρ_A = λ² − λ + det ρ_A, giving eigenvalues
via the quadratic formula. Rather than formalizing eigendecomposition
in full generality, define the entropy directly via the trace formula
or axiomatize the spectral theorem for 2×2 Hermitian matrices.

**RECOMMENDED SIMPLIFICATION:** Instead of general eigendecomposition,
prove the result for diagonal density matrices (which suffice for the
Bell state partial trace (1/2)I) and note that the general case follows
from unitary invariance of entropy and the spectral theorem.

---

## 5. Assembly and Axiom Audit

### 5.1 Main.lean structure

```lean
-- Main.lean

import Paper11_Entanglement.TsirelsonBound
import Paper11_Entanglement.BellState

/-! # Paper 11: Constructive Cost of Quantum Entanglement

## Part A: The Tsirelson bound is BISH

The CHSH bound |⟨ψ, Cψ⟩| ≤ 2√2 is proved using only:
- Tensor product algebra (Kronecker product properties)
- Norm triangle inequality
- Cauchy-Schwarz on ℝ²
- Algebraic identity (B+B')² + (B-B')² = 4I

No omniscience or choice principles appear.

## Part B: Entanglement entropy is BISH

The von Neumann entropy of the reduced state of a Bell pair
is computed using only:
- Finite matrix arithmetic (partial trace)
- Continuous function evaluation (η at 1/2)

No omniscience or choice principles appear.
-/

-- Axiom audit
#print axioms tsirelson_bound
-- Expected: [propext, Quot.sound]
-- NO Classical.choice

#print axioms bellState_entropy
-- Expected: [propext, Quot.sound]
-- NO Classical.choice

#print axioms bellState_partialTrace
-- Expected: [propext, Quot.sound]
-- NO Classical.choice
```

### 5.2 What counts as success

The formalization succeeds if:

1. `tsirelson_bound` compiles with `#print axioms` showing NO
   `Classical.choice` and NO custom axioms.

2. `bellState_partialTrace` compiles with same axiom profile.

3. `bellState_entropy` compiles (possibly using `binaryEntropy_half`
   which is pure algebra).

**Acceptable compromises:**

- If the general Tsirelson bound is hard (abstract involutions on
  Kronecker products), prove it for SPECIFIC observables: the standard
  CHSH-maximizing choice A = σ_z, A' = σ_x, B = (σ_z+σ_x)/√2,
  B' = (σ_z−σ_x)/√2. This is a concrete 4×4 matrix computation and
  still demonstrates BISH-provability. The abstract version can be
  noted as a remark.

- If eigendecomposition is hard, the Bell state entropy via direct
  computation (eigenvalues of (1/2)I are both 1/2, done) suffices.

- If `eta_continuousOn` is hard, axiomatize it as a bridge lemma.

### 5.3 What would be surprising

If `Classical.choice` appears in #print axioms for EITHER theorem,
that is a genuine discovery — it would mean some step in the finite-
dimensional entanglement computation requires classical logic, which
would challenge the working hypothesis. Investigate carefully before
axiomatizing it away.

---

## 6. Estimated Effort and Risk Assessment

| Module | Lines | Risk | Notes |
|--------|-------|------|-------|
| Defs | 60 | Low | Standard definitions |
| TensorBasic | 80–120 | Medium | Kronecker product API may be thin |
| InvolutionNorm | 40–60 | Medium | Depends on Kronecker unitary lemmas |
| TsirelsonBound | 80–120 | Medium | Assembly of algebraic steps |
| PartialTrace | 40–60 | Low | Explicit finite computation |
| BinaryEntropy | 60–80 | Low–Med | η continuity might need axiom |
| BellState | 40–60 | Low | Concrete matrix computation |
| Main | 30 | Low | Assembly + audit |

**Total: 430–630 lines.**

**Primary risk:** Mathlib's Kronecker product API. If `Matrix.kroneckerMap`
doesn't have the mixed-product property or norm lemmas, substantial
infrastructure work is needed. The fallback (everything as explicit 4×4
matrices with `Fin 4` indices and `fin_cases` + `norm_num`) is ugly but
guaranteed to work.

**Secondary risk:** The involution-norm lemma (§3.2). If proving
‖(A⊗I)v‖ = ‖v‖ abstractly is hard, prove it for the specific Pauli
matrices used in CHSH. `σ_z² = I` and `σ_x² = I` are explicit 2×2
matrix computations.

---

## 7. Connection to Paper 10

### 7.1 New calibration table row

Upon completion, Paper 11 adds the following to the calibration table
of Paper 10:

| Layer | Principle | Status | Source |
|-------|-----------|--------|--------|
| Bell nonlocality (CHSH) | BISH | Calibrated | Paper 11 |
| Entanglement entropy (qubit) | BISH | Calibrated | Paper 11 |
| Partial trace (finite-dim) | BISH | Calibrated | Paper 11 |

### 7.2 What this means

The calibration table previously covered: states, limits, spectra,
uncertainty. It did not cover compositional structure. Paper 11
establishes that the compositional layer — tensor products, entanglement,
correlations — is BISH for finite-dimensional systems.

Combined with Papers 2–9, this means: **all logical costs in the
calibration programme arise from infinite-dimensional idealization,
not from quantum compositional structure.**

This is the strongest evidence yet for the working hypothesis: nature's
relational structure is constructively accessible; only the mathematical
scaffolding of infinite-dimensional analysis incurs non-constructive costs.

---

## 8. For the Formalization Agent — Quick Start

### 8.1 Priority order

1. **First:** Set up the project, import Mathlib, create module structure.

2. **Second:** Formalize `bellState_partialTrace` — this is the easiest
   win. It's a concrete 4×4 matrix computation. Use `fin_cases` and
   `norm_num` to verify each entry.

3. **Third:** Formalize `binaryEntropy_half` — pure algebra with
   `Real.log`.

4. **Fourth:** Formalize the Cauchy-Schwarz ℝ² lemma — one-liner with
   `nlinarith`.

5. **Fifth:** Formalize `tsirelson_bound` — this is the main effort.
   Start with the concrete-matrix approach if Kronecker API is thin.

### 8.2 Key Mathlib searches

Before starting, search Mathlib for:
```
Matrix.kroneckerMap
Matrix.kronecker_mul_kronecker  (or similar mixed-product property)
Matrix.mulVec_kronecker
EuclideanSpace.norm_eq
Real.log_zero
Real.log_one
Real.log_inv
inner_self_eq_norm_sq
norm_add_le
```

If `Matrix.kronecker_mul_kronecker` doesn't exist, this is the biggest
infrastructure gap. Fallback: prove it for 2×2 matrices specifically,
or work entirely with explicit 4×4 matrices.

### 8.3 No-sorry target

The goal is ZERO sorries. Every lemma should be fully proved.
The only acceptable `axiom` is `eta_continuousOn` if the limit
proof at 0 is genuinely difficult — and this should be marked
clearly as a bridge lemma.

### 8.4 Testing

After each module compiles:
1. Run `#print axioms` on the main theorems.
2. Verify NO `Classical.choice` appears.
3. If `Classical.choice` appears, identify which lemma introduced it
   (likely a Mathlib lemma using `Decidable` instances or `Classical.dec`).
   Replace with constructive alternatives.

**Common source of unwanted Classical.choice in Mathlib:** decidability
instances for equality or ordering on ℝ. If this appears, use
`open Classical in` judiciously and document why it's benign (meta-level
classical reasoning, not object-level), OR find constructive alternatives.

---

## Appendix A: Pauli Matrices for Concrete Fallback

If the abstract involution approach is too heavy, use explicit Pauli
matrices throughout.

```lean
def σ_x : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def σ_y : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def σ_z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
def I₂ : Matrix (Fin 2) (Fin 2) ℂ := 1

-- Verify involution properties
lemma σ_x_sq : σ_x * σ_x = 1 := by ext i j; fin_cases i <;> fin_cases j <;> simp [σ_x, Matrix.mul_apply] <;> norm_num
lemma σ_z_sq : σ_z * σ_z = 1 := by ext i j; fin_cases i <;> fin_cases j <;> simp [σ_z, Matrix.mul_apply] <;> norm_num

-- Standard CHSH-maximizing observables:
-- A = σ_z, A' = σ_x
-- B = (σ_z + σ_x)/√2, B' = (σ_z - σ_x)/√2
-- These achieve the Tsirelson bound exactly.
```

The concrete approach replaces all abstract reasoning with `fin_cases`
enumeration and `norm_num` computation. It's guaranteed to compile but
produces verbose proofs. For a 4×4 matrix, this means at most 16 cases
per lemma — tedious but tractable.

---

## Appendix B: Why This Is Not Trivial

One might object: "Of course finite-dimensional linear algebra is
constructive — it's just matrix multiplication." This misses the point.

The Tsirelson bound is not merely a matrix computation. It is a *bound
on all possible measurements* — a universally quantified statement over
all involutions and all unit vectors. The proof must work for arbitrary
observables, not just specific numerical instances. The algebraic
structure that makes this possible (the sum-of-squares identity, the
norm-preservation under involution tensoring) is what the formalization
verifies.

Similarly, the entanglement entropy computation involves the *function*
η(x) = -x log x, which requires reasoning about real-valued functions
on [0,1]. The constructive status of this function — specifically, the
handling of the point x = 0 — is nontrivial and is resolved by the
continuity of η rather than by case-splitting on whether eigenvalues
vanish.

The contribution of this paper is not that finite things are finite.
It is that the *conceptual infrastructure of quantum entanglement* —
Bell inequalities, entanglement measures, partial traces — lives at
BISH, adding a new column to the calibration table that no previous
paper addressed.
