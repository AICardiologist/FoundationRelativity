# Paper 53: The CM Decidability Oracle
## Specification for Lean 4 Implementation

### What We Are Building

A verified decision procedure for numerical equivalence on products of CM elliptic curves. Given two algebraic cycles Z, W on E^n (where E is one of the 13 CM elliptic curves over ℚ), the oracle outputs `true` or `false` for "Z ≡_num W" — and carries a Lean proof that the output is correct.

This is Paper 50 Theorem C made computational. Paper 50 proved the 13 CM elliptic motives are BISH-decidable. Paper 53 exhibits the decider.

---

## PART 1: THE MATHEMATICS (What the Lean code must implement)

### 1.1 The 13 CM Elliptic Curves

The CM elliptic curves over ℚ correspond to the 13 imaginary quadratic fields K = ℚ(√-d) with class number 1:

| d  | K           | j-invariant        | End(E) ⊗ ℚ  |
|----|-------------|--------------------|--------------| 
| 1  | ℚ(i)        | 1728               | ℚ(i)         |
| 2  | ℚ(√-2)      | 8000               | ℚ(√-2)       |
| 3  | ℚ(√-3)      | 0                  | ℚ(√-3)       |
| 7  | ℚ(√-7)      | -3375              | ℚ(√-7)       |
| 11 | ℚ(√-11)     | -32768             | ℚ(√-11)      |
| 19 | ℚ(√-19)     | -884736            | ℚ(√-19)      |
| 43 | ℚ(√-43)     | -884736000         | ℚ(√-43)      |
| 67 | ℚ(√-67)     | -147197952000      | ℚ(√-67)      |
| 163| ℚ(√-163)    | -262537412640768000| ℚ(√-163)     |

Plus 4 more with non-maximal orders (d = 3 order ℤ[√-3], d = 4 order ℤ[i] index 2, d = 7 order index 2, d = 8 order index 2). The exact list is:

Discriminants D: -3, -4, -7, -8, -11, -12, -16, -19, -27, -28, -43, -67, -163

For each, End(E) is an order O_D in K = ℚ(√D), and End(E) ⊗ ℚ = K.

### 1.2 The Cycle Algebra on E^n

For a CM elliptic curve E with End(E) ⊗ ℚ = K (an imaginary quadratic field), the numerical Chow ring of E^n is completely determined by the endomorphism algebra.

**Key fact (Lieberman 1968):** For abelian varieties, homological equivalence = numerical equivalence. This is unconditional. So we work with numerical equivalence throughout.

**The cycle algebra.** CH*(E^n)_num ⊗ ℚ is generated as a ℚ-algebra by:
- The n fundamental classes [E_i] (codimension 0 of each factor)
- The n divisor classes [0_i] (the origin on each factor, codimension 1)
- The graph classes [Γ_φ] for each φ ∈ End(E) (codimension 1 on E × E)
- Products of the above

For a CM elliptic curve, End(E) ⊗ ℚ = K, so the graph classes are parameterized by elements of K.

**Intersection numbers.** Everything reduces to computing deg(Γ_φ · Γ_ψ) on E × E for φ, ψ ∈ End(E). The fundamental formula is:

    deg(Γ_φ · Γ_ψ) = deg(φ - ψ) = Nm_{K/ℚ}(φ - ψ)

where Nm is the norm of the imaginary quadratic field. This is a finite computation in K.

More generally, for cycles on E^n, the intersection matrix is determined by the Gram matrix of the Néron-Tate height pairing, which for CM curves is computed by the CM period relations.

### 1.3 The Decision Procedure

**Input:** 
- A discriminant D from the list of 13
- An integer n (the power E^n)
- Two algebraic cycles Z₁, Z₂ ∈ CH^r(E^n), represented as ℚ-linear combinations of basis cycles (products of graph classes and divisor classes)

**Output:** 
- A boolean: `true` if Z₁ ≡_num Z₂, `false` otherwise

**Algorithm:**
1. Compute Z = Z₁ - Z₂ 
2. Compute the intersection number deg(Z · W) for every basis element W of CH^{n-r}(E^n)_num ⊗ ℚ
3. Each intersection number reduces to a ℚ-linear combination of terms Nm_{K/ℚ}(α) for α ∈ K
4. These are rational numbers, computable exactly
5. Z ≡_num 0 iff all intersection numbers are zero
6. Return `true` if all zero, `false` if any nonzero

**Termination:** The basis of CH^{n-r}(E^n)_num ⊗ ℚ is finite (bounded by the Betti numbers). The norm computation in K is a finite operation over ℚ. The algorithm terminates.

**Correctness:** By definition of numerical equivalence, Z ≡_num 0 iff deg(Z · W) = 0 for all W. Since we test against a basis, this is equivalent to testing against all W. The intersection numbers are computed correctly by the norm formula.

### 1.4 The Rosati Positivity Check

As a bonus, the oracle can verify Axiom 3 (Archimedean polarization) computationally:

For each CM discriminant D, compute the intersection matrix on CH^1(E × E)_num ⊗ ℚ with respect to a basis of graph classes. Verify that the Rosati involution (induced by a principal polarization) produces a positive-definite form on the primitive part. This is a finite eigenvalue computation over ℚ(√D).

This provides a computational certificate that all three DPT axioms hold for the CM elliptic motive.

---

## PART 2: THE LEAN 4 ARCHITECTURE

### 2.1 What Mathlib Provides

Check these exist in current Mathlib (as of Feb 2026):

- `Mathlib.NumberTheory.NumberField.Basic` — number fields, ring of integers
- `Mathlib.NumberTheory.NumberField.Norm` — field norms
- `Mathlib.RingTheory.Discriminant` — discriminants
- `Mathlib.LinearAlgebra.BilinearForm` — bilinear forms, definiteness
- `Mathlib.LinearAlgebra.QuadraticForm.Basic` — quadratic forms
- `Mathlib.Analysis.InnerProductSpace.Basic` — inner product spaces
- `Mathlib.Data.Matrix.Basic` — matrices, determinants
- `Mathlib.Algebra.Order.Field.Basic` — ordered fields

### 2.2 File Structure

```
Paper53/
├── CMData.lean          -- The 13 CM discriminants, fields, j-invariants
├── EndomorphismRing.lean -- End(E) as an order in K = ℚ(√D)
├── CycleAlgebra.lean    -- CH*(E^n)_num ⊗ ℚ as a finite-dim ℚ-vector space
├── IntersectionPairing.lean -- The norm formula: deg(Γ_φ · Γ_ψ) = Nm(φ-ψ)
├── Decider.lean         -- The decision procedure with correctness proof
├── RosatiCheck.lean     -- Computational verification of Axiom 3
├── Examples.lean        -- #eval calls on concrete inputs
└── Main.lean            -- Top-level theorem statements
```

### 2.3 Core Definitions

```lean
-- CMData.lean

/-- The 13 discriminants with class number 1 -/
def cmDiscriminants : List ℤ := 
  [-3, -4, -7, -8, -11, -12, -16, -19, -27, -28, -43, -67, -163]

/-- A CM elliptic curve is specified by its discriminant -/
structure CMEllipticCurve where
  D : ℤ
  hD : D ∈ cmDiscriminants
  -- The CM field is ℚ(√D)

/-- The imaginary quadratic field ℚ(√D) -/
-- Use Mathlib's NumberField infrastructure or define concretely:
-- Elements are pairs (a, b) representing a + b√D with a, b ∈ ℚ
structure QuadField (D : ℤ) where
  re : ℚ 
  im : ℚ   -- coefficient of √D

/-- Field norm: Nm(a + b√D) = a² - Db² -/
def QuadField.norm (D : ℤ) (z : QuadField D) : ℚ :=
  z.re ^ 2 - D * z.im ^ 2

/-- The norm is always rational (this is trivial but state it) -/
theorem norm_rational (D : ℤ) (z : QuadField D) : 
    ∃ q : ℚ, QuadField.norm D z = q := ⟨_, rfl⟩
```

```lean
-- CycleAlgebra.lean

/-- A cycle on E^n is a ℚ-linear combination of basis cycles.
    Basis cycles in codimension r on E^n are indexed by:
    - subsets S ⊂ {1,...,n} of size r (for products of [0_i])
    - plus graph classes Γ_φ for endomorphisms φ
    
    For simplicity, represent as a vector in ℚ^m where m = dim CH^r(E^n)_num -/
structure Cycle (D : ℤ) (n : ℕ) (r : ℕ) where
  coeffs : Fin (basisSize D n r) → ℚ

/-- The intersection pairing: a bilinear form ℚ^m × ℚ^m → ℚ -/
def intersectionMatrix (D : ℤ) (n : ℕ) (r : ℕ) : 
    Matrix (Fin (basisSize D n r)) (Fin (basisSize D n r)) ℚ :=
  -- Entries computed from the norm formula
  sorry -- This is the main computation to implement
```

```lean
-- Decider.lean

/-- The decision procedure -/
def numericallyEquivalent (D : ℤ) (hD : D ∈ cmDiscriminants) 
    (n : ℕ) (r : ℕ) (Z₁ Z₂ : Cycle D n r) : Bool :=
  let Z := Z₁ - Z₂
  let M := intersectionMatrix D n (n - r)  -- complementary codimension
  -- Z ≡_num 0 iff M * Z.coeffs = 0
  (M.mulVec Z.coeffs) = 0

/-- Correctness: the decider agrees with numerical equivalence -/
theorem decider_correct (D : ℤ) (hD : D ∈ cmDiscriminants)
    (n : ℕ) (r : ℕ) (Z₁ Z₂ : Cycle D n r) :
    numericallyEquivalent D hD n r Z₁ Z₂ = true ↔ 
    Z₁ ≡_num Z₂ := by
  sorry -- Needs: intersection matrix correctly computes deg(Z · W) for all W
         -- This is the bridge from linear algebra to algebraic geometry
         -- Acceptable sorry: it axiomatizes Lieberman + norm formula
```

```lean
-- RosatiCheck.lean

/-- Verify positive-definiteness of primitive intersection form -/
def rosatiPositive (D : ℤ) (hD : D ∈ cmDiscriminants) : Bool :=
  -- Compute the intersection matrix on CH^1(E×E)_prim
  -- Check all eigenvalues of the relevant principal minor are positive
  -- This is a finite computation over ℚ(√D)
  sorry -- Implementation: compute matrix, check leading principal minors > 0

/-- DPT certificate: all three axioms verified computationally -/
structure DPTCertificate (D : ℤ) where
  hD : D ∈ cmDiscriminants
  axiom1 : ∀ n r (Z₁ Z₂ : Cycle D n r), Decidable (Z₁ ≡_num Z₂)
  axiom2 : AlgebraicSpectrum D  -- eigenvalues of Frobenius are algebraic integers
  axiom3 : rosatiPositive D hD = true  -- Archimedean polarization verified
```

```lean
-- Examples.lean

-- Concrete computations that #eval can run

/-- E: y² = x³ - x (j = 1728, D = -4, End = ℤ[i]) -/
#eval numericallyEquivalent (-4) (by decide) 2 1 
  ⟨![1, 0, 0]⟩   -- the diagonal Δ
  ⟨![0, 1, 1]⟩   -- [E×0] + [0×E]
-- Expected: false (these are not numerically equivalent)

/-- Verify: Δ · Δ = deg(id - id) = 0... wait, 
    Δ · (E×0) = 1, (E×0 + 0×E) · (E×0) = 0 + 1 = 1
    So they agree on E×0. Check all basis elements. -/

#eval numericallyEquivalent (-4) (by decide) 2 1
  ⟨![0, 0, 0]⟩   -- the zero cycle  
  ⟨![0, 0, 0]⟩   -- the zero cycle
-- Expected: true

/-- Rosati positivity for j = 1728 -/
#eval rosatiPositive (-4) (by decide)
-- Expected: true

/-- Rosati positivity for all 13 CM curves -/
#eval cmDiscriminants.map (fun D => 
  if h : D ∈ cmDiscriminants then rosatiPositive D h else false)
-- Expected: [true, true, true, true, true, true, true, true, 
--            true, true, true, true, true]
```

### 2.4 The Sorry Budget

**Zero sorries (must achieve):**
- The linear algebra: definite bilinear form has trivial radical
- The norm computation: Nm_{K/ℚ}(a + b√D) = a² - Db²  
- The decidability of ℚ-equality
- The `#eval` computations (these either run or they don't)

**Principled sorries (acceptable, clearly marked):**
- `intersectionMatrix_correct`: the matrix entries equal the geometric intersection numbers. This axiomatizes Fulton's intersection theory on E^n.
- `lieberman`: homological = numerical for abelian varieties. This is a deep theorem we cite but don't prove.
- `norm_formula`: deg(Γ_φ · Γ_ψ) = Nm(φ - ψ). This is classical CM theory.
- `basis_spans`: the chosen basis of CH^r(E^n) is complete. This is a Betti number computation.

**These sorries are the interface between verified computation and cited algebraic geometry.** The paper's honest claim is: "IF the intersection matrix is as classical CM theory computes, THEN the decider is correct, AND here are the outputs on concrete inputs."

---

## PART 3: THE PAPER STRUCTURE

### 3.1 What Paper 53 Claims

**Theorem A (The Oracle).** There exists a verified decision procedure for numerical equivalence on products of the 13 CM elliptic curves. The procedure is implemented in Lean 4, compiles with zero errors, and produces correct outputs on all tested inputs.

**Theorem B (DPT Certificates).** For each of the 13 CM discriminants, the decision procedure computationally verifies all three DPT axioms: decidable equality (Axiom 1) by construction, algebraic spectrum (Axiom 2) by computing Frobenius eigenvalues as Weil numbers in K, and Archimedean polarization (Axiom 3) by checking positive-definiteness of the Rosati form on primitive components.

**Theorem C (Computability Boundary).** The oracle extends to E^n for arbitrary n. The time complexity is polynomial in n (the intersection matrix has size bounded by the Betti numbers of E^n, which grow polynomially). The oracle does NOT extend to CM abelian varieties of dimension ≥ 4, where the intersection matrix on the exotic part of the cycle algebra cannot be computed without the Hodge conjecture.

### 3.2 Sections

§1. Introduction — Paper 50 proved decidability; this paper exhibits the decider.

§2. The CM data — the 13 discriminants, endomorphism rings, intersection formulas.

§3. The cycle algebra — CH*(E^n)_num as a finite-dimensional ℚ-vector space, the norm formula for intersection numbers.

§4. The decision procedure — algorithm, termination proof, correctness proof (modulo the intersection matrix axiom).

§5. The Rosati certificate — computational verification of Axiom 3 for all 13 curves.

§6. Examples and outputs — concrete #eval results demonstrating the oracle.

§7. The boundary — why the oracle stops at dimension 3 (exotic classes at dimension 4).

---

## PART 4: INSTRUCTIONS FOR THE LEAN AI

### Step 1: Set up the project
```bash
lake init Paper53
cd Paper53
# Add Mathlib dependency to lakefile.lean
```

### Step 2: Implement QuadField
Define ℚ(√D) as pairs (a, b) ∈ ℚ × ℚ with field operations. Prove it's a field. Implement the norm. This should be straightforward — Mathlib may already have `Zsqrtd` or `GaussianInt` that can be adapted.

### Step 3: Implement the intersection matrix for E × E
Start with n = 2 (the simplest nontrivial case). For E with CM by K = ℚ(√D):

CH^1(E × E)_num ⊗ ℚ has basis:
- e₁ = [E × 0]  (pullback of a point from first factor)
- e₂ = [0 × E]  (pullback of a point from second factor)  
- e₃ = [Δ]      (the diagonal, = graph of identity)

If End(E) ⊗ ℚ = K and K has more than just ℤ (i.e., D ≠ -3, -4 which have units), the basis includes:
- e₄ = [Γ_ω]   (graph of the CM endomorphism ω = (1+√D)/2 or √D)

The intersection matrix on CH^1(E×E) is:
```
deg(eᵢ · eⱼ) for the basis elements
```

Key formulas:
- deg([E×0] · [0×E]) = 1
- deg([E×0] · [E×0]) = 0  
- deg([Δ] · [E×0]) = 1
- deg([Δ] · [Δ]) = -deg(id) = ... wait, this needs care.

Actually: on E × E, the self-intersection of the diagonal is deg(Δ · Δ) = χ(E) = 0 for an elliptic curve (Euler characteristic). But in the Chow ring modulo numerical equivalence, we need the full intersection theory.

**IMPORTANT:** For E × E with E an elliptic curve:
- deg([E×0]²) = 0
- deg([0×E]²) = 0  
- deg([E×0] · [0×E]) = 1
- deg([Δ]²) = deg(c₁(N_{Δ/E×E})) = deg(-T_E) = 2 - 2g = 0 for g = 1

Hmm, so the diagonal has self-intersection 0 on E × E. Let me reconsider.

For codimension 1 on a surface (E × E is a surface), the intersection pairing is the Néron-Severi pairing. For E × E with End(E) = O_K:

NS(E × E) ⊗ ℚ = M₂(K) restricted to "Rosati-symmetric" = Hermitian matrices over K

Actually, the cleanest formulation: 

NS(E × E) ⊗ ℚ ≅ End(E) ⊗ ℚ ⊕ ℚ·[E×0] ⊕ ℚ·[0×E]

Wait — the standard result is:

Hom(E, E) = End(E), and for E × E:
NS(E × E) ⊗ ℚ ≅ ℚ ⊕ ℚ ⊕ End(E) ⊗ ℚ

where the first ℚ is [E×0], the second is [0×E], and End(E) ⊗ ℚ gives the graph classes.

For End(E) ⊗ ℚ = K (2-dimensional over ℚ), NS(E×E) ⊗ ℚ is 4-dimensional.

The intersection form: for graph classes Γ_φ, Γ_ψ on E × E:

    deg(Γ_φ · Γ_ψ) = 1 - deg(φ - ψ) + 1 ... 

No wait. The standard formula for curves C₁, C₂ on a surface:

For Γ_φ (graph of φ: E → E) and Γ_ψ (graph of ψ):
    Γ_φ · Γ_ψ = number of fixed points of φ - ψ (with multiplicity)
              = 1 - Tr(φ - ψ) + deg(φ - ψ)    (Lefschetz fixed point formula... but that's for the graph)

Actually for elliptic curves E, if φ: E → E has no fixed points:
    Γ_φ · Γ_ψ = deg(φ - ψ) when φ ≠ ψ

And:
    Γ_φ · Γ_φ = -deg(φ') where φ' = dφ (the differential)
    
Hmm, this is getting into the weeds. Let me just state the correct formula and let the Lean AI verify it computationally.

**THE CORRECT FORMULA** (for the Lean AI to implement):

For an elliptic curve E and endomorphisms φ, ψ ∈ End(E):

    deg(Γ_φ · Γ_ψ) = deg(φ - ψ)  if φ ≠ ψ
    deg(Γ_φ · Γ_φ) = 2 - Tr(φ)... 

No. Let me look this up properly. The intersection number of two graph classes on E × E:

Let pr₁, pr₂: E × E → E be the projections. Then Γ_φ = {(x, φ(x))} and:

    Γ_φ · Γ_ψ = deg(pr₁|_{Γ_φ ∩ Γ_ψ}) = #{x : φ(x) = ψ(x)} = deg(φ - ψ)

when φ - ψ is a nonzero isogeny. When φ = ψ, the intersection is the self-intersection of Γ_φ, which by adjunction on E × E (a surface) equals:

    Γ_φ² = 2p_a(Γ_φ) - 2 + (K_{E×E} · Γ_φ)

Since K_{E×E} = 0 (E × E is an abelian surface) and Γ_φ ≅ E has p_a = 1:

    Γ_φ² = 2(1) - 2 + 0 = 0

So: **Every graph class on E × E has self-intersection 0.**

And for distinct endomorphisms:
    Γ_φ · Γ_ψ = deg(φ - ψ) = Nm_{K/ℚ}(φ - ψ)

This is completely explicit and computable.

Similarly:
    [E×0] · [E×0] = 0
    [0×E] · [0×E] = 0
    [E×0] · [0×E] = 1
    [E×0] · Γ_φ = 1  (the graph meets E×{0} once)
    [0×E] · Γ_φ = deg(φ)

So the intersection matrix is entirely determined by the norm form of K and the degrees of endomorphisms.

**FOR THE LEAN AI:** Implement this intersection matrix explicitly for each D. The norm Nm_{K/ℚ}(a + b√D) = a² - Db² is the only computation needed. Everything else is combinatorics (tracking which basis elements pair with which).

### Step 4: Extend to E^n
For E^n, the cycles are generated by pullbacks and pushforwards of the E × E data along the various projection/inclusion maps. The intersection theory reduces to sums of terms from the E × E case. The Lean AI should implement this recursively.

### Step 5: The Rosati check
For each D, compute the intersection matrix M on the primitive part of CH^1(E × E)_num ⊗ ℚ. Primitive means: mod out by the span of L(CH^0) = span of [H] where H is a polarization.

Check that M is positive-definite (all eigenvalues positive). For a 2×2 or 3×3 rational matrix, this is: check det > 0 and trace > 0 (for 2×2), or check leading principal minors are all positive (Sylvester's criterion).

### Step 6: Run #eval
Produce concrete outputs. The money shot is:

```lean
#eval allCMCurvesDecidable  -- outputs: true
#eval allRosatiPositive      -- outputs: true  
#eval dptCertificateAll13    -- outputs: [✓, ✓, ✓, ✓, ✓, ✓, ✓, ✓, ✓, ✓, ✓, ✓, ✓]
```

These are the computational certificates that the DPT specification is satisfied.

---

## PART 5: WHAT SUCCESS LOOKS LIKE

The Lean project compiles with zero errors. The #eval calls produce output. The sorry budget is exactly the interface between computation and algebraic geometry (the intersection matrix axiom, Lieberman's theorem, the norm formula). The logical architecture (decidability from definiteness) has zero sorries.

The paper can then say: "We have exhibited a verified decision procedure for numerical equivalence on CM elliptic motives. The procedure runs, produces correct outputs, and its correctness proof compiles in Lean 4. The DPT specification of Paper 50 is not merely a characterization — it is a computational certificate that can be verified by machine."

That's what "the decidability is real" means.
