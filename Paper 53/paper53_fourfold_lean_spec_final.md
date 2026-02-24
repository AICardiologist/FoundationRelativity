# Paper 53 Fourfold Extension: Lean Specification (Final v3)

## Summary for the Lean AI

You are extending a working Lean 4 project (Paper53/P53_CMOracle/) that 
verifies decidability for CM elliptic curves. The extension computes the 
self-intersection of an exotic Weil class on an abelian fourfold, testing 
the dimension-4 boundary of the DPT framework.

---

## THE MATHEMATICS

### 1. Weil-Type Abelian Varieties (van Geemen CIME §5.2)

An abelian variety X of dimension 2n has "Weil type" w.r.t. K = ℚ(√-d)
if K embeds in End(X) ⊗ ℚ with the eigenvalue condition on T₀X.

The K-Hermitian form attached to a Weil-type polarization E:

    H(x, y) = E(x, (√-d)*y) + √-d · E(x, y)

Properties (van Geemen CIME Lemma 5.2):
- Hermitian on the K-vector space V = H¹(X, ℚ), K-dim 2n
- Signature (n, n)
- In standard form: H = diag(a, 1, ..., 1, -1, ..., -1) with a > 0
- det H = (-1)ⁿ · a with a ∈ ℚ_{>0}
- For n = 2 (fourfold): det H = a > 0

### 2. Eigenspace Decomposition (van Geemen CIME §6.10)

Over ℂ, V_ℂ = W ⊕ W̄ where W, W̄ are eigenspaces for √-d.

**ISOTROPICITY (proved in CIME §6.10):** W and W̄ are isotropic for E.
Proof: for x, y ∈ W, dE(x,y) = E((√-d)*x, (√-d)*y) = E(√-dx, √-dy) 
= -dE(x,y), so E|_{W×W} = 0.

E induces a perfect duality W ≅ W̄*.

### 3. Weil Classes (van Geemen CIME §4.9, Theorem 6.12)

The space of Weil-Hodge classes:
    ⋀²ⁿ_K H¹(X, ℚ) ↪ Bⁿ(X)

2-dimensional over ℚ, 1-dimensional over K.

After base change: W(X) ⊗ K = K·ω₊ ⊕ K·ω₋

By isotropicity of W, W̄:
- ⟨ω₊, ω₊⟩ = 0
- ⟨ω₋, ω₋⟩ = 0
- ⟨ω₊, ω₋⟩ = c ∈ K, c ≠ 0

### 4. Self-Intersection of a ℚ-Rational Weil Class

    w = ω₊ + ω₋  (ℚ-rational)
    
    deg(w · w) = Tr_{K/ℚ}(c)

### 5. Hodge-Riemann Prediction

For a real primitive (p,p)-class α on a compact Kähler n-fold, with 
2p = n (middle cohomology):

    (-1)^{n(n-1)/2} · i^{p-q} · ∫ α ∧ ᾱ > 0

For our case (n = 4, p = q = 2, real class so ᾱ = α):

    (-1)^6 · 1 · deg(α²) > 0  ⟹  deg(w · w) > 0

**Prediction: deg(w · w) > 0.**

### 6. The Cross-Pairing from the Hermitian Matrix

For H = diag(h₁, h₂, h₃, h₄) over K with signature (2,2):

The cross-pairing c depends on the elementary symmetric functions of 
the hᵢ. The exact formula is pinned down by the following:

**REGRESSION TEST (van Geemen, SIGMA 2022, arXiv:2108.02087):**

For X = J × J (pp abelian surface J), K = ℚ(i):
- H = diag(1, 1, -1, -1), det H = 1
- In basis {ω₁², ω_σ², ω₂²} for diagonal Hodge classes aω₁²+bω_σ²+cω₂²:
  - Weil class conic C_K:  4b² = ac
  - Square-zero locus S₀:  3b² = -ac

These two equations uniquely determine the intersection matrix entries.

**IMPLEMENTATION STRATEGY:** 
1. Parameterize the intersection form on the 3-dim space B²(X) as a 
   function of det H (the only invariant for signature (2,2) forms).
2. For the J × J test case, compute the 3×3 matrix in the {ω₁², ω_σ², ω₂²}
   basis using the alternating form E and Hermitian form H.
3. Verify the two conic equations.
4. Once verified, apply the same computation to Milne's H = diag(1,-1,-1,1).
5. Extract Tr_{K/ℚ}(c) and report the sign.

### 7. Milne's Example (Acta Arith. 100, 2001, Example 1.8)

- K = ℚ(√-3)
- B = elliptic curve with j = 0, CM by K
- A = CM abelian 3-fold, CM type (E, Φ₀), E = F·K, 
  F = ℚ[t]/(t³+t²-2t-1)
- X = A × B, dimension 4

Hermitian form: H = H_A ⊥ H_B

H_B = (1) on the 1-dim K-space H¹(B, ℚ)

H_A has signature (1, 2) on the 3-dim K-space H¹(A, ℚ).
In suitable K-basis: H_A = diag(1, -1, -1)

Total: H = diag(1, -1, -1, 1), det H = 1 > 0 ✓

The Weil class is algebraic (Schoen 1998, Comp. Math. 65).

---

## LEAN IMPLEMENTATION

### New Files

```
WeilType.lean           -- H definition, signature, det
WeilClass.lean          -- Eigenspace decomposition, isotropic
CrossPairing.lean       -- c from H, self-intersection formula
RegressionTest.lean     -- J×J conic verification  
MilneExample.lean       -- H = diag(1,-1,-1,1), specific data
SignComputation.lean    -- Tr(c), sign, Hodge-Riemann check
BoundaryTheorem.lean    -- Theorems C + D
```

### Key Definitions

```lean
/-- A Weil-type Hermitian form: diagonal over K with signature (n,n) -/
structure WeilHermitian (n : ℕ) where
  K_disc : ℤ                          -- discriminant of K = ℚ(√K_disc)
  entries : Fin (2*n) → ℚ             -- diagonal entries h₁,...,h_{2n}
  sig_pos : (entries.filter (· > 0)).length = n
  sig_neg : (entries.filter (· < 0)).length = n

/-- Discriminant: product of diagonal entries -/
def WeilHermitian.det (H : WeilHermitian n) : ℚ :=
  (Finset.univ.prod (fun i => H.entries i))

/-- Discriminant constraint: det H = (-1)^n · a, a > 0 -/
theorem det_sign (H : WeilHermitian n) : 
    (-1)^n * H.det > 0 := by sorry  -- follows from signature

/-- Cross-pairing: the nonzero mixed term ⟨ω₊, ω₋⟩ -/
-- This is the formula to be determined by regression test
def crossPairing (H : WeilHermitian 2) : QuadFieldQ H.K_disc :=
  sorry  -- THE KEY FORMULA — pin down via regression test

/-- Self-intersection of ℚ-rational Weil class -/
def weilSelfIntersection (H : WeilHermitian 2) : ℚ :=
  let c := crossPairing H
  2 * c.re  -- Tr_{K/ℚ}(a + b√d) = 2a for quadratic fields
```

### Regression Test

```lean
/-- J × J test case: K = ℚ(i), H = diag(1,1,-1,-1) -/
def testH_JxJ : WeilHermitian 2 := {
  K_disc := -1,
  entries := ![1, 1, -1, -1],
  sig_pos := by decide,
  sig_neg := by decide
}

/-- Verify conic C_K: 4b² = ac in the J×J intersection form -/
theorem regression_CK : ... := by sorry  -- verify from intersection matrix

/-- Verify square-zero: 3b² = -ac -/
theorem regression_S0 : ... := by sorry  -- verify from intersection matrix

#eval regressionCheck  -- must output: true
```

### Milne Example

```lean
/-- Milne's CM abelian fourfold: H = diag(1,-1,-1,1) over ℚ(√-3) -/
def milneH : WeilHermitian 2 := {
  K_disc := -3,
  entries := ![1, -1, -1, 1],
  sig_pos := by decide,
  sig_neg := by decide
}

#eval milneH.det  
-- Expected: 1 (> 0, ✓)

#eval weilSelfIntersection milneH
-- Expected: a specific positive rational number

#eval weilSelfIntersection milneH > 0
-- Expected: true (Hodge-Riemann confirmed)
```

### Axiom Budget (6 new, 5 existing = 11 total)

**Existing (CM elliptic, unchanged):**
1. basis_spans_CH1_E2
2. lieberman_hom_eq_num
3. norm_formula_intersection
4. intersectionMatrix_E2_correct
5. decider_correct

**New (fourfold extension):**
6. hermitian_form_van_geemen — H(x,y) = E(x,(√-d)*y) + √-d·E(x,y)
7. eigenspace_isotropic — W, W̄ isotropic for E
8. cross_pairing_formula — c = ⟨ω₊, ω₋⟩ from H (pinned by regression)
9. milne_cm_type_hermitian — H_A = diag(1,-1,-1) for CM type Φ₀
10. schoen_algebraicity — Weil class algebraic for K=ℚ(√-3), det=1

### What MUST #eval (no sorry)

- det(diag(1,-1,-1,1)) = 1
- Regression test for J × J conics = true
- Tr_{ℚ(√-3)/ℚ}(c) = [specific number]
- Sign check = true or false
- All QuadFieldQ arithmetic

---

## THEOREMS THE PAPER CLAIMS

**Theorem A** (existing): CM elliptic decider, 13 curves, verified.

**Theorem B** (existing): DPT certificates for all 13 CM curves.

**Theorem C** (new): For Milne's CM abelian fourfold A × B:
  (i)   deg(w · w) = [number], confirming Hodge-Riemann
  (ii)  The exotic Weil class lies outside the Lefschetz ring
  (iii) Regression-tested against van Geemen's conic identities

**Theorem D** (new): The DPT decidability boundary is dimension 4:
  - dim 1–3: decidable (Paper 52 + Theorem A)
  - dim 4: exotic class exists, is algebraic, satisfies HR, 
    but lies outside Lefschetz ring control
  - The decider cannot extend without the Hodge conjecture as input
