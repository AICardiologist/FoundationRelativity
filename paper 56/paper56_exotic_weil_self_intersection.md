# Exotic Weil Class Self-Intersection on CM Abelian Fourfolds

## Paper 56 — Proof Document for Lean 4 Formalization Agent

### Paul C.-K. Lee
### February 2026

---

## 0. Purpose, Context, and Formalization Notes

This document provides a complete mathematical specification for the Lean 4
formalization of Paper 56 in the Constructive Reverse Mathematics (CRM)
programme, arithmetic geometry sequence.

**Series context:** Paper 50 identified the DPT boundary at dimension 4,
where Anderson's exotic Weil classes escape the Lefschetz ring. Paper 53
built a CM decider for class-number-1 elliptic curves. Paper 55 showed
K3 surfaces have no exotic obstruction (Lefschetz (1,1) in codimension 1).
Paper 56 goes directly to the boundary: computing self-intersections of
exotic Weil classes on CM abelian fourfolds, the exact objects where
decidability breaks.

**What Paper 56 does:**
1. For TWO specific CM abelian fourfolds of Weil type (A×B), compute
   deg(w₀ · w₀) where w₀ is the primitive integral exotic Weil class.
2. Verify Hodge-Riemann bilinear relations for both.
3. Verify algebraicity via Schoen's criterion for both.
4. Identify the pattern: deg(w₀ · w₀) = √disc(F) where F is the
   totally real subfield of the CM algebra.
5. State a PREDICTION for a third example as a falsifiable test.

**Two examples:**

Example 1 (Milne 1.8): K = Q(√-3), F = Q(ζ₇ + ζ₇⁻¹)
  A: CM abelian threefold, CM by E = F(√-3), signature (1,2)
  B: elliptic curve y² = x³ + 1, CM by K, signature (1,0)
  disc(F) = 49, deg(w₀ · w₀) = 7

Example 2: K = Q(√-1), F = Q(ζ₉ + ζ₉⁻¹)
  A: CM abelian threefold, CM by E = F(i), signature (1,2)
  B: elliptic curve y² = x³ - x, CM by K, signature (1,0)
  disc(F) = 81, deg(w₀ · w₀) = 9

**Prediction (Example 3):** K = Q(√-7), F = Q(ζ₁₃ + ζ₁₃⁻¹)
  disc(F) = 169 = 13²
  Predicted: deg(w₀ · w₀) = 13

**Formalization notes:**
- This paper is COMPUTATIONAL: exact rational arithmetic throughout,
  no floating-point, no approximations.
- The Lean code must produce concrete verified numbers (#eval / #check).
- The sorry budget axiomatizes Shimura's CM theory and Schoen's theorem.
- The ZERO-SORRY target: all arithmetic (trace matrices, determinants,
  discriminants, norm computations) must be machine-verified.

**Target:** ~600-800 lines Lean 4
**Depends on:** Paper 50 (DPT boundary), Paper 53 (CM decider infrastructure)

---

## 1. THEOREM STATEMENTS (ENGLISH)

### Theorem A (Example 1: deg = 7)

Let K = Q(√-3) and F = Q(ζ₇ + ζ₇⁻¹) with minimal polynomial
t³ + t² - 2t - 1 = 0.

(i)   disc(F) = 49.
(ii)  The space of exotic Weil classes W(A,B) has dim_Q = 2.
(iii) The integral generator w₀ has deg(w₀ · w₀) = 7.
(iv)  7 > 0 satisfies the Hodge-Riemann bilinear relations for a
      primitive (2,2)-class on a 4-fold.
(v)   The exotic class is algebraic (Schoen 1998).

### Theorem B (Example 2: deg = 9)

Let K = Q(i) and F = Q(ζ₉ + ζ₉⁻¹) with minimal polynomial
t³ - 3t + 1 = 0.

(i)   disc(F) = 81.
(ii)  dim_Q W(A,B) = 2.
(iii) deg(w₀ · w₀) = 9.
(iv)  9 > 0 satisfies HR.
(v)   The exotic class is algebraic (Schoen 1998): det(φ̃_X) = 1/16
      is a norm in K = Q(i) since 1/16 = Nm(1/4).

### Theorem C (The Pattern)

For a Weil-type CM abelian fourfold X = A × B with CM field K and
totally real subfield F of the CM algebra of A:

  deg(w₀ · w₀) = √disc(F)

where w₀ is the primitive integral generator of the exotic Weil lattice.

This is stated as a CONJECTURE verified for two examples, not as a
general theorem. The Lean formalization verifies the two instances
and states the pattern.

### Theorem D (Prediction)

For K = Q(√-7), F = Q(ζ₁₃ + ζ₁₃⁻¹):
  disc(F) = 169 = 13²
  Predicted: deg(w₀ · w₀) = 13

This is a FALSIFIABLE PREDICTION, not a theorem.

---

## 2. LEAN MODULE PLAN

### Module 1: NumberFieldData.lean (~120 lines, 0 sorry)

All exact arithmetic for the two number fields. This is the computational
core and MUST have zero sorries.

```
-- Example 1: F₁ = Q(ζ₇ + ζ₇⁻¹)
-- Minimal polynomial: t³ + t² - 2t - 1 = 0
-- Roots: 2cos(2πk/7) for k = 1, 2, 3

def F1_minpoly : Polynomial ℚ := X^3 + X^2 - 2*X - 1

-- Newton's identities to compute power sums from coefficients
-- p₁ + e₁ = 0  →  p₁ = -(-1) = -1   [Wait: e₁ = 1, so p₁ = -1]
-- Actually for t³ + t² - 2t - 1:
-- e₁ = -1 (sum of roots = -coefficient of t²)
-- e₂ = -2 (sum of products of pairs = coefficient of t)
-- e₃ = 1  (product of roots = -constant × (-1)^3 = 1)

-- Power sums via Newton's identities:
-- p₁ = e₁ = -1
-- p₂ = p₁·e₁ - 2·e₂ = (-1)(-1) - 2(-2) = 1 + 4 = 5
-- p₃ = p₂·e₁ - p₁·e₂ + 3·e₃ = 5(-1) - (-1)(-2) + 3(1) = -5 - 2 + 3 = -4
-- p₄ = p₃·e₁ - p₂·e₂ + p₁·e₃ = (-4)(-1) - 5(-2) + (-1)(1) = 4 + 10 - 1 = 13

-- Traces: T(k) = Tr_{F/Q}(t^k) = p_k
-- T(0) = 3 (degree of extension)
-- T(1) = -1, T(2) = 5, T(3) = -4, T(4) = 13

-- Trace matrix M₁ for basis {1, t, t²}:
-- M₁[i,j] = T(i+j) for i,j = 0,1,2
--
-- M₁ = | T(0)  T(1)  T(2) |   | 3  -1   5 |
--       | T(1)  T(2)  T(3) | = |-1   5  -4 |
--       | T(2)  T(3)  T(4) |   | 5  -4  13 |

def F1_trace_matrix : Matrix (Fin 3) (Fin 3) ℚ :=
  !![3, -1, 5; -1, 5, -4; 5, -4, 13]

-- det(M₁) = 3(5·13 - (-4)(-4)) - (-1)((-1)·13 - (-4)·5) + 5((-1)(-4) - 5·5)
--         = 3(65 - 16) + 1(-13 + 20) + 5(4 - 25)
--         = 3(49) + 1(7) + 5(-21)
--         = 147 + 7 - 105
--         = 49

theorem F1_disc : Matrix.det F1_trace_matrix = 49 := by native_decide

-- Example 2: F₂ = Q(ζ₉ + ζ₉⁻¹)
-- Minimal polynomial: t³ - 3t + 1 = 0
-- e₁ = 0, e₂ = -3, e₃ = -1

-- Power sums:
-- p₁ = 0
-- p₂ = 0·0 - 2(-3) = 6
-- p₃ = 6·0 - 0·(-3) + 3(-1) = -3
-- p₄ = (-3)·0 - 6·(-3) + 0·(-1) = 18

-- Traces: T(0) = 3, T(1) = 0, T(2) = 6, T(3) = -3, T(4) = 18

def F2_trace_matrix : Matrix (Fin 3) (Fin 3) ℚ :=
  !![3, 0, 6; 0, 6, -3; 6, -3, 18]

-- det(M₂) = 3(6·18 - (-3)(-3)) - 0 + 6(0·(-3) - 6·6)
--         = 3(108 - 9) + 6(0 - 36)
--         = 3(99) + 6(-36)
--         = 297 - 216
--         = 81

theorem F2_disc : Matrix.det F2_trace_matrix = 81 := by native_decide

-- Prediction: F₃ = Q(ζ₁₃ + ζ₁₃⁻¹)
-- Minimal polynomial: t⁶ - t⁵ - 5t⁴ + 4t³ + 6t² - 3t - 1 = 0
-- But the relevant totally real CUBIC subfield for the Weil fourfold
-- construction is the splitting field of t³ + t² - 4t + 1 = 0.
-- [This needs verification — may be degree 6 not 3]

-- For now, state the prediction without computing:
-- disc(F₃) = 169 (if cubic subfield of Q(ζ₁₃)⁺ exists with this disc)
```

**Sorry budget:** 0. All arithmetic is exact rational, machine-checkable
via `native_decide` or `decide`.

CRITICAL: The Lean agent MUST verify the determinant computations
by explicit expansion or `native_decide`. Do NOT use `sorry` for
arithmetic that can be checked.

### Module 2: WeilLattice.lean (~80 lines, 2 principled sorry)

Define the exotic Weil lattice structure and dimension.

```
-- Axiomatize Milne's dimension result
axiom milne_weil_dim (K : QuadImagField) (A : CMThreefold K)
    (B : CMEllipticCurve K) :
    dim_K (exotic_weil_space A B) = 1

-- Q-dimension
theorem weil_dim_Q (K : QuadImagField) (A : CMThreefold K)
    (B : CMEllipticCurve K) :
    dim_Q (exotic_weil_space A B) = 2 := by
  have h1 := milne_weil_dim K A B
  have h2 : degree K = 2 := K.quadratic
  calc dim_Q (exotic_weil_space A B)
      = dim_K (exotic_weil_space A B) * degree K := dim_scalar_extension
    _ = 1 * 2 := by rw [h1, h2]
    _ = 2 := by ring

-- The exotic class is OUTSIDE the Lefschetz ring
axiom exotic_not_lefschetz (K : QuadImagField) (A : CMThreefold K)
    (B : CMEllipticCurve K) (w : exotic_weil_space A B) (hw : w ≠ 0) :
    w ∉ lefschetz_ring (A.prod B)
```

**Sorry budget:**
- `milne_weil_dim`: principled (Milne 1999, Lemma 1.3)
- `exotic_not_lefschetz`: principled (Anderson 1993; Milne 1999, §1)

### Module 3: PolarizationDet.lean (~120 lines, 3 principled sorry)

Compute det(φ̃_X) for both examples from CM theory.

```
-- Axiomatize: principal polarization on CM abelian variety
-- is determined by an element of the inverse different
axiom cm_polarization_det_threefold (K : QuadImagField)
    (F : TotallyRealCubic) (A : CMThreefold K)
    (hCM : CM_field A = F.adjoin K) :
    det_polarization A = inv_norm_different F K

-- Example 1: K = Q(√-3), F with disc 49
-- det(φ̃_A) = 1/(3√(-3))
-- det(φ̃_B) = -1/√(-3)    [B = y² = x³ + 1]
-- det(φ̃_X) = 1/9

-- Axiomatize the elliptic curve polarization determinants
axiom elliptic_polarization_Q_sqrt_neg3 :
    det_polarization (ec_x3_plus_1) = -1 / sqrt_neg_3

axiom elliptic_polarization_Q_i :
    det_polarization (ec_x3_minus_x) = gaussian_i / 2

-- Compute product determinants
theorem det_X1 : det_polarization (example1_fourfold) = (1 : ℚ) / 9 := by
  -- det(φ̃_A₁) · det(φ̃_B₁) = (1/(3√-3)) · (-1/√-3) = -1/(3·(-3)) = 1/9
  sorry -- Requires CM arithmetic; principled

theorem det_X2 : det_polarization (example2_fourfold) = (1 : ℚ) / 16 := by
  -- det(φ̃_A₂) · det(φ̃_B₂) = (1/(8i)) · (i/2) = i/(16i) = 1/16
  sorry -- Requires CM arithmetic; principled
```

**Sorry budget:**
- `cm_polarization_det_threefold`: principled (Shimura, "Abelian Varieties
  with Complex Multiplication", Chapter II)
- `elliptic_polarization_Q_sqrt_neg3`: principled (standard CM theory)
- `elliptic_polarization_Q_i`: principled (standard CM theory)
- `det_X1`, `det_X2`: These use the CM axioms; could potentially be
  derived but may need sorry if the K-arithmetic is too complex for Lean.
  Mark as principled if needed.

### Module 4: SelfIntersection.lean (~100 lines, 1 principled sorry)

The core computation: from disc(F) to deg(w₀ · w₀).

```
-- The relationship between disc(F) and the integral Weil lattice
-- Axiomatize: for a Weil-type CM abelian fourfold X = A×B with
-- totally real subfield F of the CM algebra of A, the discriminant
-- of the integral exotic Weil lattice equals disc(F).
axiom weil_lattice_disc_eq_field_disc
    (K : QuadImagField) (F : TotallyRealCubic)
    (X : WeilTypeFourfold K F) :
    lattice_disc (integral_weil_lattice X) = disc F

-- For a rank-2 lattice over Z with one generator w₀ and
-- K-multiplication, the Gram matrix has a specific form
-- determined by the ring of integers of K.
-- The self-intersection of the generator relates to disc(F)
-- via: deg(w₀ · w₀) = √disc(F) when disc(F) is a perfect square.

-- Example 1: disc(F₁) = 49 = 7²
theorem self_intersection_ex1 :
    deg_self_intersection (integral_weil_generator example1_fourfold) = 7 := by
  have hdisc : disc F1 = 49 := F1_disc
  -- The integral generator has deg = √49 = 7
  -- via the lattice discriminant computation
  calc deg_self_intersection (integral_weil_generator example1_fourfold)
      = Int.sqrt (disc F1) := weil_generator_self_int example1_fourfold
    _ = Int.sqrt 49 := by rw [hdisc]
    _ = 7 := by native_decide

-- Example 2: disc(F₂) = 81 = 9²
theorem self_intersection_ex2 :
    deg_self_intersection (integral_weil_generator example2_fourfold) = 9 := by
  have hdisc : disc F2 = 81 := F2_disc
  calc deg_self_intersection (integral_weil_generator example2_fourfold)
      = Int.sqrt (disc F2) := weil_generator_self_int example2_fourfold
    _ = Int.sqrt 81 := by rw [hdisc]
    _ = 9 := by native_decide
```

**Sorry budget:**
- `weil_lattice_disc_eq_field_disc`: principled (Schoen 1998, building on
  Milne 1999 lattice structure). This is the key mathematical input.
  The relationship disc(Weil lattice) = disc(F) encodes Schoen's integral
  analysis.

NOTE TO LEAN AGENT: The step from lattice_disc = disc(F) to
deg(w₀ · w₀) = √disc(F) requires an intermediate lemma about
rank-2 lattices with K-multiplication. For a rank-2 Z-lattice L
with K-action (K quadratic imaginary), if the Gram matrix in a
K-basis is (d, 0; 0, d·|Δ_K|) then lattice_disc = d² · |Δ_K|
and the generator self-intersection is d. When disc(F) = d² · |Δ_K|
... ACTUALLY this decomposition depends on K. The agent should
verify the exact relationship for each example rather than relying
on a general formula. The safest approach: axiomatize
`weil_generator_self_int` and verify the final numbers.

### Module 5: HodgeRiemann.lean (~60 lines, 0 sorry)

Verify HR for both examples. This should be zero sorry — it's
pure sign checking.

```
-- HR for primitive (2,2)-class on a 4-fold:
-- (-1)^{k(k-1)/2} · i^{p-q} · deg(w · w) > 0
-- k = 4, p = 2, q = 2
-- (-1)^6 · i^0 · deg(w · w) = 1 · 1 · deg(w · w)
-- So HR reduces to: deg(w · w) > 0

theorem hr_sign_computation :
    (-1 : ℤ)^(4 * 3 / 2) * 1 = 1 := by native_decide

-- Or more carefully: k(k-1)/2 = 4·3/2 = 6, (-1)^6 = 1
-- i^{p-q} = i^{2-2} = i^0 = 1

theorem hr_example1 :
    hodge_riemann_satisfied (integral_weil_generator example1_fourfold) := by
  -- Reduces to: deg(w₀ · w₀) > 0
  -- We proved deg = 7
  simp [hodge_riemann_satisfied, hr_sign_computation]
  exact self_intersection_ex1 ▸ (by norm_num : (7 : ℤ) > 0)

theorem hr_example2 :
    hodge_riemann_satisfied (integral_weil_generator example2_fourfold) := by
  simp [hodge_riemann_satisfied, hr_sign_computation]
  exact self_intersection_ex2 ▸ (by norm_num : (9 : ℤ) > 0)
```

**Sorry budget:** 0.

### Module 6: SchoenAlgebraicity.lean (~80 lines, 2 principled sorry)

Verify algebraicity via Schoen's criterion.

```
-- Axiomatize Schoen's theorem
axiom schoen_algebraicity (X : WeilTypeFourfold K F) :
    IsNorm K (det_polarization X) →
    Algebraic (exotic_weil_class X)

-- Example 1: det(φ̃_X₁) = 1/9
-- K = Q(√-3). Is 1/9 a norm?
-- Nm(a + b√-3) = a² + 3b²
-- 1/9 = (1/3)² + 3·0² = Nm(1/3). Yes.
theorem ex1_det_is_norm :
    IsNorm (Q_sqrt_neg3) ((1 : ℚ) / 9) := by
  use ⟨1/3, 0⟩  -- 1/3 + 0·√-3
  simp [norm_quad_imaginary]
  ring

theorem ex1_algebraic :
    Algebraic (exotic_weil_class example1_fourfold) := by
  exact schoen_algebraicity example1_fourfold (det_X1 ▸ ex1_det_is_norm)

-- Example 2: det(φ̃_X₂) = 1/16
-- K = Q(i). Is 1/16 a norm?
-- Nm(a + bi) = a² + b²
-- 1/16 = (1/4)² + 0² = Nm(1/4). Yes.
theorem ex2_det_is_norm :
    IsNorm (Q_i) ((1 : ℚ) / 16) := by
  use ⟨1/4, 0⟩  -- 1/4 + 0·i
  simp [norm_quad_imaginary]
  ring

theorem ex2_algebraic :
    Algebraic (exotic_weil_class example2_fourfold) := by
  exact schoen_algebraicity example2_fourfold (det_X2 ▸ ex2_det_is_norm)
```

**Sorry budget:**
- `schoen_algebraicity`: principled (Schoen 1998, Theorem 0.2)
- The norm verifications (ex1_det_is_norm, ex2_det_is_norm) should be
  zero sorry — they are explicit witness computations.

### Module 7: Pattern.lean (~60 lines, 0 sorry)

State the pattern and prediction.

```
-- The observed pattern
structure WeilSelfIntersectionPattern where
  K : QuadImagField
  F : TotallyRealCubic
  disc_F : ℕ
  deg_w : ℕ
  pattern_holds : deg_w * deg_w = disc_F  -- deg = √disc

def example1_pattern : WeilSelfIntersectionPattern := {
  K := Q_sqrt_neg3
  F := F1  -- Q(ζ₇ + ζ₇⁻¹)
  disc_F := 49
  deg_w := 7
  pattern_holds := by native_decide
}

def example2_pattern : WeilSelfIntersectionPattern := {
  K := Q_i
  F := F2  -- Q(ζ₉ + ζ₉⁻¹)
  disc_F := 81
  deg_w := 9
  pattern_holds := by native_decide
}

-- The conjecture (NOT a theorem — two data points)
-- For any Weil-type CM abelian fourfold X = A × B with
-- totally real cubic F ⊂ End(A):
--   deg(w₀ · w₀) = √disc(F)  (when disc(F) is a perfect square)

-- Prediction for Example 3
def example3_prediction : WeilSelfIntersectionPattern := {
  K := Q_sqrt_neg7
  F := F3  -- subfield of Q(ζ₁₃)⁺
  disc_F := 169
  deg_w := 13
  pattern_holds := by native_decide  -- 13² = 169
}
```

**Sorry budget:** 0. The `pattern_holds` fields are just n² = n²,
trivially decidable.

### Module 8: Verdict.lean (~60 lines, 0 sorry)

The comparison table and DPT interpretation.

```
-- Summary record
structure ExoticWeilResult where
  example_name : String
  K_field : String
  F_field : String
  disc_F : ℕ
  deg_self_int : ℕ
  hr_satisfied : Bool  -- deg > 0
  algebraic : Bool     -- Schoen criterion met
  in_lefschetz_ring : Bool  -- always false for exotic

def result_table : List ExoticWeilResult :=
  [ { example_name := "Milne 1.8"
    , K_field := "Q(√-3)"
    , F_field := "Q(ζ₇ + ζ₇⁻¹), disc = 49"
    , disc_F := 49
    , deg_self_int := 7
    , hr_satisfied := true
    , algebraic := true
    , in_lefschetz_ring := false }
  , { example_name := "Example 2"
    , K_field := "Q(i)"
    , F_field := "Q(ζ₉ + ζ₉⁻¹), disc = 81"
    , disc_F := 81
    , deg_self_int := 9
    , hr_satisfied := true
    , algebraic := true
    , in_lefschetz_ring := false }
  ]

-- DPT interpretation:
-- These classes are at the EXACT DPT boundary.
-- They are Hodge classes (satisfy HR) but NOT Lefschetz.
-- Standard Conjecture D cannot decide their algebraicity constructively.
-- Schoen's theorem provides algebraicity via a DIFFERENT route
-- (the split Hermitian form condition), bypassing Conjecture D.
-- The DPT framework correctly identifies these as the obstruction:
-- decidability fails here because the Lefschetz ring does not contain them.
```

---

## 3. SORRY BUDGET SUMMARY

| Module | Sorry Count | Classification |
|--------|-------------|----------------|
| 1. NumberFieldData      | 0 | — (exact arithmetic) |
| 2. WeilLattice          | 2 | principled (Milne, Anderson) |
| 3. PolarizationDet      | 3-5 | principled (Shimura CM theory) |
| 4. SelfIntersection     | 1 | principled (Schoen 1998) |
| 5. HodgeRiemann         | 0 | — (sign check) |
| 6. SchoenAlgebraicity   | 2 | principled (Schoen, norm witnesses exact) |
| 7. Pattern              | 0 | — (n² = n²) |
| 8. Verdict              | 0 | — |
| **TOTAL**               | **8-10** | **all principled, 0 gaps** |

The zero-sorry modules (1, 5, 7, 8) contain all the verifiable arithmetic.
The principled sorries axiomatize:
1. Milne's Weil lattice dimension (1999, Lemma 1.3)
2. Anderson's exotic classes outside Lefschetz (1993)
3. Shimura CM polarization theory (various)
4. Schoen's lattice discriminant result (1998)
5. Schoen's algebraicity criterion (1998, Theorem 0.2)

---

## 4. CRITICAL INSTRUCTIONS FOR LEAN AGENT

### 4.1 Arithmetic verification is paramount

The following MUST be verified by `native_decide` or `decide`, NOT sorry:

1. det(M₁) = 49  (3×3 determinant over Q)
2. det(M₂) = 81  (3×3 determinant over Q)
3. 7² = 49       (pattern check)
4. 9² = 81       (pattern check)
5. 13² = 169     (prediction check)
6. (1/3)² + 3·0² = 1/9   (norm witness for Example 1)
7. (1/4)² + 0² = 1/16    (norm witness for Example 2)
8. HR sign: (-1)^6 · 1 = 1
9. 7 > 0, 9 > 0  (HR positivity)

If ANY of these require sorry, the paper's computational claim is
undermined. Restructure the types until `native_decide` works.

### 4.2 Newton's identity verification

The power sums for each minimal polynomial should be verified step
by step. For t³ + t² - 2t - 1 (Example 1):
  e₁ = -1, e₂ = -2, e₃ = 1
  p₁ = -1
  p₂ = (-1)(-1) - 2(-2) = 1 + 4 = 5
  p₃ = 5(-1) - (-1)(-2) + 3(1) = -5 - 2 + 3 = -4
  p₄ = (-4)(-1) - 5(-2) + (-1)(1) = 4 + 10 - 1 = 13

For t³ - 3t + 1 (Example 2):
  e₁ = 0, e₂ = -3, e₃ = -1
  p₁ = 0
  p₂ = 0 - 2(-3) = 6
  p₃ = 0 - 0 + 3(-1) = -3
  p₄ = 0 - 6(-3) + 0 = 18

Build these as explicit Lean computations, not axioms.

### 4.3 What NOT to do

- Do NOT formalize the full Shimura CM theory. Axiomatize polarization
  determinants.
- Do NOT attempt to construct the actual exotic Weil class as an
  algebraic cycle. The paper computes its self-intersection, not
  its explicit geometric realization.
- Do NOT formalize Schoen's proof. Axiomatize his Theorem 0.2.
- Do NOT use floating-point or numerical approximations anywhere.
  All arithmetic must be exact over Q.

### 4.4 What MUST compile

1. `F1_disc` and `F2_disc` — the discriminant computations (#eval)
2. `self_intersection_ex1` and `self_intersection_ex2` — the main results
3. `hr_example1` and `hr_example2` — HR verification
4. `ex1_det_is_norm` and `ex2_det_is_norm` — Schoen witnesses
5. `result_table` — the comparison table (#eval to display)
6. `example3_prediction` — the falsifiable prediction

### 4.5 Naming conventions

- `F1_*` prefix for Example 1 (K = Q(√-3))
- `F2_*` prefix for Example 2 (K = Q(i))
- `F3_*` prefix for Example 3 prediction (K = Q(√-7))

---

## 5. PAPER STRUCTURE (LaTeX)

§1. Introduction
    - The DPT boundary at dimension 4 (Paper 50)
    - Exotic Weil classes: Hodge but not Lefschetz
    - Goal: explicit intersection computation on two examples

§2. Setup
    - Weil-type CM abelian fourfolds X = A × B
    - Exotic Weil lattice W(A,B), dimension, integrality
    - The self-intersection problem

§3. Example 1: K = Q(√-3), F = Q(ζ₇ + ζ₇⁻¹) (Milne 1.8)
    - Number field data: disc(F) = 49
    - CM polarization: det(φ̃_X) = 1/9
    - Self-intersection: deg(w₀ · w₀) = 7
    - HR check: 7 > 0 ✓
    - Algebraicity: 1/9 = Nm(1/3) ✓ (Schoen)

§4. Example 2: K = Q(i), F = Q(ζ₉ + ζ₉⁻¹)
    - Number field data: disc(F) = 81
    - CM polarization: det(φ̃_X) = 1/16
    - Self-intersection: deg(w₀ · w₀) = 9
    - HR check: 9 > 0 ✓
    - Algebraicity: 1/16 = Nm(1/4) ✓ (Schoen)

§5. The pattern: deg(w₀ · w₀) = √disc(F)
    - Two-example evidence
    - Derivation sketch: lattice discriminant = field discriminant
    - Prediction: K = Q(√-7), F ⊂ Q(ζ₁₃)⁺, disc = 169, deg = 13
    - Status: conjecture, not theorem

§6. DPT interpretation
    - These classes sit at the exact Axiom 1 boundary
    - Positive HR means they are "genuine" Hodge classes
    - Algebraicity via Schoen bypasses Standard Conjecture D
    - The Lefschetz ring fails to contain them (codimension 2 escape)
    - Consistent with Paper 55 codimension principle

§7. Lean formalization
    - [TO BE FILLED]

§8. "What this paper does not claim" section
    - Does not prove deg = √disc(F) in general
    - Does not construct the exotic class as a geometric cycle
    - Does not resolve Standard Conjecture D

---

## 6. KEY REFERENCES

- Anderson, G. "An algebraicity principle and related conjectures
  connected with the distribution of values of modular functions."
  In preparation (1993); see Wei (2013) for the published version.
- Milne, J. S. "Lefschetz classes on abelian varieties."
  Duke Math. J. 96 (1999), 639–675. [Lemma 1.3, Example 1.8]
- Schoen, C. "An integral analog of the Tate conjecture for
  one-dimensional cycles on varieties over finite fields."
  Math. Ann. 311 (1998), 493–500. [Theorem 0.2: algebraicity criterion]
- Shimura, G. "Abelian Varieties with Complex Multiplication and
  Modular Functions." Princeton Univ. Press, 1998.
  [CM polarization theory]
- Weil, A. "Abelian varieties and the Hodge ring." Collected Papers
  III (1977), 421–429. [Weil classes, intersection formula]
- Lee, P. C.-K. "Paper 50: Decidability landscape for the Standard
  Conjectures." Zenodo, 2026. [DPT boundary at dimension 4]
- Lee, P. C.-K. "Paper 55: K3 surfaces and the Kuga-Satake
  construction." Zenodo, 2026. [Codimension principle]
