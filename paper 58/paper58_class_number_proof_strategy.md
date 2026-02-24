# Paper 58: Class Number Correction — Exotic Weil Classes on CM Fourfolds with h_K > 1

## Proof Strategy Document for Lean 4 Agent

**Series:** Constructive Reverse Mathematics and Arithmetic Geometry
**Depends on:** Paper 56 (Gram matrix derivation, h = f for h_K = 1), Paper 57 (nine class-number-1 verifications)
**Target:** ~700–900 lines Lean 4, ≤ 2 sorries (principled bridge axioms)
**Date:** 2026-02-21

---

## 1. THEOREM STATEMENTS (ENGLISH)

Papers 56–57 proved: for h_K = 1, the exotic Weil class w₀ on a CM abelian fourfold has Hermitian self-intersection h = f (the conductor of the cyclic Galois totally real cubic F), equivalently h² = disc(F).

Paper 58 extends this to class number h_K > 1.

**Theorem A (Corrected Self-Intersection Formula).** Let K = ℚ(√-d) be a quadratic imaginary field (h_K arbitrary). Let F be a cyclic Galois totally real cubic with disc(F) = f² (conductor f). Let E = F·K, A a CM abelian 3-fold with CM type (E, Φ₀), B a CM elliptic curve with CM by O_K, and X = A × B.

The Weil lattice W_int = W(A,B) ∩ H⁴(X, ℤ) is a projective O_K-module of rank 1, isomorphic to a fractional ideal 𝔞 of O_K. The rational Hermitian self-intersection is:

    h = f / Nm(𝔞)

The true invariant is the product:

    h · Nm(𝔞) = f

For h_K = 1, Nm(𝔞) = 1 and h = f, recovering Papers 56–57.

**Theorem B (Gram Matrix Determinant).** The Gram matrix of the real intersection pairing B(x,y) = Tr_{K/ℚ} H(x,y) on an integral ℤ-basis {α·w₀, β·w₀} of W_int = 𝔞·w₀ satisfies:

    det(G) = h² · Nm(𝔞)² · |Δ_K| = f² · |Δ_K|

The topological volume f² · |Δ_K| is an absolute geometric invariant independent of h_K.

**Theorem C (Steinitz Class Determination).** The Steinitz class [𝔞] ∈ Cl(K) is NOT a free parameter. It is uniquely determined by the norm condition: h = f/Nm(𝔞) must lie in Nm(K×) (the set of rational numbers representable as norms from K). The class group acts as an arithmetic compensator resolving local norm obstructions.

Concretely: for each pair (K, f), the Steinitz class [𝔞] is the unique class such that f/Nm(𝔞) ∈ Nm(K×). This is a finite, decidable computation.

**Theorem D (Norm Obstruction Examples).** For K = ℚ(√-5), h_K = 2:
- f = 7: 7 ∉ Nm(K×) (x² + 5y² = 7 has no rational solution), so the lattice is forced into the non-trivial Steinitz class with Nm(𝔞) = 2, giving h = 7/2. Verified: (3/2)² + 5·(1/2)² = 7/2 ∈ Nm(K×). ✓
- f = 9: Check whether 9 ∈ Nm(K×). If yes, lattice is free. If no, lattice is non-free with h = 9/2.
- f = 13, 19, 37, 61, 79, 97, 163: Same analysis for each conductor.

---

## 2. MATHEMATICAL BACKGROUND

### 2.1 The Free Case (Papers 56–57, recap)

For h_K = 1:
- O_K is a PID, so W_int = O_K · w₀ (free)
- Integral basis: {w₀, ω·w₀} where O_K = ℤ ⊕ ℤω
- Gram matrix entries computed from h = H(w₀, w₀) via B = Tr_{K/ℚ} ∘ H
- det(G) = h² · |Δ_K|
- Combined with the geometric identity det(G) = f² · |Δ_K|, this gives h = f

### 2.2 The Projective Case (Paper 58, new)

For h_K > 1:
- W_int is a projective O_K-module of rank 1
- By Steinitz theorem: W_int ≅ 𝔞 for some fractional ideal 𝔞 of O_K
- Integral basis: {α·w₀, β·w₀} where {α, β} is a ℤ-basis of 𝔞
- Gram matrix:

    G₁₁ = B(αw₀, αw₀) = Tr(h·α·ᾱ) = 2h·Nm(α)
    G₂₂ = B(βw₀, βw₀) = Tr(h·β·β̄) = 2h·Nm(β)
    G₁₂ = B(αw₀, βw₀) = Tr(h·α·β̄) = h·(αβ̄ + ᾱβ)

- Determinant:

    det(G) = 4h²·Nm(α)·Nm(β) - h²·(αβ̄ + ᾱβ)²
           = -h²·(αβ̄ - ᾱβ)²
           = -h²·Nm(𝔞)²·Δ_K
           = h²·Nm(𝔞)²·|Δ_K|

  (using the fact that (αβ̄ - ᾱβ)² = Nm(𝔞)²·Δ_K for a ℤ-basis of 𝔞)

- Setting det(G) = f²·|Δ_K| gives h²·Nm(𝔞)² = f², hence h·Nm(𝔞) = f.

### 2.3 The Norm Obstruction

Schoen's algebraicity condition requires h ∈ Nm(K×) (the Hermitian self-intersection must be representable as a norm from K). The question: is f/Nm(𝔞) a norm in K×?

For K = ℚ(√-d), the norm form is Nm(a + b√-d) = a² + d·b². A positive rational r is a norm in K× iff r = a² + d·b² for some a, b ∈ ℚ.

**Key number-theoretic fact:** An integer n is representable as a² + d·b² (with a, b ∈ ℤ) iff certain congruence conditions hold. For representation over ℚ, the condition is weaker — n is a norm in K× iff n is locally a norm at every place (Hasse norm theorem).

For specific cases:
- K = ℚ(√-5), d = 5: n is a norm iff x² + 5y² = n has a rational solution.
  - n = 7: No. (Check: 7 ≡ 2 mod 5, and 2 is not a quadratic residue mod 5. By local conditions at p = 5, 7 is not a norm.) Actually, we need to be more careful — the local condition at p = 5 for x² + 5y² involves the Hilbert symbol. The math genius asserts 7 ∉ Nm(K×) and provides the verification (3/2)² + 5(1/2)² = 14/4 = 7/2 for the corrected h = 7/2. This needs to be verified.

**NOTE TO LEAN AI:** The norm representability checks (is n ∈ Nm(K×)?) can be done computationally for specific n and K. For K = ℚ(√-5), check whether x² + 5y² = n has a rational solution by searching over a finite set of denominators, or by checking local conditions at all primes dividing 5·n·∞.

### 2.4 Ring of Integers for K = ℚ(√-5)

Since -5 ≡ 3 (mod 4):
- O_K = ℤ[√-5]
- Δ_K = -4·5 = -20
- |Δ_K| = 20
- ω = √-5 (not (1+√-5)/2)
- Integral basis of O_K: {1, √-5}

Class group: Cl(K) = ℤ/2ℤ
Non-trivial ideal class: 𝔭 = (2, 1+√-5), Nm(𝔭) = 2
ℤ-basis of 𝔭: {2, 1+√-5}

---

## 3. LEAN MODULE STRUCTURE

### Module 1: `Defs.lean` (~120 lines)

Core definitions extending Papers 56–57.

```lean
-- Defs.lean

/-- A quadratic imaginary field K = ℚ(√-d) -/
structure QuadImagField where
  d : ℕ        -- d in ℚ(√-d), square-free
  d_pos : d > 0
  disc : ℤ     -- Δ_K
  abs_disc : ℕ -- |Δ_K|
  class_num : ℕ -- h_K
  disc_eq : disc = if d % 4 == 3 then -(4 * d : ℤ) else sorry
    -- Simplified: for d ≡ 3 mod 4, Δ_K = -4d
  abs_disc_eq : abs_disc = disc.natAbs

/-- A fractional ideal of O_K, represented by its ℤ-basis and norm -/
structure FractionalIdeal (K : QuadImagField) where
  /-- First basis element: α = a₁ + a₂√-d, stored as (a₁_num, a₁_den, a₂_num, a₂_den) -/
  α_re_num : ℤ
  α_re_den : ℕ  -- positive
  α_im_num : ℤ  -- coefficient of √-d
  α_im_den : ℕ  -- positive
  /-- Second basis element: β = b₁ + b₂√-d -/
  β_re_num : ℤ
  β_re_den : ℕ
  β_im_num : ℤ
  β_im_den : ℕ
  /-- Ideal norm Nm(𝔞) -/
  ideal_norm : ℕ
  ideal_norm_pos : ideal_norm > 0

/-- The trivial ideal O_K itself -/
def trivialIdeal (K : QuadImagField) : FractionalIdeal K where
  α_re_num := 1; α_re_den := 1; α_im_num := 0; α_im_den := 1
  β_re_num := 0; β_re_den := 1; β_im_num := 1; β_im_den := 1
  ideal_norm := 1; ideal_norm_pos := by norm_num

/-- For K = ℚ(√-5): the non-trivial ideal 𝔭 = (2, 1+√-5) -/
def ideal_p_sqrt5 : FractionalIdeal ⟨5, by norm_num, -20, 20, 2, by norm_num, by norm_num⟩ where
  α_re_num := 2; α_re_den := 1; α_im_num := 0; α_im_den := 1
  β_re_num := 1; β_re_den := 1; β_im_num := 1; β_im_den := 1
  ideal_norm := 2; ideal_norm_pos := by norm_num

/-- Totally real cubic field (reused from Papers 56–57) -/
structure TotallyRealCubic where
  a : ℤ
  b : ℤ
  c : ℤ
  disc : ℤ
  disc_pos : disc > 0
  disc_eq : disc = a^2 * b^2 - 4 * b^3 - 4 * a^3 * c + 18 * a * b * c - 27 * c^2
  conductor : ℕ  -- f, where disc = f²
  conductor_sq : disc = (conductor : ℤ)^2

/-- Weil lattice data for the h_K > 1 case -/
structure WeilLatticeData where
  K : QuadImagField
  F : TotallyRealCubic
  ideal : FractionalIdeal K
  /-- h = f / Nm(𝔞), stored as rational (h_num / h_den) -/
  h_num : ℤ
  h_den : ℕ
  h_den_pos : h_den > 0
  /-- The fundamental identity: h · Nm(𝔞) = f -/
  h_times_norm_eq_f : h_num * ideal.ideal_norm = F.conductor * h_den
```

### Module 2: `GramMatrix.lean` (~150 lines)

Gram matrix computation for projective O_K-modules.

```lean
-- GramMatrix.lean

/-- Compute the Gram matrix entries for W_int = 𝔞·w₀
    on integral basis {α·w₀, β·w₀} where {α, β} is a ℤ-basis of 𝔞.

    G₁₁ = 2h · Nm(α)
    G₂₂ = 2h · Nm(β)
    G₁₂ = h · (αβ̄ + ᾱβ) = h · Tr(αβ̄)

    All entries must be integers.
    
    We work with rational h = h_num/h_den and check integrality.
-/

/-- Norm of α = (a₁/d₁) + (a₂/d₂)√-d is a₁²/d₁² + d·a₂²/d₂² -/
-- Stored as a rational number (norm_num / norm_den)

/-- Gram matrix as a 2×2 integer matrix -/
def gramMatrix (data : WeilLatticeData) : Matrix (Fin 2) (Fin 2) ℤ :=
  -- Compute from the ideal basis and h
  -- Implementation details depend on exact rational arithmetic
  sorry -- Filled in per-instance below

/-- For K = ℚ(√-5), f = 7, 𝔞 = (2, 1+√-5):
    h = 7/2, α = 2, β = 1+√-5
    G₁₁ = 2·(7/2)·4 = 28
    G₂₂ = 2·(7/2)·6 = 42
    G₁₂ = (7/2)·(2(1-√-5) + 2(1+√-5)) = (7/2)·4 = 14
    G = [[28, 14], [14, 42]]
-/
def gram_K5_f7 : Matrix (Fin 2) (Fin 2) ℤ := !![28, 14; 14, 42]

/-- det(G) = 28·42 - 14² = 1176 - 196 = 980 -/
theorem gram_K5_f7_det : gram_K5_f7.det = 980 := by native_decide

/-- Expected: f² · |Δ_K| = 49 · 20 = 980 -/
theorem gram_K5_f7_volume : (7 : ℤ)^2 * 20 = 980 := by norm_num

/-- The determinant matches the topological volume -/
theorem gram_K5_f7_match : gram_K5_f7.det = (7 : ℤ)^2 * 20 := by
  rw [gram_K5_f7_det, gram_K5_f7_volume]
```

### Module 3: `NormObstruction.lean` (~200 lines)

The norm representability computations that force the Steinitz class.

```lean
-- NormObstruction.lean

/-- A positive rational r = p/q is a norm in K = ℚ(√-d) iff
    there exist a, b ∈ ℚ with a² + d·b² = p/q,
    equivalently: there exist integers x, y, z > 0 with x² + d·y² = (p/q)·z².
    
    For computational purposes, we check bounded representatives. -/

/-- 7 is NOT a norm in ℚ(√-5)×.
    Proof: x² + 5y² = 7z² has no integer solution with z > 0.
    Bounded check: for z = 1, x² + 5y² = 7.
      y = 0: x² = 7, no integer solution.
      y = 1: x² = 2, no integer solution.
      y ≥ 2: 5y² ≥ 20 > 7.
    For z = 2, x² + 5y² = 28.
      y = 0: x² = 28, no.
      y = 1: x² = 23, no.
      y = 2: x² = 8, no.
      y ≥ 3: 5y² ≥ 45 > 28.
    General argument: 7 is inert in ℤ[√-5] (since (-5/7) = (2/7) = 1,
    wait this needs Legendre symbol check).
    
    Actually: use that 7 ≡ 2 mod 5 and check the Hilbert symbol (7, -5)_p
    at p = 5. Or just verify computationally for small cases.
    
    SIMPLEST APPROACH: native_decide on a bounded search. -/

/-- 7 is not representable as x² + 5y² for x, y ∈ ℤ -/
theorem seven_not_norm_int : ¬ ∃ (x y : ℤ), x^2 + 5 * y^2 = 7 := by
  intro ⟨x, y, h⟩
  -- Bounded: |x| ≤ 2, |y| ≤ 1 suffice since x² ≤ 7 and 5y² ≤ 7
  omega  -- or interval_cases + omega

/-- 7 is not a norm in ℚ(√-5)× (rational version).
    If x² + 5y² = 7 · z² with x, y, z ∈ ℤ, z > 0, then
    reducing mod 5: x² ≡ 2z² mod 5.
    If z ≢ 0 mod 5: x²/z² ≡ 2 mod 5, but 2 is not a QR mod 5
    (squares mod 5 are {0, 1, 4}). So 5 | z, hence 5 | x, write
    x = 5x', z = 5z', then 25x'² + 5y² = 175z'², 5x'² + y² = 35z'².
    Then y² ≡ 0 mod 5, so 5 | y. Infinite descent. -/
theorem seven_not_norm_rational_K5 :
    ¬ ∃ (x y z : ℤ), z > 0 ∧ x^2 + 5 * y^2 = 7 * z^2 := by
  sorry -- SORRY 1: Infinite descent argument. 
         -- For Lean, try native_decide on bounded search,
         -- or formalize the mod-5 descent.

/-- 7/2 IS a norm in ℚ(√-5)×.
    Witness: (3/2)² + 5·(1/2)² = 9/4 + 5/4 = 14/4 = 7/2.
    Equivalently: 3² + 5·1² = 14 = 7·2, so x=3, y=1, z=2 gives
    x² + 5y² = 14 = (7/2)·z² = (7/2)·4. Wait, that's 14 = 14. ✓
    More precisely: 3² + 5·1² = 7·2, so x² + 5y² = 7·2·z² with z=1. -/
theorem seven_half_is_norm_K5 :
    ∃ (x y z : ℤ), z > 0 ∧ x^2 + 5 * y^2 = 7 * 2 * z^2 :=
  ⟨3, 1, 1, by norm_num, by norm_num⟩

/-- Therefore the Steinitz class must be non-trivial for f=7, K=ℚ(√-5):
    - If free (Nm(𝔞) = 1): h = 7, but 7 ∉ Nm(K×). Contradiction.
    - If non-free (Nm(𝔞) = 2): h = 7/2, and 7/2 ∈ Nm(K×). ✓ -/
theorem steinitz_forced_nontrivial_K5_f7 :
    -- 7 is not a norm (free case blocked)
    (¬ ∃ (x y z : ℤ), z > 0 ∧ x^2 + 5 * y^2 = 7 * z^2) ∧
    -- 7·2 IS a norm (non-free case works)
    (∃ (x y z : ℤ), z > 0 ∧ x^2 + 5 * y^2 = 7 * 2 * z^2) := by
  exact ⟨seven_not_norm_rational_K5, seven_half_is_norm_K5⟩
```

### Module 4: `ClassNumberExamples.lean` (~200 lines)

Systematic computation for K = ℚ(√-5) paired with multiple conductors from Papers 56–57.

```lean
-- ClassNumberExamples.lean

/-- For each conductor f from Papers 56–57, determine:
    1. Is f a norm in ℚ(√-5)×? (If yes: free lattice, h = f)
    2. Is f/2 a norm in ℚ(√-5)×? (If yes: non-free lattice, h = f/2)
    3. Compute the Gram matrix
    4. Verify det(G) = f² · 20 -/

-- Conductor f = 7 (done in Module 3)
-- Gram: [[28, 14], [14, 42]], det = 980 = 49·20 ✓

-- Conductor f = 9
-- Is 9 a norm? x² + 5y² = 9: x=2, y=1 gives 4+5=9. YES!
-- So lattice is FREE, h = 9.
-- Gram matrix on {w₀, √-5·w₀}:
--   G₁₁ = 2·9·1 = 18
--   G₂₂ = 2·9·5 = 90
--   G₁₂ = 9·Tr(√-5) = 9·0 = 0    (since Tr(√-5) = √-5 + (-√-5) = 0)
-- Wait: for K = ℚ(√-5), ω = √-5.
-- G₁₂ = h·Tr(1·(−√-5)) = 9·(−√-5 + √-5) = 0
-- G = [[18, 0], [0, 90]], det = 1620 = 81·20 ✓

def gram_K5_f9 : Matrix (Fin 2) (Fin 2) ℤ := !![18, 0; 0, 90]
theorem gram_K5_f9_det : gram_K5_f9.det = 1620 := by native_decide
theorem gram_K5_f9_match : gram_K5_f9.det = (9 : ℤ)^2 * 20 := by norm_num

-- Witness: 9 is a norm
theorem nine_is_norm_K5 : ∃ (x y : ℤ), x^2 + 5 * y^2 = 9 :=
  ⟨2, 1, by norm_num⟩

-- Conductor f = 13
-- Is 13 a norm? x² + 5y² = 13: check x=0..3, y=0..1
--   y=0: x²=13, no. y=1: x²=8, no. So 13 is NOT a norm (integer).
-- Rational norm: need x² + 5y² = 13z². Mod 5: x² ≡ 3z² mod 5.
--   QR mod 5: {0,1,4}. 3·z² mod 5: if z≢0: 3·{1,4} = {3,2}. Neither is a QR.
--   So 5|z, descent. 13 ∉ Nm(K×).
-- Is 13/2 a norm? x² + 5y² = 26z². z=1: x² + 5y² = 26.
--   y=0: x²=26, no. y=1: x²=21, no. y=2: x²=6, no.
-- z=1 failed. z arbitrary: mod 5, x² ≡ z² mod 5, so (x/z)² ≡ 1 mod 5. OK.
-- Actually: 1² + 5·1² = 6. 26/6 not integer. Try: x² + 5y² = 26.
--   Nope. But over Q: (1)² + 5(√(21/5))²... this needs careful checking.
-- 
-- THE LEAN AI SHOULD: for each f, do a bounded search for
-- (x, y, z) with z = 1..10 and x² + 5y² = f·z² (free case)
-- or x² + 5y² = f·2·z² (non-free case, Nm(𝔞)=2).
-- Report which case works.

-- IMPORTANT: The Lean AI should compute these systematically.
-- I provide the f=7 and f=9 cases as worked examples.
-- The Lean AI should extend to f = 13, 19, 37, 61, 79, 97, 163.

-- Conductor f = 19
-- Is 19 a norm? x² + 5y² = 19: y=0: x²=19, no. y=1: x²=14, no. 
--   y=2: x²=-1, no. So not an integer norm.
-- Rational: mod 5: x² ≡ 4z² mod 5, so (x/z)² ≡ 4 mod 5. 
--   4 IS a QR mod 5 (2²=4). So the local condition at 5 passes.
-- Need to check other local conditions. 
-- Try: x² + 5y² = 19z², z=1: no (checked). z=2: x² + 5y² = 76.
--   y=1: x²=71, no. y=2: x²=56, no. y=3: x²=31, no. y=4: x²=-4, no.
-- z=3: x² + 5y² = 171. y=1: x²=166, no. y=2: x²=151, no. ...
-- This is getting tedious. The Lean AI should automate this search.

-- FOR THE LEAN AI: The pattern is:
-- 1. For each conductor f from {7, 9, 13, 19, 37, 61, 79, 97, 163}:
-- 2. Search for (x, y, z) with 0 < z ≤ Z, |x| ≤ X, |y| ≤ Y such that:
--    (a) x² + 5y² = f·z²  (free case, Nm(𝔞) = 1)
--    (b) x² + 5y² = 2f·z²  (non-free case, Nm(𝔞) = 2)
-- 3. If (a) has a solution: lattice is free, h = f.
--    If (b) has a solution but (a) doesn't: lattice is non-free, h = f/2.
-- 4. Compute Gram matrix accordingly.
-- 5. Verify det(G) = f² · 20 by native_decide.
```

### Module 5: `Completeness.lean` (~100 lines)

Summary theorem and the universal identity h·Nm(𝔞) = f.

```lean
-- Completeness.lean

/-- Data for a verified h_K > 1 example -/
structure VerifiedExample where
  conductor : ℕ
  ideal_norm : ℕ  -- 1 (free) or 2 (non-free for h_K = 2)
  gram : Matrix (Fin 2) (Fin 2) ℤ
  det_eq : gram.det = (conductor : ℤ)^2 * 20
  norm_witness : Bool  -- true if lattice is free, false if non-free
  -- For free: ∃ x y, x² + 5y² = f
  -- For non-free: (¬ ∃ x y z, z > 0 ∧ x² + 5y² = f·z²) ∧ 
  --               (∃ x y z, z > 0 ∧ x² + 5y² = 2f·z²)

/-- The universal identity: for ALL examples, h · Nm(𝔞) = f -/
-- This follows from det(G) = f²·|Δ_K| and det(G) = h²·Nm(𝔞)²·|Δ_K|

/-- Summary: all nine conductors verified for K = ℚ(√-5) -/
-- theorem all_nine_K5_verified : ... (filled in after computation)
```

### Module 6: `Main.lean` (~50 lines)

Assembly and summary.

```lean
-- Main.lean

import P58_ClassNumber.Defs
import P58_ClassNumber.GramMatrix
import P58_ClassNumber.NormObstruction
import P58_ClassNumber.ClassNumberExamples
import P58_ClassNumber.Completeness

/-!
# Paper 58: Class Number Correction for Exotic Weil Classes

## Summary

Papers 56–57 proved h = f (conductor) for CM abelian fourfolds with h_K = 1.
Paper 58 extends to h_K > 1 with the corrected formula:

    h · Nm(𝔞) = f

where 𝔞 is the Steinitz class of the Weil lattice, forced by the norm
condition h = f/Nm(𝔞) ∈ Nm(K×).

First test field: K = ℚ(√-5), h_K = 2, |Δ_K| = 20.

Results:
- f = 7: lattice non-free (Nm(𝔞)=2), h = 7/2, G = [[28,14],[14,42]], det = 980 ✓
- f = 9: lattice free (Nm(𝔞)=1), h = 9, G = [[18,0],[0,90]], det = 1620 ✓
- f = 13, 19, ...: systematically computed

The topological volume det(G) = f²·|Δ_K| is an absolute invariant.
The class group determines how this volume distributes between h and Nm(𝔞).
-/
```

---

## 4. SORRY BUDGET

**Target: ≤ 2 sorries.**

| # | Location | Statement | Classification |
|---|----------|-----------|----------------|
| 1 | `NormObstruction.lean` | `seven_not_norm_rational_K5` — 7 ∉ Nm(ℚ(√-5)×) | **TRY TO CLOSE** by mod-5 descent formalized in Lean, or by bounded `native_decide`. The descent is: x²+5y²=7z², mod 5 gives x²≡2z², 2 is not QR mod 5, so 5∣z, then 5∣x, descent. Should be ~30 lines. |
| 2 | `Defs.lean` | `disc_eq` for general d | **Simplify**: only implement for d = 5 specifically, avoid general case. Then close by `norm_num`. |

**Bridge axioms (not counted as sorries):**
- The topological volume identity det(G) = f²·|Δ_K| (from Paper 56's geometric argument)
- Schoen's norm condition h ∈ Nm(K×) (from Schoen 1988, Theorem 0.2)

**Realistic sorry count: 0–1.**

---

## 5. FORMALIZATION NOTES

### 5.1 Tactic Expectations

- `native_decide` for all Gram matrix determinants (2×2, small entries)
- `norm_num` for arithmetic identities
- `omega` for integer inequalities in norm checks
- Bounded `decide` or `native_decide` for small norm representability searches

### 5.2 Key Difference from Papers 56–57

Papers 56–57 used 3×3 trace matrices from Newton's identities to compute disc(F). Paper 58 does NOT recompute disc(F) — it takes f as input from Papers 56–57 and computes the Gram matrix on the projective O_K-module. The trace matrix pipeline is not needed here.

The new computational content is:
1. Norm representability checks (is f a norm in K×?)
2. Gram matrix computation on non-standard integral bases
3. Determinant verification

### 5.3 Mathlib Dependencies

**Reused from Papers 56–57:**
- `Matrix`, `Matrix.det`, `Fin`, `!![...]` notation
- `native_decide`

**New (probably not needed from Mathlib, implement directly):**
- Norm form x² + dy² — just use integer arithmetic
- Ideal bases — represented as explicit integer vectors

**Explicitly NOT needed:**
- No algebraic number theory imports
- No class group theory from Mathlib
- No ideal theory from Mathlib
- Everything is explicit computation on specific integers

### 5.4 Extension Strategy

After K = ℚ(√-5) is verified, the framework extends to:
- K = ℚ(√-6), h_K = 2, |Δ_K| = 24
- K = ℚ(√-10), h_K = 2, |Δ_K| = 40
- K = ℚ(√-13), h_K = 2, |Δ_K| = 52
- K = ℚ(√-15), h_K = 2, |Δ_K| = 60

Each requires:
1. Compute O_K and Δ_K
2. Identify the non-trivial ideal class and its norm
3. For each conductor f: check norm condition, determine Steinitz class
4. Compute Gram matrix, verify determinant

The pipeline is identical — only the constants change. The Lean AI should parameterize by (d, Nm(𝔞)) so extending to new K is a matter of instantiation.

---

## 6. RELATIONSHIP TO PAPERS 56–57

**Paper 56:** Derived h² = disc(F) for h_K = 1 via Gram matrix algebra. The derivation used freeness of the Weil lattice over O_K.

**Paper 57:** Verified all nine class-number-1 fields. These are now the h_K = 1 base cases.

**Paper 58 (this paper):** Extends to h_K > 1 with the corrected formula h·Nm(𝔞) = f. The topological volume f²·|Δ_K| is invariant; the class group redistributes it between h and Nm(𝔞). The norm obstruction forces the Steinitz class, making the class group determination a decidable computation — consistent with the CRM programme's thesis.

**The CRM observation:** The class group enters the formula through a decidability condition (is f a norm in K×?). This is a finite, constructive computation — it doesn't require LPO or MP. The class number correction is itself decidable in BISH. This means the DPT framework extends cleanly to h_K > 1: the three axioms still work, with Axiom 3 (positive-definiteness) now operating on the projective lattice rather than the free lattice.

---

## 7. EXPECTED OUTPUT

```
lake build
-- Build succeeded, 0 errors, 0 warnings

-- Key results:
-- ✓ gram_K5_f7_det : det(G) = 980 (native_decide)
-- ✓ gram_K5_f7_match : 980 = 49 · 20 (norm_num)
-- ✓ gram_K5_f9_det : det(G) = 1620 (native_decide)
-- ✓ gram_K5_f9_match : 1620 = 81 · 20 (norm_num)
-- ✓ nine_is_norm_K5 : ∃ x y, x² + 5y² = 9 (witness: 2, 1)
-- ✓ seven_not_norm_rational_K5 : 7 ∉ Nm(K×) (descent)
-- ✓ seven_half_is_norm_K5 : 7/2 ∈ Nm(K×) (witness: 3, 1, 1)
-- ✓ steinitz_forced_nontrivial_K5_f7 : norm obstruction forces non-free lattice
-- ✓ [additional conductors f = 13, 19, 37, 61, 79, 97, 163]
```
