# Paper 59: De Rham Decidability — The p-adic Precision Bound

## Proof Strategy Document for Lean 4 Agent

**Series:** Constructive Reverse Mathematics and Arithmetic Geometry
**Depends on:** Paper 50 (DPT axioms), Paper 51 (BSD calibration, exceptional zero)
**Target:** ~500–700 lines Lean 4, ≤ 1 sorry (bridge axiom)
**Date:** 2026-02-21

---

## 1. THEOREM STATEMENTS (ENGLISH)

**Theorem A (p-adic Precision Bound).** Let E/ℚ be an elliptic curve with good reduction at a prime p. Let V = V_p(E) be the p-adic Galois representation, and let D_cris(V) be the associated crystalline filtered φ-module (2-dimensional over ℚ_p). Let a_p = Tr(φ) be the trace of Frobenius, so the characteristic polynomial of φ is T² - a_p·T + p.

The precision bound for BISH-decidable p-adic verification is:

    N_M = v_p(det(1 - φ)) = v_p(1 - a_p + p)

where v_p is the p-adic valuation. To verify x = 0 in D_cris(V) to precision k, it suffices to compute modulo p^{k + N_M}.

**Theorem B (Ordinary Case).** If E has good ordinary reduction at p, then v_p(a_p) = 0, and:

    det(1 - φ) = 1 - a_p + p

Since a_p is a p-adic unit (v_p(a_p) = 0) and p has valuation 1:
- If 1 - a_p ≢ 0 mod p: N_M = 0 (no precision loss)
- If 1 - a_p ≡ 0 mod p: N_M = v_p(1 - a_p + p) ≥ 1

**Theorem C (Supersingular Case).** If E has good supersingular reduction at p, then v_p(a_p) ≥ 1 (and a_p = 0 if p ≥ 5). For a_p = 0:

    det(1 - φ) = 1 + p

and N_M = v_p(1 + p). For p ≥ 3, N_M = 0 (since 1 + p is a p-adic unit). For p = 2, N_M = v_2(3) = 0 also.

So for supersingular primes with a_p = 0: **N_M = 0, no precision loss at all.**

**Theorem D (Verification Table).** For specific elliptic curves and primes:

| Curve | p | a_p | det(1-φ) | N_M | Reduction |
|-------|---|-----|----------|-----|-----------|
| X₀(11) | 2 | -2 | 1-(-2)+2 = 5 | 0 | good |
| X₀(11) | 3 | -1 | 1-(-1)+3 = 5 | 0 | good |
| X₀(11) | 5 | 1 | 1-1+5 = 5 | 1 | good ordinary |
| X₀(11) | 7 | -2 | 1-(-2)+7 = 10 | 0 | good |
| X₀(11) | 13 | 4 | 1-4+13 = 10 | 0 | good |
| X₀(11) | 19 | 0 | 1-0+19 = 20 | 0 | good supersingular |
| X₀(11) | 23 | -1 | 1-(-1)+23 = 25 | 0 | good |
| X₀(14) | 3 | -2 | 1-(-2)+3 = 6 | 0 | good |
| X₀(14) | 5 | -1 | 1-(-1)+5 = 7 | 0 | good |
| X₀(15) | 2 | -1 | 1-(-1)+2 = 4 | 2 | good ordinary |
| X₀(15) | 7 | 1 | 1-1+7 = 7 | 1 | good ordinary |
| 37a | 2 | -2 | 1-(-2)+2 = 5 | 0 | good |
| 37a | 3 | -3 | 1-(-3)+3 = 7 | 0 | good |
| 37a | 5 | -2 | 1-(-2)+5 = 8 | 0 | good |

**Theorem E (Semistable Extension — MTT Exceptional Zero).** For E/ℚ with split multiplicative reduction at p (Tate curve), the crystalline module D_cris(V) does not exist. Instead, D_st(V) is a 2-dimensional filtered (φ, N)-module with N ≠ 0.

The precision bound uses the Tate parameter q_E:

    N_M^{st} = v_p(q_E)

which is computable from the j-invariant: v_p(q_E) = -v_p(j(E)) when v_p(j(E)) < 0.

For E = X₀(11) at p = 11 (split multiplicative):
- j(E) = -122023936/161051 = -2^12·3·11^{-5}·... (need exact computation)
- Actually: the Tate parameter for X₀(11) at p = 11 has v_{11}(q_E) that needs explicit computation from the minimal model.

The Lean AI should compute this from the minimal Weierstrass model.

---

## 2. MATHEMATICAL BACKGROUND

### 2.1 The DPT Framework Recap

Paper 50 established three axioms for decidability of numerical equivalence. Axiom 3 (Archimedean polarization) provides BISH-decidability at the infinite place via positive-definiteness (u(ℝ) = 1).

At finite primes, u(ℚ_p) = 4 blocks positive-definiteness. The replacement is:

**De Rham descent** (Faltings/Tsuji → Berger → Colmez-Fontaine):
1. V is de Rham (automatic for geometric representations)
2. V is potentially semistable (Berger's equivalence)
3. D_pst(V) is weakly admissible (Colmez-Fontaine)
4. Weak admissibility provides the precision bound N_M

### 2.2 The Precision Bound Mechanism

For a crystalline representation V with D = D_cris(V):
- The Bloch-Kato finite cohomology H¹_f(ℚ_p, V) is computed via:
  0 → H⁰(ℚ_p, V) → D_cris(V) → D_cris(V) ⊕ D_dR(V)/Fil⁰ → H¹_f → 0
- The key operator is (1-φ): D_cris(V) → D_cris(V)
- Inverting (1-φ) loses precision v_p(det(1-φ))
- Weak admissibility guarantees det(1-φ) ≠ 0 and bounds its valuation

### 2.3 The Characteristic Polynomial

For an elliptic curve E/ℚ with good reduction at p:
- D_cris(V) is 2-dimensional
- char(φ) = T² - a_p T + p (Weil conjecture)
- det(1-φ) = (1-α)(1-β) = 1 - (α+β) + αβ = 1 - a_p + p
- The Hasse bound |a_p| ≤ 2√p ensures the roots have specific valuation structure

### 2.4 Known a_p Values

The Lean AI should hardcode a_p values from LMFDB or standard tables. For X₀(11) (Cremona label "11a1", conductor 11):
- a₂ = -2, a₃ = -1, a₅ = 1, a₇ = -2, a₁₃ = 4, a₁₇ = -2, a₁₉ = 0, a₂₃ = -1

These are well-known and can be verified independently.

---

## 3. LEAN MODULE STRUCTURE

### Module 1: `Defs.lean` (~80 lines)

```lean
-- Defs.lean

/-- An elliptic curve over ℚ, represented by minimal Weierstrass data -/
structure EllipticCurveData where
  label : String       -- Cremona label
  conductor : ℕ
  conductor_pos : conductor > 0

/-- Good reduction data at a prime p -/
structure GoodReductionData where
  curve : EllipticCurveData
  p : ℕ
  p_prime : Nat.Prime p
  a_p : ℤ              -- trace of Frobenius
  hasse_bound : a_p.natAbs ^ 2 ≤ 4 * p  -- |a_p| ≤ 2√p (squared form)

/-- The characteristic polynomial det(T - φ) evaluated at T = 1 -/
def det_one_minus_frob (d : GoodReductionData) : ℤ :=
  1 - d.a_p + d.p

/-- The p-adic precision bound N_M -/
-- For computational purposes, we compute v_p(det(1-φ)) directly
-- v_p(n) for a nonzero integer n and prime p

def padic_val (p : ℕ) (n : ℤ) : ℕ :=
  -- Standard p-adic valuation
  if n = 0 then 0  -- convention; det(1-φ) ≠ 0 by weak admissibility
  else Nat.find (fun k => ¬ (p^(k+1) : ℤ) ∣ n)  -- or explicit implementation

/-- The precision bound -/
def precision_bound (d : GoodReductionData) : ℕ :=
  padic_val d.p (det_one_minus_frob d)
```

### Module 2: `PadicVal.lean` (~120 lines)

Explicit p-adic valuation computation on integers.

```lean
-- PadicVal.lean

/-- p-adic valuation of a nonzero integer -/
-- Implementation: repeatedly divide by p, count successes

/-- v_p(n) for specific small cases, verified by native_decide -/

theorem v5_of_5 : multiplicity 5 (5 : ℤ) = 1 := by native_decide
-- Or use padicValInt from Mathlib if available

/-- Key computation: det(1-φ) for X₀(11) at p=5 -/
-- a_5 = 1, det = 1 - 1 + 5 = 5, v_5(5) = 1
theorem X0_11_p5_det : (1 : ℤ) - 1 + 5 = 5 := by norm_num
theorem X0_11_p5_bound : -- v_5(5) = 1, so N_M = 1
  ∃ (k : ℕ), k = 1 ∧ (5 : ℤ)^k ∣ 5 ∧ ¬ (5 : ℤ)^(k+1) ∣ 5 := by
  exact ⟨1, rfl, ⟨1, by ring⟩, by omega⟩

/-- For X₀(11) at p=2: a_2 = -2, det = 1-(-2)+2 = 5, v_2(5) = 0 -/
theorem X0_11_p2_det : (1 : ℤ) - (-2) + 2 = 5 := by norm_num
theorem X0_11_p2_bound : ¬ (2 : ℤ) ∣ 5 := by omega
-- N_M = 0

/-- For X₀(11) at p=3: a_3 = -1, det = 1-(-1)+3 = 5, v_3(5) = 0 -/
theorem X0_11_p3_det : (1 : ℤ) - (-1) + 3 = 5 := by norm_num
theorem X0_11_p3_bound : ¬ (3 : ℤ) ∣ 5 := by omega

/-- For X₀(11) at p=19 (supersingular): a_19 = 0, det = 1+19 = 20, v_19(20) = 0 -/
theorem X0_11_p19_det : (1 : ℤ) - 0 + 19 = 20 := by norm_num
theorem X0_11_p19_bound : ¬ (19 : ℤ) ∣ 20 := by omega
```

### Module 3: `VerificationTable.lean` (~200 lines)

Systematic verification for multiple curves and primes.

```lean
-- VerificationTable.lean

/-- A verified precision bound entry -/
structure VerifiedBound where
  label : String
  p : ℕ
  a_p : ℤ
  det_val : ℤ           -- det(1-φ)
  N_M : ℕ               -- v_p(det(1-φ))
  det_eq : (1 : ℤ) - a_p + p = det_val
  bound_correct : -- N_M is the exact p-adic valuation
    (if N_M = 0 then ¬ (p : ℤ) ∣ det_val
     else (p : ℤ)^N_M ∣ det_val ∧ ¬ (p : ℤ)^(N_M + 1) ∣ det_val)

/-- X₀(11) verification -/
def X0_11_at_2 : VerifiedBound := {
  label := "11a1", p := 2, a_p := -2, det_val := 5, N_M := 0,
  det_eq := by norm_num,
  bound_correct := by simp; omega
}

def X0_11_at_3 : VerifiedBound := {
  label := "11a1", p := 3, a_p := -1, det_val := 5, N_M := 0,
  det_eq := by norm_num,
  bound_correct := by simp; omega
}

def X0_11_at_5 : VerifiedBound := {
  label := "11a1", p := 5, a_p := 1, det_val := 5, N_M := 1,
  det_eq := by norm_num,
  bound_correct := by simp; exact ⟨⟨1, by ring⟩, by omega⟩
}

def X0_11_at_7 : VerifiedBound := {
  label := "11a1", p := 7, a_p := -2, det_val := 10, N_M := 0,
  det_eq := by norm_num,
  bound_correct := by simp; omega
}

def X0_11_at_13 : VerifiedBound := {
  label := "11a1", p := 13, a_p := 4, det_val := 10, N_M := 0,
  det_eq := by norm_num,
  bound_correct := by simp; omega
}

def X0_11_at_19 : VerifiedBound := {
  label := "11a1", p := 19, a_p := 0, det_val := 20, N_M := 0,
  det_eq := by norm_num,
  bound_correct := by simp; omega
}

-- The Lean AI should extend this table to:
-- X₀(14) (conductor 14, "14a1"): a₃ = -2, a₅ = -1
-- X₀(15) (conductor 15, "15a1"): a₂ = -1, a₇ = 1
-- 37a (conductor 37, "37a1"): a₂ = -2, a₃ = -3, a₅ = -2
-- Additional curves from LMFDB

-- TARGET: At least 20 verified entries across ≥ 4 curves and ≥ 5 primes each.
```

### Module 4: `WeakAdmissibility.lean` (~100 lines)

The abstract theorem: weak admissibility implies N_M is bounded.

```lean
-- WeakAdmissibility.lean

/-- For a 2-dimensional crystalline representation with Hodge-Tate
    weights 0 and 1 (elliptic curve), weak admissibility means:
    - t_N(D) = v_p(det φ) = v_p(p) = 1 = t_H(D)  (equality for full module)
    - For any 1-dim sub D': t_H(D') ≤ t_N(D')

    The eigenvalues α, β of φ satisfy αβ = p and α + β = a_p.
    
    Ordinary: v_p(α) = 0, v_p(β) = 1
    Supersingular: v_p(α) = v_p(β) = 1/2 (in an extension)
    
    In both cases, det(1-φ) = (1-α)(1-β) = 1 - a_p + p.
    
    Weak admissibility guarantees 1 - a_p + p ≠ 0.
    (This is the number of F_p-rational points of the reduction!)
    Actually: 1 - a_p + p = #E(F_p), which is always ≥ 1.
-/

/-- #E(F_p) = 1 - a_p + p is always positive (Hasse bound) -/
theorem hasse_implies_positive (p : ℕ) (a_p : ℤ) 
    (hp : p ≥ 2) (hasse : a_p ^ 2 ≤ 4 * p) :
    1 - a_p + (p : ℤ) > 0 := by
  -- From |a_p| ≤ 2√p and p ≥ 2:
  -- 1 - a_p + p ≥ 1 - 2√p + p = (1 - √p)² ≥ 0
  -- Actually for p ≥ 2: 1 - a_p + p ≥ 1 - 2√p + p > 0
  -- since (√p - 1)² > 0 for p ≥ 2.
  -- The Lean proof needs: a_p ≤ 2√p ≤ p (for p ≥ 4), handle p=2,3 separately
  sorry -- The Lean AI should close this; it's elementary from Hasse bound

/-- Therefore N_M = v_p(#E(F_p)) is always well-defined -/
-- This is a beautiful observation: the precision bound is the 
-- p-adic valuation of the number of rational points!

/-- The precision bound is bounded by the Hasse bound:
    #E(F_p) ≤ 1 + 2√p + p = (1 + √p)²
    So N_M = v_p(#E(F_p)) ≤ v_p((1+√p)²) 
    For practical purposes: N_M ≤ 2 for p ≥ 5 (since #E(F_p) ≤ (1+√p)² < p³)
-/
```

### Module 5: `Interpretation.lean` (~80 lines)

The CRM interpretation connecting to Paper 50/51.

```lean
-- Interpretation.lean

/-!
# CRM Interpretation: Axiom 5 is a Theorem

## The Three + One Axiom Structure

Paper 50 established three axioms for decidability of numerical equivalence:
- Axiom 1: Decidable morphisms (linear algebra, unconditional)
- Axiom 2: Integrality (algebraic integers, unconditional)  
- Axiom 3: Archimedean polarization (positive-definiteness, u(ℝ)=1)

The "Axiom 5" (de Rham decidability) completes the picture at finite primes:
- For geometric representations, de Rham is automatic (Faltings/Tsuji)
- Berger: de Rham ⟺ potentially semistable (uniform descent)
- Colmez-Fontaine: weakly admissible (precision bound exists)

Therefore: Axiom 5 is a THEOREM for motives, not an independent axiom.

## The Precision Bound N_M

The p-adic precision bound N_M = v_p(det(1-φ)) has a beautiful
arithmetic interpretation:

    N_M = v_p(#E(𝔽_p))

The precision lost in p-adic verification is exactly the p-adic 
valuation of the number of rational points on the reduction.

When #E(𝔽_p) is coprime to p (the "generic" case): N_M = 0, 
no precision loss at all.

When p | #E(𝔽_p) (anomalous primes): N_M ≥ 1, precision loss 
occurs. This is exactly when the p-adic BSD exceptional zero 
phenomenon manifests (Paper 51).

## Connection to Paper 51

Paper 51 identified the exceptional zero as the p-adic avatar of 
the u-invariant obstruction. Paper 60 quantifies this:
- N_M = 0: standard decidability, no anomaly
- N_M ≥ 1: precision loss = the "exceptional" extra computation
- The L-invariant ℒ_p compensates for this precision loss

The exceptional zero is not a failure of decidability — it's a 
quantified precision cost, bounded by N_M.
-/
```

### Module 6: `Main.lean` (~30 lines)

Assembly.

```lean
-- Main.lean

import P60_DeRham.Defs
import P60_DeRham.PadicVal
import P60_DeRham.VerificationTable
import P60_DeRham.WeakAdmissibility
import P60_DeRham.Interpretation

/-!
# Paper 60: De Rham Decidability — The p-adic Precision Bound

For elliptic curves with good reduction at p:
  N_M = v_p(1 - a_p + p) = v_p(#E(𝔽_p))

Verified for X₀(11), X₀(14), X₀(15), 37a across multiple primes.

"Axiom 5" is a theorem for geometric representations:
  de Rham (Faltings) → pot. semistable (Berger) → 
  weakly admissible (Colmez-Fontaine) → N_M computable.
-/
```

---

## 4. SORRY BUDGET

**Target: 0–1 sorry.**

| # | Location | Statement | Strategy |
|---|----------|-----------|----------|
| 1 | `WeakAdmissibility.lean` | `hasse_implies_positive` | TRY TO CLOSE by `omega` after case-split on small p, or by algebraic manipulation of Hasse bound. Should be ≤ 20 lines. |

**Bridge axioms (not counted):**
- The identification D_cris(V) with a 2-dim ℚ_p-vector space whose φ has char poly T² - a_p T + p (from p-adic Hodge theory)
- The connection between det(1-φ) and the precision loss in inverting (1-φ) (linear algebra over a DVR)

**Realistic: 0 sorries on computational content, 0–1 on the Hasse positivity lemma.**

---

## 5. KEY OBSERVATIONS FOR THE LEAN AI

1. **det(1-φ) = #E(𝔽_p).** This is the beautiful coincidence: the precision bound equals the p-adic valuation of the point count. The Lean AI should state this as an explicit theorem.

2. **All computations are integer arithmetic.** a_p is an integer, p is an integer, 1 - a_p + p is an integer. The p-adic valuation of an integer is computed by trial division. No p-adic analysis or period rings appear in the formalization — only their consequences for integers.

3. **The Hasse bound |a_p| ≤ 2√p in squared form is a_p² ≤ 4p.** This avoids irrational numbers in Lean.

4. **Extend the table aggressively.** 20+ entries is the target. Use curves of small conductor (11, 14, 15, 17, 19, 20, 21, 24, 26, 27, 30, 32, 33, 34, 36, 37, 38, 39, 40, ...) at primes of good reduction. The a_p values are standard and can be hardcoded.

5. **Anomalous primes are the interesting cases.** When p | #E(𝔽_p), N_M ≥ 1. These are rare but important. For X₀(11): p = 5 gives #E(𝔽₅) = 5, so N_M = 1. Find more anomalous examples across the curve table.

---

## 6. EXPECTED OUTPUT

```
lake build
-- Build succeeded, 0 errors

-- Key results:
-- ✓ X0_11_at_5: det(1-φ) = 5, N_M = 1 (anomalous)
-- ✓ X0_11_at_2: det(1-φ) = 5, N_M = 0
-- ✓ X0_11_at_3: det(1-φ) = 5, N_M = 0
-- ✓ X0_11_at_7: det(1-φ) = 10, N_M = 0
-- ✓ X0_11_at_13: det(1-φ) = 10, N_M = 0
-- ✓ X0_11_at_19: det(1-φ) = 20, N_M = 0 (supersingular)
-- ✓ [14+ additional entries]
-- ✓ hasse_implies_positive: #E(𝔽_p) > 0
-- ✓ N_M = v_p(#E(𝔽_p)) interpretation theorem
```

