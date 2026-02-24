# Paper 48: Birch and Swinnerton-Dyer Conjecture — Lean 4 Formalization Specification

## Constructive Calibration of the BSD Conjecture

**Target:** Formalize the constructive reverse mathematics calibration of
the BSD Conjecture, proving that:
- B1: Deciding L(E,1) = 0 (analytic rank) requires LPO over ℝ
- B2: The Néron-Tate height is a positive-definite Archimedean polarization
- B3: The regulator is computable given generators (BISH)
- B4: Contrast with p-adic BSD (Mazur-Tate-Teitelbaum): u(ℚ_p) = 4
      blocks positive-definiteness, creating exceptional zero pathology

**Dependencies:** Mathlib4 (InnerProductSpace, real analysis), Paper 45 (LPO, u-invariant)

---

## 1. Mathematical Context

### 1.1 The BSD Conjecture

For an elliptic curve E/ℚ:
(a) ord_{s=1} L(E,s) = rank E(ℚ)
(b) The leading coefficient involves |Ш|, Ω_E, Reg_E, ∏c_p, |E(ℚ)_tors|²

### 1.2 Constructive Content

**Analytic side (LPO + MP):** L(E,1) is a computable real number.
Deciding L(E,1) = 0 is zero-testing a real Cauchy sequence (LPO).
Finding the order of vanishing requires testing successive derivatives
(LPO each) and searching for the first nonzero one (MP).

**Algebraic side (BISH + MP):** E(ℚ) is finitely generated. Points
have rational coordinates. The Néron-Tate height ĥ(P) provides a
positive-definite pairing on E(ℚ) ⊗ ℝ. The regulator Reg_E = det(⟨Pᵢ,Pⱼ⟩)
is computable from generators. Finding generators requires search (MP).

**Key insight:** BSD is the ARCHIMEDEAN counterpart of WMC/Tate/FM.
The Néron-Tate height IS the Archimedean polarization that the
finite-prime conjectures lack. u(ℝ) = 1 means positive-definiteness
is available.

---

## 2. File Structure

```
P48_BSD/
├── Defs.lean              -- Core definitions
├── B1_AnalyticLPO.lean    -- L(E,1) = 0 requires LPO
├── B2_Polarization.lean   -- Néron-Tate as Archimedean polarization
├── B3_Regulator.lean      -- Regulator computability in BISH
├── B4_PadicContrast.lean  -- p-adic BSD failure (u = 4)
├── Main.lean              -- Assembly
└── lakefile.lean
```

---

## 3. Definitions (Defs.lean)

```lean
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.Determinant

universe u

-- LPO for ℝ
def LPO_R : Prop := ∀ (x : ℝ), x = 0 ∨ x ≠ 0

-- The L-function value at s = 1 (axiomatized as a computable real)
axiom L_value : ℝ  -- L(E, 1)
axiom L_computable : ∃ (f : ℕ → ℚ), ∀ (ε : ℚ), ε > 0 →
  ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → |↑(f n) - L_value| < ε
  -- L(E,1) is a computable real number (has a computable Cauchy sequence)

-- Successive derivatives (for order of vanishing)
axiom L_deriv : ℕ → ℝ  -- L^(k)(E, 1)

-- The Mordell-Weil group (finitely generated abelian group)
-- Simplified: free part is a ℤ-module of rank r
variable (r : ℕ)  -- the algebraic rank

-- Generators of the free part
axiom MW_generators : Fin r → Type  -- P₁, ..., P_r
axiom MW_rational : ∀ (i : Fin r), ℚ × ℚ  -- rational coordinates

-- Néron-Tate height pairing
axiom neron_tate : Fin r → Fin r → ℝ  -- ⟨Pᵢ, Pⱼ⟩

-- Positive-definiteness of the Néron-Tate pairing
axiom neron_tate_pos_def :
  ∀ (v : Fin r → ℝ), v ≠ 0 →
    ∑ i, ∑ j, v i * neron_tate i j * v j > 0

-- The regulator
def regulator : ℝ := Matrix.det (Matrix.of neron_tate)

-- p-adic height (for contrast)
axiom Q_p : Type
axiom Q_p_field : Field Q_p
axiom padic_height : Fin r → Fin r → Q_p
```

---

## 4. B1: Analytic Rank Requires LPO (B1_AnalyticLPO.lean)

### 4.1 Statement

```lean
-- Deciding L(E,1) = 0 requires LPO over ℝ
theorem L_value_zero_requires_LPO :
  Decidable (L_value = 0) → LPO_R := by
  sorry

-- More precisely: deciding the order of vanishing requires LPO + MP
-- For each derivative, testing L^(k)(E,1) = 0 requires LPO
theorem analytic_rank_requires_LPO :
  (∀ (k : ℕ), Decidable (L_deriv k = 0)) → LPO_R := by
  sorry

-- LPO suffices for each individual zero-test
theorem LPO_decides_L_zero :
  LPO_R → Decidable (L_value = 0) := by
  sorry
```

### 4.2 Proof Strategy

**B1 (→):** L_value is a specific real number (a Cauchy sequence).
For any real number a, we can construct (in principle) an elliptic
curve E_a such that L(E_a, 1) = a. More cleanly: axiomatize that
the map from ℝ to "L-values" is surjective onto a dense subset,
or simply encode: for any a : ℝ, deciding "a = 0" is equivalent
to LPO_R, and L_value is a specific real number, so deciding
L_value = 0 is an instance of this.

The cleanest approach: LPO_R is equivalent to "every real number
is zero or nonzero." Deciding L_value = 0 is a special case.
To get the converse (this special case implies the general),
we need an encoding axiom that any real number can be realized
as an L-value. Alternatively, formalize the simpler:

  (∀ x : ℝ, Decidable (x = 0)) ↔ LPO_R

which is definitional, and note that L_value : ℝ is an instance.

**B1 (←):** LPO_R directly gives Decidable (L_value = 0) since
L_value : ℝ.

---

## 5. B2: Néron-Tate as Archimedean Polarization (B2_Polarization.lean)

### 5.1 Statement

```lean
-- The Néron-Tate pairing defines an inner product space
-- This is the Archimedean polarization (u(ℝ) = 1)

-- Construct the inner product space on ℝ^r from neron_tate
noncomputable def MW_inner_product : InnerProductSpace ℝ (EuclideanSpace ℝ (Fin r)) :=
  sorry -- Construct from neron_tate matrix using pos-def assumption

-- The key theorem: positive-definiteness is AVAILABLE over ℝ
-- (contrast with p-adic case in B4)
theorem archimedean_polarization_exists :
  ∃ (ip : InnerProductSpace ℝ (EuclideanSpace ℝ (Fin r))),
    ∀ (v : EuclideanSpace ℝ (Fin r)), v ≠ 0 → @inner ℝ _ ip.toInner v v > 0 := by
  sorry -- From neron_tate_pos_def

-- Consequence: non-torsion points are detectable without LPO
-- (ĥ(P) > 0 is semi-decidable: open condition, can be verified to any precision)
theorem height_positive_semidecidable :
  ∀ (i : Fin r), ∃ (ε : ℚ), ε > 0 ∧ neron_tate i i > ε := by
  sorry -- Follows from positive-definiteness on basis vectors
```

### 5.2 Proof Strategy

Construct the inner product from the Néron-Tate matrix using Mathlib's
`InnerProductSpace` infrastructure. The positive-definiteness axiom
`neron_tate_pos_def` provides the key property. The construction is:

1. Define bilinear form B(v,w) = ∑ᵢⱼ vᵢ · neron_tate i j · wⱼ
2. Show B is symmetric (neron_tate is symmetric — add axiom)
3. Show B is positive-definite (from neron_tate_pos_def)
4. Mathlib's `InnerProductSpace.ofBilinearForm` or similar

The semi-decidability result (height_positive_semidecidable) follows
because for basis vectors eᵢ, ⟨eᵢ, eᵢ⟩ = neron_tate i i > 0 by
positive-definiteness. Being strictly positive, it exceeds some
rational ε > 0, which can be found by computation.

---

## 6. B3: Regulator Computability (B3_Regulator.lean)

### 6.1 Statement

```lean
-- Given generators, the regulator is computable
-- (it's a determinant of a matrix of real inner products)

-- The regulator is strictly positive (consequence of positive-definiteness)
theorem regulator_positive : regulator > 0 := by
  sorry -- det of positive-definite matrix is positive

-- The regulator is computable from generators
-- (each neron_tate i j is a computable real, det is a polynomial in entries)
theorem regulator_computable :
  ∃ (f : ℕ → ℚ), ∀ (ε : ℚ), ε > 0 →
    ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → |↑(f n) - regulator| < ε := by
  sorry -- Composition of computable reals under polynomial operations

-- Key contrast with analytic rank: regulator is computable AND nonzero,
-- while L^(r)(E,1) is computable but zero-testing requires LPO
-- The BSD formula equates a computable-but-undecidable quantity
-- with computable-and-decidable quantities.
```

### 6.2 Proof Strategy

**regulator_positive:** The Néron-Tate matrix is positive-definite
(axiom). The determinant of a positive-definite real matrix is
strictly positive. This is a standard result; check if Mathlib
has `Matrix.PosDef.det_pos` or similar.

**regulator_computable:** Each entry neron_tate i j is a computable
real (it's defined as a limit of rational heights, which is a
computable Cauchy sequence). The determinant is a polynomial in the
entries (sum of products with signs). Polynomials preserve
computability of real numbers. Therefore det is computable.

---

## 7. B4: p-adic Contrast (B4_PadicContrast.lean)

### 7.1 Statement

```lean
-- p-adic heights are NOT positive-definite (u(ℚ_p) = 4)
-- This creates the "exceptional zero" pathology of Mazur-Tate-Teitelbaum

-- Import u-invariant result from Paper 45
axiom trace_form_isotropic_Qp :
  ∀ (n : ℕ), n ≥ 5 →
    ∃ (v : Fin n → Q_p), v ≠ 0 ∧
      ∀ (B : Fin n → Fin n → Q_p),
        (∀ i j, B i j = B j i) →
        ∑ i, ∑ j, v i * B i j * v j = 0
  -- Any symmetric bilinear form of dim ≥ 5 over ℚ_p is isotropic

-- p-adic height pairing cannot be positive-definite for rank ≥ 5
theorem padic_height_not_pos_def
  (hr : r ≥ 5) :
  ¬ (∀ (v : Fin r → Q_p), v ≠ 0 →
       ∑ i, ∑ j, v i * padic_height i j * v j ≠ 0) := by
  sorry -- From trace_form_isotropic_Qp

-- p-adic regulator can vanish (exceptional zero phenomenon)
-- Contrast with B3 where Archimedean regulator is always positive
theorem padic_regulator_can_vanish :
  ¬ (Matrix.det (Matrix.of padic_height) ≠ (0 : Q_p)) := by
  sorry -- Not provable in general; state as possibility
  -- More precisely: there exist representations where p-adic det = 0
```

### 7.2 Proof Strategy

This directly imports Paper 45 C3 methodology, applied to ℚ_p
instead of the generic local field. The key point: the same
u-invariant obstruction that blocks polarization for WMC/Tate/FM
also blocks positive-definiteness of the p-adic height pairing.

The contrast theorem is the formal expression of why classical BSD
works (u(ℝ) = 1, positive-definite, regulator > 0) while p-adic
BSD has pathologies (u(ℚ_p) = 4, not positive-definite, regulator
can vanish, requiring the ℒ-invariant correction of MTT).

---

## 8. Assembly (Main.lean)

```lean
import P48_BSD.Defs
import P48_BSD.B1_AnalyticLPO
import P48_BSD.B2_Polarization
import P48_BSD.B3_Regulator
import P48_BSD.B4_PadicContrast

-- Summary: BSD calibrates at LPO+MP (analytic) / BISH+MP (algebraic)
-- The Archimedean polarization (Néron-Tate) is AVAILABLE (u(ℝ) = 1)
-- unlike WMC/Tate/FM where u = 4 blocks it.
-- p-adic BSD fails precisely because u(ℚ_p) = 4.

theorem bsd_calibration_summary :
  -- B1: Analytic rank requires LPO
  (LPO_R → Decidable (L_value = 0))
  ∧
  -- B2: Archimedean polarization exists
  True  -- placeholder for inner product construction
  ∧
  -- B3: Regulator is positive (BISH, no LPO needed)
  (regulator > 0 → True)  -- placeholder
  ∧
  -- B4: p-adic contrast
  True  -- placeholder for u-invariant obstruction
  := by
  exact ⟨LPO_decides_L_zero, trivial, fun _ => trivial, trivial⟩
```

---

## 9. Axiom Budget

Expected custom axioms: ~10
1. L_value : ℝ (the L-function value)
2. L_computable (Cauchy sequence witness)
3. L_deriv : ℕ → ℝ (derivatives)
4. MW_generators, MW_rational (Mordell-Weil data)
5. neron_tate : Fin r → Fin r → ℝ (height pairing matrix)
6. neron_tate_pos_def (positive-definiteness)
7. padic_height (for contrast)
8. Q_p as field (for contrast)
9. trace_form_isotropic_Qp (from Paper 45)

Target: ≤ 10 custom axioms, 0 sorries on proved theorems.

---

## 10. Relationship to Paper 45

**Reuses:** LPO definition pattern, u-invariant obstruction (C3 → B4)

**New beyond Paper 45:**
- B2 (positive-definite inner product construction from height pairing)
  is the FIRST time in the atlas that polarization WORKS. Papers 45-47
  all proved polarization is BLOCKED. Paper 48 proves it is AVAILABLE.
  This is the Archimedean escape made concrete.
- B3 (regulator positivity) exercises Mathlib's positive-definite matrix
  API in a way the other papers don't.
- B4 (p-adic contrast) connects the u-invariant obstruction to the
  Mazur-Tate-Teitelbaum exceptional zero, a concrete number-theoretic
  phenomenon.
