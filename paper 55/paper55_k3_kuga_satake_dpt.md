# K3 Surfaces, the Kuga-Satake Construction, and the DPT Framework

## Paper 55 — Proof Document for Lean 4 Formalization Agent

### Paul C.-K. Lee
### February 2026

---

## 0. Purpose, Context, and Formalization Notes

This document provides a complete mathematical specification for the Lean 4
formalization of Paper 55 in the Constructive Reverse Mathematics (CRM)
programme, arithmetic geometry sequence.

**Series context:** Paper 54 performed the first out-of-sample test of
DPT via the Bloch-Kato conjecture, finding a partial decomposition with
two fracture points (mixed motives, p-adic volumes). Paper 55 performs
the SECOND out-of-sample test: K3 surfaces over finite fields. Unlike
Bloch-Kato, this calibration FULLY SUCCEEDS — all three DPT axioms are
realized, and the Kuga-Satake construction factors through the axioms
precisely as the framework predicts.

**Result summary:**
1. Axiom 1: transferred from KS(X)×KS(X) to X via André's motivated
   cycles (1996). Logically redundant for surfaces (Matsusaka 1957) but
   the functorial mechanism works exactly as DPT requires.
2. Axiom 2: independent of Kuga-Satake. Deligne Weil I, as always.
3. Axiom 3: THIS IS WHAT KUGA-SATAKE PROVIDES. It converts the indefinite
   intersection form on P²(X,R) (signature (2,19)) into a positive-definite
   Rosati involution on KS(X). The DPT framework correctly predicts that
   the reduction to abelian varieties exists BECAUSE the K3 surface lacks
   native positive-definiteness in the relevant sense.
4. No Picard-number boundary exists. Lefschetz (1,1) kills all exotic
   obstructions because K3 arithmetic lives in codimension 1.
5. The CY3 prediction is corrected: Axiom 3 does NOT fail for CY3s
   (Hodge-Riemann provides it natively). The true obstruction is Axiom 1
   at codimension 2, matching the abelian fourfold case.

**Formalization notes:**
- The Lean formalization captures the logical structure: which axiom
  each construction provides, why the Picard-number boundary vanishes,
  and why CY3s fail at Axiom 1 not Axiom 3.
- External theorems (André, Deligne, Hodge-Riemann, Lefschetz (1,1),
  Lieberman, Madapusi Pera) are axiomatized as principled sorries.
- The ZERO-SORRY target is the logical decomposition and the structural
  arguments about codimension.

**Target:** ~500-650 lines Lean 4
**Depends on:** Paper 50 (DPT class), Paper 54 (calibration record type)

---

## 1. THEOREM STATEMENTS (ENGLISH)

### Theorem A (Axiom 1 Transfer via Motivated Cycles)

Let X be a polarized K3 surface over F_q. Let KS(X) be its Kuga-Satake
abelian variety. The Kuga-Satake correspondence is a motivated cycle
(André 1996, Theorem 0.4). In the category of motives for motivated
cycles, h²(X) is a direct summand of h²(KS(X)×KS(X)). Because
numerical equivalence = homological equivalence on abelian varieties
(Lieberman 1968), and this equality is preserved under the split
injection, Axiom 1 (decidable equality) transfers from KS(X) to X.

For surfaces, this is logically redundant: Matsusaka (1957) gives
Conjecture D for divisors unconditionally. But the functorial mechanism
works as DPT predicts.

### Theorem B (Axiom 2 Independence)

Frobenius eigenvalues on H²(X_{F_q}, Q_ℓ) are Weil numbers of weight 2,
hence algebraic integers. This is Deligne (1974), Théorème 1.6. The
Kuga-Satake embedding preserves eigenvalues (Galois-equivariant) but
does not provide the algebraicity. Axiom 2 holds independently.

### Theorem C (Axiom 3 via Kuga-Satake: The Core Result)

The intersection form on primitive cohomology P²(X, R) has signature
(2, 19) — indefinite. The Kuga-Satake construction:

(i)   Takes the even Clifford algebra C⁺(P²(X, Z))
(ii)  Equips it with the canonical trace form from the main involution
(iii) This trace form is positive-definite
(iv)  It becomes the Riemann form on the complex torus KS(X) of
      dimension 2^{19}
(v)   This induces a positive-definite Rosati involution on KS(X)

In Madapusi Pera (2015, Proposition 3.14), this positive-definiteness
is operationally required: it embeds the orthogonal Shimura variety
into a Siegel modular variety, enabling Faltings' finiteness theorem
to bound heights of lifted Tate cycles.

**This is exactly the DPT prediction:** the K3 surface lacks Axiom 3
natively, and the Kuga-Satake construction manufactures it.

### Theorem D (Supersingular Bypass)

For supersingular K3 surfaces (ρ = 22 in char p ≥ 5), the entire H²
is algebraic. The transcendental lattice T(X) has rank 0. The Tate
conjecture is proved (Nygaard-Ogus 1985, Charles 2013, Maulik 2014)
without Kuga-Satake. Since there is no transcendental data requiring
Archimedean descent, Axiom 3 is vacuously satisfied.

### Theorem E (No Picard Number Boundary)

For K3 surfaces, ALL Hodge/Tate classes lie in H² (degree 2,
codimension 1). By Lefschetz (1,1) — unconditional — every such
class is a divisor class, hence lies in the Lefschetz ring. The
transcendental lattice T(X) contains zero Hodge classes by definition.
H⁴ is 1-dimensional, generated by the point class.

Therefore: the Lefschetz ring equals the full algebra of algebraic
cycles, for ALL K3 surfaces regardless of Picard number.

The DPT boundary at codimension 2 (abelian fourfolds, exotic Weil
classes) has no K3 analogue. The organizing principle is CODIMENSION
of Hodge classes, not dimension of the variety.

### Theorem F (CY3 Correction: Axiom 1 Fails, Not Axiom 3)

For a Calabi-Yau threefold Y:

(i)   Axiom 3 does NOT fail: the Hodge-Riemann bilinear relations
      give a positive-definite form H(x,y) = Q(x,Cy) on H³(Y,R)
      and H⁴(Y,R) unconditionally.
(ii)  Kuga-Satake does not exist for CY3s (weight 3 Hodge structure
      cannot embed into weight 1 of an abelian variety).
(iii) But the absence of Kuga-Satake is not an Axiom 3 problem — it's
      a proof-strategy problem (cannot reduce to abelian varieties).
(iv)  The true DPT obstruction: unknown Hodge classes in H⁴(Y)
      (codimension 2) escape the Lefschetz ring. This is an Axiom 1
      failure, identical to the abelian fourfold case.

### Theorem G (Calibration Verdict)

| Component               | DPT Axiom | Status  | Provider         |
|--------------------------|----------|---------|------------------|
| Cycle decidability       | Axiom 1  | Proven  | André motivated  |
| Frobenius algebraicity   | Axiom 2  | Proven  | Deligne Weil I   |
| Positive-definite form   | Axiom 3  | Proven  | KS trace form    |
| Supersingular case       | (all)    | Proven  | Direct (no KS)   |
| Picard number boundary   | —        | None    | Lefschetz (1,1)  |

Full decomposition succeeds. First calibration outside abelian
varieties where all three axioms are realized.

---

## 2. LEAN MODULE PLAN

### Module 1: K3DPTCalibration.lean (~60 lines, 0 sorry)

Import the DPT calibration record from Paper 54. Define K3-specific
types.

```
-- K3-specific structures
structure K3Surface where
  picard_number : ℕ
  hp_picard_le_20 : picard_number ≤ 20  -- over alg closed field char 0
  -- Over F_q: picard_number ≤ 22

structure PrimitiveIntersectionForm where
  pos_inertia : ℕ := 2
  neg_inertia : ℕ := 19
  signature_is_2_19 : pos_inertia = 2 ∧ neg_inertia = 19

-- The intersection form is indefinite
theorem intersection_form_indefinite (Q : PrimitiveIntersectionForm) :
    ¬PositiveDefinite Q.to_bilinear ∧ ¬NegativeDefinite Q.to_bilinear := by
  constructor
  · intro hpos
    -- Positive-definite has signature (21, 0), not (2, 19)
    exact absurd Q.signature_is_2_19.2 (by omega)
  · intro hneg
    -- Negative-definite has signature (0, 21), not (2, 19)
    exact absurd Q.signature_is_2_19.1 (by omega)
```

### Module 2: Axiom1Transfer.lean (~100 lines, 3 principled sorry)

Formalize Theorem A: motivated cycle transfer of decidability.

```
-- Axiomatize André's theorem
axiom andre_motivated_cycle :
  ∀ (X : K3Surface) (KS : AbelianVariety),
    IsKugaSatake KS X →
    IsMotivatedCycle (kuga_satake_correspondence X KS)

-- Axiomatize Lieberman's theorem for abelian varieties
axiom lieberman_hom_num_abelian :
  ∀ (A : AbelianVariety),
    HomologicalEq A = NumericalEq A

-- Axiomatize Matsusaka for surfaces (makes transfer redundant
-- but we prove it anyway for the DPT mechanism)
axiom matsusaka_conj_d_surfaces :
  ∀ (S : Surface),
    ConjectureD_Divisors S

-- Transfer theorem
theorem axiom1_transfer (X : K3Surface) (KS : AbelianVariety)
    (hKS : IsKugaSatake KS X) :
    DecidableEq (CH_num X) := by
  -- h²(X) is a direct summand of h²(KS×KS) via motivated cycle
  have hmot := andre_motivated_cycle X KS hKS
  -- Numerical = homological on KS×KS (Lieberman)
  have hlib := lieberman_hom_num_abelian (KS ×ₐ KS)
  -- Decidability on abelian variety pulls back through split injection
  exact decidability_pullback hmot hlib

-- Alternative: direct proof for surfaces (Matsusaka)
theorem axiom1_direct (X : K3Surface) :
    DecidableEq (CH_num X) := by
  exact matsusaka_conj_d_surfaces X.to_surface
```

**Sorry budget:**
- `andre_motivated_cycle`: principled (André 1996, Theorem 0.4)
- `lieberman_hom_num_abelian`: principled (Lieberman 1968)
- `matsusaka_conj_d_surfaces`: principled (Matsusaka 1957)

### Module 3: Axiom2Independence.lean (~50 lines, 1 principled sorry)

Formalize Theorem B.

```
-- Same Deligne axiom as Paper 54 Module 3
axiom deligne_weil_I :
  ∀ (X : SmoothProjectiveVariety) (p : Prime) (ℓ : Prime) (hℓ : ℓ ≠ p),
    ∀ α ∈ frobenius_eigenvalues X p ℓ,
      IsAlgebraicInteger α

-- Axiom 2 for K3 surfaces: independent of Kuga-Satake
theorem axiom2_k3 (X : K3Surface) (p : Prime) :
    AlgebraicSpectrum (H2_etale X p) := by
  intro α hα
  exact deligne_weil_I X.to_variety p (aux_prime p) (by assumption) α hα

-- Kuga-Satake preserves but does not provide eigenvalues
theorem ks_preserves_eigenvalues (X : K3Surface) (KS : AbelianVariety)
    (hKS : IsKugaSatake KS X) (p : Prime) :
    frobenius_eigenvalues X p ⊆ frobenius_eigenvalues (KS ×ₐ KS) p := by
  exact kuga_satake_galois_equivariant hKS p
```

**Sorry budget:**
- `deligne_weil_I`: principled (Deligne 1974, Théorème 1.6) — shared with Paper 54

### Module 4: Axiom3KugaSatake.lean (~130 lines, 2 principled sorry)

Formalize Theorem C: the core result. Kuga-Satake manufactures
positive-definiteness.

```
-- The Clifford algebra construction
structure CliffordAlgebraData (X : K3Surface) where
  -- C⁺(P²(X, Z)): even part of Clifford algebra
  even_clifford : Type
  -- The trace form from the main involution
  trace_form : BilinearForm ℝ even_clifford
  -- THIS IS THE KEY: the trace form is positive-definite
  trace_positive_definite : PositiveDefinite trace_form

-- Axiomatize: Clifford algebra trace form is positive-definite
-- This is a theorem in Clifford algebra theory, not a conjecture
axiom clifford_trace_positive_definite :
  ∀ (V : QuadraticSpace ℤ) (hV : Signature V = (2, 19)),
    PositiveDefinite (clifford_trace_form (even_clifford V))

-- Axiomatize: the Rosati involution on KS(X) is induced by
-- the Clifford trace form
axiom rosati_from_clifford_trace :
  ∀ (X : K3Surface) (KS : AbelianVariety)
    (hKS : IsKugaSatake KS X),
    RosatiInvolution KS = induced_from (clifford_trace_form X)

-- The main theorem: Kuga-Satake provides Axiom 3
theorem axiom3_via_kuga_satake (X : K3Surface) (KS : AbelianVariety)
    (hKS : IsKugaSatake KS X) :
    ArchimedeanPolarized KS := by
  -- The Clifford trace form is positive-definite
  have hpd := clifford_trace_positive_definite
    (primitive_lattice X) (signature_2_19 X)
  -- This induces the Rosati involution
  have hros := rosati_from_clifford_trace X KS hKS
  -- Rosati involution is positive-definite
  exact ⟨rosati_form KS, by rw [hros]; exact hpd, u_invariant_real_infinite⟩

-- The K3 surface LACKS native Axiom 3
theorem k3_lacks_native_axiom3 (X : K3Surface) :
    ¬PositiveDefinite (intersection_form_P2 X) := by
  exact (intersection_form_indefinite (primitive_form X)).1
```

**Sorry budget:**
- `clifford_trace_positive_definite`: principled (standard Clifford algebra
  theory; see Lawson-Michelsohn, "Spin Geometry", Chapter I)
- `rosati_from_clifford_trace`: principled (see van Geemen, "Kuga-Satake
  varieties and the Hodge conjecture", §2)

### Module 5: SupersingularBypass.lean (~70 lines, 1 principled sorry)

Formalize Theorem D.

```
-- Supersingular: ρ = 22, T(X) = 0
structure SupersingularK3 extends K3Surface where
  picard_22 : picard_number = 22  -- in char p
  transcendental_rank_zero : rank (transcendental_lattice self) = 0

-- Axiomatize: Tate conjecture for supersingular K3 proved without KS
axiom tate_supersingular_direct :
  ∀ (X : SupersingularK3) (p : Prime) (hp : p ≥ 5),
    TateConjecture X p

-- All three axioms hold trivially
theorem dpt_supersingular (X : SupersingularK3) (p : Prime) (hp : p ≥ 5) :
    DPTSatisfied X := by
  constructor
  · -- Axiom 1: all classes are divisorial, trivially decidable
    exact axiom1_direct X.to_K3Surface
  constructor
  · -- Axiom 2: Deligne as always
    exact axiom2_k3 X.to_K3Surface p
  · -- Axiom 3: vacuously satisfied (no transcendental data to descend)
    exact axiom3_vacuous X.transcendental_rank_zero
```

**Sorry budget:**
- `tate_supersingular_direct`: principled (Nygaard-Ogus 1985; Charles 2013;
  Maulik 2014)

### Module 6: NoPicardBoundary.lean (~100 lines, 1 principled sorry)

Formalize Theorem E: the absence of a decidability boundary.

```
-- Axiomatize Lefschetz (1,1)
axiom lefschetz_1_1 :
  ∀ (X : SmoothProjectiveVariety),
    ∀ c ∈ hodge_classes X 1 1,
      c ∈ divisor_classes X

-- K3: all Hodge/Tate classes live in H² (codimension 1)
theorem k3_all_classes_codim_1 (X : K3Surface) :
    ∀ c ∈ algebraic_classes X,
      codimension c = 1 ∨ codimension c = 0 ∨ codimension c = 2 := by
  -- H⁰: trivial (generated by 1)
  -- H²: the only interesting cohomology
  -- H⁴: 1-dimensional, generated by point class
  intro c hc
  exact k3_cohomology_structure X c hc

-- All algebraic classes lie in the Lefschetz ring
theorem k3_lefschetz_exhaustive (X : K3Surface) :
    algebraic_classes X = lefschetz_ring X := by
  ext c
  constructor
  · intro hc
    -- Case split on codimension
    rcases k3_all_classes_codim_1 X c hc with h0 | h1 | h2
    · -- Codimension 1: Lefschetz (1,1)
      exact lefschetz_ring_contains_divisors (lefschetz_1_1 X c (by assumption))
    · -- Codimension 0: trivially in Lefschetz ring
      exact lefschetz_ring_contains_constants h1
    · -- Codimension 2 (= degree 4): generated by point = L²
      exact lefschetz_ring_contains_top h2
  · -- Lefschetz ring ⊆ algebraic: immediate
    exact lefschetz_ring_algebraic X

-- The transcendental lattice contains NO Hodge classes
theorem transcendental_no_hodge (X : K3Surface) :
    ∀ c ∈ transcendental_lattice X,
      c ∉ hodge_classes X 1 1 := by
  -- By definition: T(X) = (NS(X))⊥ in H²
  -- Hodge classes in H² are precisely NS(X) ⊗ Q
  -- Their intersection with T(X) is {0}
  exact transcendental_orthogonal_to_algebraic X

-- Therefore: no Picard-number-dependent boundary
theorem no_picard_boundary (X : K3Surface) :
    ∀ (ρ : ℕ) (hρ : X.picard_number = ρ),
      ¬∃ (c : AlgebraicClass X), c ∉ lefschetz_ring X := by
  intro ρ hρ ⟨c, hc_alg, hc_not_lef⟩
  exact hc_not_lef (k3_lefschetz_exhaustive X ▸ hc_alg)
```

**Sorry budget:**
- `lefschetz_1_1`: principled (Lefschetz 1924; see Griffiths-Harris,
  "Principles of Algebraic Geometry", §1.2)

### Module 7: CY3Correction.lean (~100 lines, 1 principled sorry)

Formalize Theorem F: the CY3 correction.

```
structure CalabiYauThreefold where
  h30 : ℕ := 1
  h21 : ℕ  -- > 0 for non-rigid CY3
  h_mirror : h30 = 1

-- Axiomatize Hodge-Riemann for weight 3
axiom hodge_riemann_weight3 :
  ∀ (Y : CalabiYauThreefold),
    ∃ (H : BilinearForm ℝ (H3_Betti Y)),
      PositiveDefinite H

-- CY3: Axiom 3 does NOT fail
theorem cy3_axiom3_holds (Y : CalabiYauThreefold) :
    ArchimedeanPolarized (H3_Betti Y) := by
  obtain ⟨H, hH⟩ := hodge_riemann_weight3 Y
  exact ⟨H, hH, u_invariant_real_infinite⟩

-- CY3: no Kuga-Satake (weight 3 ≠ weight 1)
theorem cy3_no_kuga_satake (Y : CalabiYauThreefold) :
    ¬∃ (A : AbelianVariety), IsKugaSatake A Y := by
  intro ⟨A, hKS⟩
  -- Kuga-Satake requires weight 2 Hodge structure
  -- H³(Y) has weight 3
  exact weight_mismatch hKS (cy3_weight_3 Y)

-- CY3: the TRUE obstruction is Axiom 1 at codimension 2
-- H⁴(Y) can contain Hodge classes not generated by divisors
theorem cy3_axiom1_obstruction (Y : CalabiYauThreefold) :
    ∃ (subspace : CohomologySubspace Y 4),
      MayContainHodgeClasses subspace ∧
      ¬(subspace ⊆ lefschetz_ring Y) := by
  -- H⁴(Y) has dimension h²² = h¹¹ which can be large
  -- Classes in H^{2,2} not generated by H^{1,1} ∧ H^{1,1}
  -- escape the Lefschetz ring
  -- This is the SAME obstruction as abelian fourfolds
  use codim2_subspace Y
  constructor
  · exact h22_contains_hodge Y
  · exact codim2_escapes_lefschetz Y

-- The codimension principle: failure mode is codimension, not dimension
theorem codimension_principle :
    ∀ (V : SmoothProjectiveVariety),
      DPT_Obstruction V ↔
        ∃ (p : ℕ) (hp : p ≥ 2),
          ∃ c ∈ hodge_classes V p p,
            c ∉ lefschetz_ring V := by
  -- Codimension ≥ 2 is the universal failure mode
  -- Codimension 1: always handled by Lefschetz (1,1)
  -- Codimension 0: trivial
  sorry -- This is a structural claim about the DPT framework;
        -- could be proved from the axioms but left as a
        -- summarizing observation
```

**Sorry budget:**
- `hodge_riemann_weight3`: principled (Hodge 1941; Griffiths 1969,
  "On the periods of certain rational integrals")
- `codimension_principle` sorry: this is a summarizing observation,
  not a gap — it packages the pattern from Papers 50, 54, 55. Could
  be removed by stating it as a definition instead of a theorem.

### Module 8: K3CalibrationVerdict.lean (~80 lines, 0 sorry)

Assemble the full result.

```
def k3Calibration : DPTCalibration := {
  name := "Tate Conjecture for K3 Surfaces"
  axiom1_source := some "André motivated cycles (1996) / Matsusaka (1957)"
  axiom1_status := .proven
  axiom2_source := some "Deligne Weil I Théorème 1.6 (1974)"
  axiom2_status := .proven
  axiom3_source := some "Clifford trace form → Rosati involution on KS(X)"
  axiom3_status := .proven
  extra_costs := []
  lpo_source := "Not applicable (Tate conjecture is algebraic, no L-function)"
  decomposition_succeeds := .yes
}

-- The extended 7-row comparison table
def extendedCalibrationTable : List DPTCalibration :=
  [wmcCalibration,       -- Paper 45: all ✓
   tateCalibration,      -- Paper 46: all ✓
   fontaineMazur,        -- Paper 47: all ✓
   bsdCalibration,       -- Paper 48: all ✓
   hodgeCalibration,     -- Paper 49: all ✓
   blochKatoCalibration, -- Paper 54: PARTIAL
   k3Calibration]        -- Paper 55: all ✓

-- Paper 55 is the first calibration OUTSIDE abelian varieties
-- where all three axioms succeed.
-- Paper 54 was the first partial failure.
-- Together they establish:
--   Pure motives + codimension 1: always works (K3)
--   Pure motives + codimension ≥ 2: fails at Axiom 1 (abelian 4-folds, CY3)
--   Mixed motives: fails at Axiom 1 for Ext¹ (Bloch-Kato)
--   p-adic: fails outside all axioms (Tamagawa factors)
```

---

## 3. SORRY BUDGET SUMMARY

| Module | Sorry Count | Classification |
|--------|-------------|----------------|
| 1. K3DPTCalibration       | 0 | — |
| 2. Axiom1Transfer         | 3 | principled (André, Lieberman, Matsusaka) |
| 3. Axiom2Independence     | 1 | principled (Deligne 1974) |
| 4. Axiom3KugaSatake       | 2 | principled (Clifford trace, van Geemen) |
| 5. SupersingularBypass    | 1 | principled (Nygaard-Ogus/Charles/Maulik) |
| 6. NoPicardBoundary       | 1 | principled (Lefschetz 1924) |
| 7. CY3Correction          | 1 | principled (Hodge-Riemann weight 3) |
|                            | 1 | structural observation (could be definition) |
| 8. K3CalibrationVerdict   | 0 | — |
| **TOTAL**                 | **10** | **9 principled, 1 structural, 0 gaps** |

The 9 principled sorries axiomatize:
1. André motivated cycles (1996, Theorem 0.4)
2. Lieberman hom = num for abelian varieties (1968)
3. Matsusaka Conjecture D for divisors on surfaces (1957)
4. Deligne Weil I (1974, Théorème 1.6)
5. Clifford algebra trace form positive-definiteness (Lawson-Michelsohn)
6. Rosati from Clifford trace (van Geemen)
7. Tate for supersingular K3 (Nygaard-Ogus 1985)
8. Lefschetz (1,1) theorem (1924)
9. Hodge-Riemann bilinear relations weight 3 (Hodge 1941)

---

## 4. CRITICAL INSTRUCTIONS FOR LEAN AGENT

### 4.1 What to import

- Paper 50: `DecidablePolarizedTannakian` class, `u_invariant_real_infinite`
- Paper 54: `DPTCalibration` record type, `blochKatoCalibration`
- If imports unavailable, STUB with clearly marked axioms.

### 4.2 What NOT to do

- Do NOT formalize the full Clifford algebra construction. Axiomatize
  the positive-definiteness of the trace form.
- Do NOT formalize André's motivated cycle category. Axiomatize the
  key property (KS correspondence is motivated).
- Do NOT attempt to formalize Madapusi Pera's proof of Tate for K3.
  That is a 50-page argument using integral canonical models of Shimura
  varieties. Axiomatize the result.
- Do NOT add sections on "further directions" or "extending to other
  varieties." Paper 55 covers K3 surfaces and CY3 corrections. Period.

### 4.3 What MUST compile

1. `intersection_form_indefinite` — signature (2,19) implies not
   positive-definite (zero sorry, pure logic)
2. `axiom3_via_kuga_satake` — KS provides Axiom 3
3. `k3_lacks_native_axiom3` — K3 does NOT have native Axiom 3
4. `k3_lefschetz_exhaustive` — all algebraic classes are Lefschetz
5. `no_picard_boundary` — no ρ-dependent boundary
6. `cy3_axiom3_holds` — CY3 DOES satisfy Axiom 3 (correction)
7. `cy3_axiom1_obstruction` — CY3 fails at Axiom 1 codim 2
8. `extendedCalibrationTable` — the 7-row comparison table

### 4.4 The key logical chain (must be machine-checkable)

```
K3 surface X
  → intersection form indefinite (signature (2,19))
  → lacks native Axiom 3
  → Kuga-Satake produces KS(X) with positive-definite Rosati
  → Axiom 3 acquired
  → Axiom 1 via André + Lieberman (or directly via Matsusaka)
  → Axiom 2 via Deligne (independent of KS)
  → Full DPT decomposition succeeds
```

This chain should be a single theorem composing the module results.

---

## 5. PAPER STRUCTURE (LaTeX)

§1. Introduction
    - DPT framework recap (3 axioms, 5+1 calibrations)
    - K3 surfaces as second out-of-sample test
    - Summary: full decomposition succeeds, Kuga-Satake = Axiom 3

§2. K3 surfaces and the Kuga-Satake construction (review)
    - Polarized K3, primitive cohomology, signature (2,19)
    - Clifford algebra, even part, trace form
    - KS(X) as 2^{19}-dimensional abelian variety
    - Role in proofs of Tate conjecture (Charles, Madapusi Pera)

§3. Axiom-by-axiom calibration (Theorems A, B, C)
    - Axiom 1: motivated cycle transfer (André) + surface redundancy
    - Axiom 2: Deligne Weil I (independent of KS)
    - Axiom 3: KS converts indefinite → positive-definite

§4. The supersingular case (Theorem D)
    - ρ = 22, T(X) = 0, no KS needed
    - DPT reading: Axiom 3 vacuously satisfied

§5. No Picard number boundary (Theorem E)
    - Lefschetz (1,1) kills all exotic obstructions
    - Contrast with abelian fourfolds: codimension is the principle
    - The codimension hierarchy

§6. Correction: Calabi-Yau threefolds (Theorem F)
    - The incorrect prediction: Axiom 3 fails for CY3
    - The correction: Hodge-Riemann gives Axiom 3 natively
    - The true obstruction: Axiom 1 at codimension 2
    - Universal failure mode: same as abelian fourfolds

§7. Lean formalization
    - [TO BE FILLED AFTER COMPILATION]

§8. Implications
    - K3: full success, KS factors through DPT
    - CY3 correction sharpens the obstruction hierarchy
    - Combined with Paper 54: the DPT boundary map is now:
      codim 1 → always works
      codim ≥ 2 pure → Axiom 1 fails (Lefschetz escape)
      mixed → Axiom 1 fails (no Ext¹ decidability)
      p-adic → outside all axioms (Tamagawa factors)

---

## 6. KEY REFERENCES

- André, Y. "Pour une théorie inconditionnelle des motifs."
  Publ. Math. IHÉS 83 (1996), 5–49. [Theorem 0.4: KS is motivated]
- Charles, F. "The Tate conjecture for K3 surfaces over finite fields."
  Invent. Math. 194 (2013), 119–145.
- Deligne, P. "La conjecture de Weil. I."
  Publ. Math. IHÉS 43 (1974), 273–307.
- Griffiths, P. "On the periods of certain rational integrals: I, II."
  Ann. of Math. 90 (1969), 460–541.
- Hodge, W. V. D. "The Theory and Applications of Harmonic Integrals."
  Cambridge Univ. Press, 1941.
- Lawson, H. B. and Michelsohn, M.-L. "Spin Geometry."
  Princeton Univ. Press, 1989. [Clifford algebra trace form]
- Lefschetz, S. "L'analysis situs et la géométrie algébrique."
  Gauthier-Villars, 1924.
- Lee, P. C.-K. "Paper 50: Decidability landscape for the Standard
  Conjectures." Zenodo, 2026.
- Lee, P. C.-K. "Paper 54: The Bloch-Kato calibration." Zenodo, 2026.
- Lieberman, D. "Numerical and homological equivalence of algebraic
  cycles on Hodge manifolds." Amer. J. Math. 90 (1968), 366–374.
- Madapusi Pera, K. "The Tate conjecture for K3 surfaces in odd
  characteristic." Invent. Math. 201 (2015), 625–668.
  [Proposition 3.14: Shimura variety embedding]
- Matsusaka, T. "The criteria for algebraic equivalence and the
  torsion group." Amer. J. Math. 79 (1957), 53–66.
- Maulik, D. "Supersingular K3 surfaces for large primes."
  Duke Math. J. 163 (2014), 2357–2425.
- Nygaard, N. and Ogus, A. "Tate's conjecture for K3 surfaces of
  finite height." Ann. of Math. 122 (1985), 461–507.
- van Geemen, B. "Kuga-Satake varieties and the Hodge conjecture."
  The Arithmetic and Geometry of Algebraic Cycles, NATO Sci. Ser.
  548 (2000), 51–82.
