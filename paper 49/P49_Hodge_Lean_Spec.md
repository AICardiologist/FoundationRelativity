# Paper 49: Hodge Conjecture — Lean 4 Formalization Specification

## Constructive Calibration of the Hodge Conjecture

**Target:** Formalize the constructive reverse mathematics calibration of
the Hodge Conjecture, proving that:
- H1: Verifying Hodge type (r,r) requires LPO over ℂ/ℝ
- H2: Verifying rationality of periods requires LPO + MP
- H3: The Hodge-Riemann polarization is available (u(ℝ) = 1) but
      blind to the rational lattice
- H4: Algebraic cycle verification is BISH-decidable (integer intersections)
- H5: The Hodge Conjecture is the nexus where algebraic descent and
      Archimedean polarization interact

**Dependencies:** Mathlib4 (InnerProductSpace, real/complex analysis), Paper 45

---

## 1. Mathematical Context

### 1.1 The Hodge Conjecture

Let X be a smooth projective variety over ℂ.
H^{2r}(X(ℂ), ℚ) ∩ H^{r,r}(X) consists of Hodge classes.
The Hodge Conjecture: every Hodge class is a ℚ-linear combination
of algebraic cycle classes.

### 1.2 Constructive Content

**Abstract side (LPO + MP):** The Hodge decomposition uses harmonic
theory (elliptic PDEs). Verifying a class is type (r,r) requires
checking that non-(r,r) harmonic projections vanish exactly (LPO).
Verifying rational periods requires deciding whether transcendental
integrals are rational (LPO + MP for numerator/denominator search).

**Geometric side (BISH + MP):** Algebraic cycles have integer
intersection numbers (BISH-decidable). Finding cycles requires
search (MP).

**The nexus:** The Hodge Conjecture lives at the Archimedean place
where BOTH mechanisms (algebraic descent and polarization) operate.
The Hodge-Riemann metric splits continuous space, but the conjecture
asserts compatibility with the rational lattice — requiring algebraic
descent on top of polarization.

---

## 2. File Structure

```
P49_Hodge/
├── Defs.lean              -- Core definitions
├── H1_HodgeTypeLPO.lean   -- Type (r,r) verification requires LPO
├── H2_RationalityLPO.lean -- Rational period verification requires LPO+MP
├── H3_Polarization.lean   -- Hodge-Riemann polarization (available but blind to ℚ)
├── H4_CycleVerify.lean    -- Cycle verification is BISH
├── H5_Nexus.lean          -- The nexus theorem
├── Main.lean              -- Assembly
└── lakefile.lean
```

---

## 3. Definitions (Defs.lean)

```lean
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension

universe u

-- LPO for ℝ and ℂ
def LPO_R : Prop := ∀ (x : ℝ), x = 0 ∨ x ≠ 0
def LPO_C : Prop := ∀ (z : ℂ), z = 0 ∨ z ≠ 0

-- The cohomology space H = H^{2r}(X(ℂ), ℂ) (complex vector space)
axiom H_C : Type  -- H^{2r}(X, ℂ)
axiom H_C_addCommGroup : AddCommGroup H_C
axiom H_C_module : Module ℂ H_C
axiom H_C_finiteDim : FiniteDimensional ℂ H_C

-- The rational lattice H_ℚ = H^{2r}(X(ℂ), ℚ) (ℚ-subspace)
axiom H_Q : Type  -- H^{2r}(X, ℚ)
axiom H_Q_addCommGroup : AddCommGroup H_Q
axiom H_Q_module : Module ℚ H_Q
axiom H_Q_finiteDim : FiniteDimensional ℚ H_Q
axiom H_Q_decidableEq : DecidableEq H_Q

-- Inclusion H_ℚ ↪ H_ℂ (via ℚ ↪ ℂ)
axiom rational_inclusion : H_Q →ₗ[ℚ] H_C

-- Hodge decomposition: projections onto (p,q) components
-- For the (r,r) component:
axiom hodge_projection_rr : H_C →ₗ[ℂ] H_C  -- π_{r,r}
axiom hodge_projection_complement : H_C →ₗ[ℂ] H_C  -- id - π_{r,r}

-- Hodge decomposition properties
axiom hodge_decomposition :
  ∀ (x : H_C), x = hodge_projection_rr x + hodge_projection_complement x
axiom hodge_projections_complementary :
  hodge_projection_rr ∘ₗ hodge_projection_complement = 0

-- Hodge-Riemann bilinear form (Archimedean polarization)
axiom hodge_riemann : H_C → H_C → ℝ  -- Q(α, β)
axiom hodge_riemann_pos_def_on_primitive :
  ∀ (x : H_C), hodge_projection_rr x = x → x ≠ 0 →
    hodge_riemann x x > 0
  -- Positive-definite on primitive (r,r)-classes

-- Algebraic cycles
axiom ChowGroup : Type
axiom ChowGroup_addCommGroup : AddCommGroup ChowGroup
axiom ChowGroup_module : Module ℚ ChowGroup
axiom cycle_class : ChowGroup →ₗ[ℚ] H_Q

-- Intersection pairing (integer-valued)
axiom intersection : ChowGroup → ChowGroup → ℤ
```

---

## 4. H1: Hodge Type Requires LPO (H1_HodgeTypeLPO.lean)

### 4.1 Statement

```lean
-- A class is of Hodge type (r,r) if its complement projection vanishes
def is_hodge_type_rr (x : H_C) : Prop :=
  hodge_projection_complement x = 0

-- Deciding Hodge type requires LPO
theorem hodge_type_requires_LPO :
  (∀ (x : H_C), Decidable (is_hodge_type_rr x)) → LPO_C := by
  sorry

-- LPO suffices for deciding Hodge type
theorem LPO_decides_hodge_type :
  LPO_C → (∀ (x : H_C), Decidable (is_hodge_type_rr x)) := by
  sorry

-- Equivalence
theorem hodge_type_iff_LPO :
  (∀ (x : H_C), Decidable (is_hodge_type_rr x)) ↔ LPO_C := by
  exact ⟨hodge_type_requires_LPO, LPO_decides_hodge_type⟩
```

### 4.2 Proof Strategy

**H1 (→):** is_hodge_type_rr x tests whether a vector in a complex
vector space equals zero. For any z : ℂ, construct x_z such that
hodge_projection_complement x_z = z • e for some fixed basis vector e.
Then deciding is_hodge_type_rr x_z decides z = 0. This requires an
encoding axiom that the complement projection is surjective (or at
least has nontrivial image).

**H1 (←):** Given LPO_C, deciding hodge_projection_complement x = 0
reduces to testing finitely many complex coordinates for zero (by
finite-dimensionality). LPO on each coordinate, finite conjunction.

Parallels Paper 45 C2, Paper 46 T1.

---

## 5. H2: Rationality Requires LPO + MP (H2_RationalityLPO.lean)

### 5.1 Statement

```lean
-- A complex class is rational if it lies in the image of rational_inclusion
def is_rational (x : H_C) : Prop :=
  ∃ (q : H_Q), rational_inclusion q = x

-- Deciding rationality requires LPO + MP
-- LPO: testing whether complex coordinates are rational
-- MP: searching for the rational representative (numerator/denominator)

-- LPO component: testing a complex number for rationality requires LPO
-- (is this computable complex number exactly equal to some rational?)
axiom rationality_test_requires_LPO :
  (∀ (z : ℂ), Decidable (∃ (q : ℚ), (algebraMap ℚ ℂ q) = z)) → LPO_C

-- MP component: even with LPO, finding the rational is unbounded search
-- (which p/q equals this real number?)

-- Combined: deciding is_rational requires LPO + MP
theorem rationality_requires_LPO :
  (∀ (x : H_C), Decidable (is_rational x)) → LPO_C := by
  sorry
```

### 5.2 Proof Strategy

Testing whether a computable complex number z is rational means:
does there exist p/q ∈ ℚ such that z = p/q? First, testing z = p/q
for a specific p/q requires checking z - p/q = 0 (LPO). Second,
finding p and q requires unbounded search (MP). The combination
LPO + MP is needed.

For the formal proof of rationality_requires_LPO: construct, for
any w : ℂ, a class x_w ∈ H_C whose rationality is equivalent to
w = 0. This requires an encoding axiom about the structure of H_C.

---

## 6. H3: Polarization Available but Blind (H3_Polarization.lean)

### 6.1 Statement

```lean
-- The Hodge-Riemann form provides an inner product on (r,r)-classes
-- This is the Archimedean polarization (u(ℝ) = 1)

-- Construct inner product space on (r,r) subspace
-- (from hodge_riemann_pos_def_on_primitive)
theorem archimedean_polarization_available :
  ∃ (S : Submodule ℂ H_C),  -- the (r,r) subspace
    ∃ (ip : InnerProductSpace ℝ S),
      ∀ (x : S), x ≠ 0 → @inner ℝ _ ip.toInner x x > 0 := by
  sorry

-- The polarization SPLITS the Hodge decomposition constructively
-- (orthogonal projection onto (r,r) is computable in BISH
-- given the positive-definite metric)
theorem hodge_splitting_BISH :
  -- Given the inner product, projection is computable
  -- (distance minimization in a strictly convex space)
  True := by  -- simplified placeholder
  trivial

-- BUT: the polarization is blind to ℚ
-- The metric is defined by integration (analytic, over ℂ)
-- It cannot distinguish rational classes from irrational ones

-- Formally: the inner product does not respect the rational lattice
-- (there is no reason for ⟨q₁, q₂⟩ to be rational for q₁, q₂ ∈ H_ℚ)
axiom polarization_blind_to_Q :
  ¬ (∀ (q₁ q₂ : H_Q),
       ∃ (r : ℚ), hodge_riemann
         (rational_inclusion q₁)
         (rational_inclusion q₂) = ↑r)
  -- The Hodge-Riemann pairing of rational classes is generally transcendental
  -- (related to Kontsevich-Zagier period conjecture)

-- This is WHY the Hodge Conjecture is hard:
-- The metric can split continuous space but cannot see rational structure.
-- Algebraic descent (from ℂ to ℚ via cycle classes) is needed ON TOP of
-- the polarization.
```

### 6.2 Proof Strategy

The key insight formalized: the Hodge-Riemann pairing evaluates as
period integrals ∫ α ∧ *β̄, which are generally transcendental numbers
(not rational). So even though the metric exists and is positive-definite
(allowing orthogonal splitting), it cannot distinguish rational Hodge
classes from irrational ones. The Hodge Conjecture asserts that when
a class is BOTH type (r,r) AND rational, it's algebraic — but the
metric alone can only verify the first condition, not the second.

polarization_blind_to_Q is an axiom encoding the transcendence of
periods (a deep fact related to the Kontsevich-Zagier conjecture).

---

## 7. H4: Cycle Verification in BISH (H4_CycleVerify.lean)

### 7.1 Statement

```lean
-- Intersection numbers of algebraic cycles are integers
theorem intersection_decidable :
  ∀ (Z₁ Z₂ : ChowGroup), Decidable (intersection Z₁ Z₂ = 0) := by
  exact fun Z₁ Z₂ => inferInstance  -- ℤ has DecidableEq

-- Given a cycle, verifying it represents a given rational class
-- reduces to integer intersection number comparisons
theorem cycle_verification_BISH :
  ∀ (Z : ChowGroup) (q : H_Q),
    -- Checking cycle_class Z = q in H_Q is decidable
    -- because H_Q has DecidableEq
    Decidable (cycle_class Z = q) := by
  sorry -- Uses H_Q_decidableEq

-- Contrast: verifying a complex class is a cycle class requires LPO
-- (must check equality in H_C, not H_Q)
theorem cycle_verification_in_HC_requires_LPO :
  (∀ (Z : ChowGroup) (x : H_C),
    Decidable (rational_inclusion (cycle_class Z) = x)) → LPO_C := by
  sorry
```

### 7.2 Proof Strategy

Direct application of DecidableEq on H_Q (axiom) and decidability of
ℤ equality. The cycle class map lands in H_Q where equality is
decidable. The contrast theorem shows that if you ask the question
in H_C (the complex ambient space) instead of H_Q (the rational
lattice), you need LPO.

---

## 8. H5: The Nexus Theorem (H5_Nexus.lean)

### 8.1 Statement

```lean
-- The Hodge Conjecture is the NEXUS where algebraic descent
-- and Archimedean polarization interact.

-- A Hodge class: rational AND type (r,r)
def is_hodge_class (x : H_C) : Prop :=
  is_rational x ∧ is_hodge_type_rr x

-- The Hodge Conjecture: every Hodge class is algebraic
def hodge_conjecture : Prop :=
  ∀ (x : H_C), is_hodge_class x →
    ∃ (Z : ChowGroup), rational_inclusion (cycle_class Z) = x

-- WITHOUT the conjecture: detecting Hodge classes requires LPO + MP
-- (must verify both rationality AND Hodge type)
theorem hodge_class_detection_requires_LPO :
  (∀ (x : H_C), Decidable (is_hodge_class x)) → LPO_C := by
  sorry -- From H1 or H2

-- WITH the conjecture: Hodge classes are algebraic,
-- so verification reduces to cycle search (MP) + integer verification (BISH)
theorem hodge_conjecture_kills_LPO :
  hodge_conjecture →
  -- For any Hodge class x, there exists a cycle Z
  -- and verifying cycle_class Z represents x is BISH-decidable
  ∀ (x : H_C), is_hodge_class x →
    ∃ (Z : ChowGroup), Decidable (cycle_class Z = sorry) := by
  sorry

-- The nexus: polarization provides the (r,r) splitting,
-- algebraic descent provides the rational structure,
-- but ONLY the conjecture connects them.
-- Neither mechanism alone suffices.

-- Polarization alone: can split H_C into Hodge types (BISH via metric)
-- but cannot see ℚ-structure (H3_polarization_blind_to_Q)

-- Algebraic descent alone: can verify rational classes (H_Q has DecidableEq)
-- but cannot determine Hodge type without the metric

-- The Hodge Conjecture asserts: when BOTH conditions hold simultaneously,
-- the cause is algebraic geometry (a cycle).
```

### 8.2 Proof Strategy

This section is more structural than computational. The key formal
content is:

1. hodge_class_detection_requires_LPO: detecting Hodge classes
   in H_C requires LPO (from H1 or H2).
2. hodge_conjecture_kills_LPO: the conjecture converts the detection
   problem from LPO (testing in H_C) to MP + BISH (searching for
   cycles and testing in H_Q).
3. The nexus observation: polarization handles Hodge type, algebraic
   descent handles rationality, the conjecture asserts they're jointly
   controlled by cycles.

---

## 9. Assembly (Main.lean)

```lean
import P49_Hodge.Defs
import P49_Hodge.H1_HodgeTypeLPO
import P49_Hodge.H2_RationalityLPO
import P49_Hodge.H3_Polarization
import P49_Hodge.H4_CycleVerify
import P49_Hodge.H5_Nexus

-- Summary: The Hodge Conjecture calibrates at LPO+MP (abstract) / BISH+MP (geometric)
-- Polarization is AVAILABLE (u(ℝ) = 1) but blind to ℚ
-- The conjecture is the nexus where algebraic descent meets polarization

theorem hodge_calibration_summary :
  -- H1: Hodge type ↔ LPO
  ((∀ x, Decidable (is_hodge_type_rr x)) ↔ LPO_C)
  ∧
  -- H4: Cycle verification is BISH
  True  -- placeholder
  ∧
  -- H3: Polarization available
  True  -- placeholder
  := by
  exact ⟨hodge_type_iff_LPO, trivial, trivial⟩
```

---

## 10. Axiom Budget

Expected custom axioms: ~14
1. H_C as finite-dimensional ℂ-module
2. H_Q as finite-dimensional ℚ-module with DecidableEq
3. rational_inclusion : H_Q →ₗ H_C
4. hodge_projection_rr, hodge_projection_complement
5. hodge_decomposition, hodge_projections_complementary
6. hodge_riemann bilinear form
7. hodge_riemann_pos_def_on_primitive
8. ChowGroup with cycle_class and intersection
9. polarization_blind_to_Q (transcendence of periods)
10. rationality_test_requires_LPO (encoding axiom)

Target: ≤ 14 custom axioms, 0 sorries on proved theorems.

---

## 11. Relationship to Paper 45

**Reuses:** LPO equivalence proof pattern (C2 → H1), BISH decidability
pattern (C4 → H4)

**New beyond all previous papers:**
- H3 (polarization available BUT blind to ℚ) is unique to the Hodge
  setting. In Papers 45-47, polarization was blocked (u = 4). In Paper 48,
  polarization was available and useful (Néron-Tate). In Paper 49,
  polarization is available but INSUFFICIENT — it can split continuous
  space but cannot see rational structure. This is the nexus phenomenon.
- H5 (nexus theorem) shows that the Hodge Conjecture requires BOTH
  mechanisms simultaneously, unlike any previous paper where one
  mechanism sufficed.
- polarization_blind_to_Q connects to the Kontsevich-Zagier period
  conjecture, opening a door to future work on transcendence theory
  within the CRM framework.
