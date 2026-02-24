# Paper 62: Northcott Failure and the LPO Frontier
## Lean 4 Proof Strategy Document

### Overview

Paper 62 maps the sharp boundary between MP and LPO for mixed motives. The boundary is **algebraic representability of the Abel-Jacobi target**: if J²(X) is an abelian variety, Northcott transfers and decidability stays at MP. If J²(X) is a non-algebraic complex torus, Northcott fails and decidability escalates to LPO.

Main results:

1. **Theorem A (Northcott Transfer):** If Abel-Jacobi is an isomorphism onto an abelian variety, Northcott transfers to the cycle group. Logic stays at MP. (Cubic threefold test case.)
2. **Theorem B (Northcott Failure):** If the intermediate Jacobian is non-algebraic (CY3, h³·⁰ ≥ 1) or cycle group is unrepresentable (Mumford), Northcott fails. Bounded height contains infinitely many cycles.
3. **Theorem C (LPO Escalation — No Weak Northcott):** No intermediate condition ("weak Northcott") prevents the escalation. Filtration by degree: each graded piece is BISH, but quantifying over all degrees is LPO.
4. **Theorem D (Sharp Boundary):** The MP/LPO boundary is determined by the Hodge numbers: |p-q| ≤ 1 implies algebraic intermediate Jacobian implies Northcott implies MP. |p-q| ≥ 2 implies non-algebraic implies no Northcott implies LPO.
5. **Theorem E (Isolation Gap):** Abelian variety targets have computable isolation gaps (Néron-Tate + Baker's theorem). Non-algebraic torus targets lack isolation gaps. Northcott failure and isolation gap failure are dual.

### File Structure

```
Paper62_Northcott_LPO/
├── Basic/
│   ├── Decidability.lean        -- BISH, MP, LPO (import from Paper 61)
│   ├── AbelJacobi.lean          -- Abel-Jacobi map, intermediate Jacobian
│   └── NorthcottDef.lean        -- Northcott property, formal definition
├── Transfer/
│   ├── AbelianTarget.lean       -- AJ isomorphism onto abelian variety => Northcott
│   └── CubicThreefold.lean      -- Explicit: cubic threefold stays at MP
├── Failure/
│   ├── Mumford.lean             -- Mumford's theorem: p_g > 0 => CH_0 infinite-dim
│   ├── NonAlgebraicTorus.lean   -- CY3: J²(X) non-algebraic => no Northcott
│   └── GriffithsGroup.lean      -- Non-trivial Griffiths group => unrepresentable
├── NoWeakNorthcott/
│   ├── GradedBISH.lean          -- Each degree-d slice is BISH
│   └── QuantifyDegrees.lean     -- Quantifying over all d ∈ ℕ is LPO
├── Boundary/
│   ├── HodgeCriterion.lean      -- |p-q| ≤ 1 vs |p-q| ≥ 2 classification
│   └── IsolationGap.lean        -- Abelian => gap; non-algebraic => no gap
└── Main.lean                    -- Summary theorems, full hierarchy table
```

### Definitions

```lean
-- Basic/NorthcottDef.lean

/-- The Northcott property for a cycle group with height function:
    for any bound B, the set {z : ĥ(z) ≤ B} is finite. -/
structure NorthcottProperty where
  /-- For any height bound, there's an explicit finite count -/
  finite_bounded : ∀ (B : ℚ), ∃ (N : ℕ), True
  -- Abstractly: the preimage of [0, B] under ĥ is finite

/-- Northcott FAILS: for some bound B, bounded-height set is infinite -/
def NorthcottFails : Prop :=
  ∃ (B : ℚ), ∀ (N : ℕ), ∃ (cycles : Fin (N + 1) → Unit),
    True  -- there exist N+1 distinct cycles of height ≤ B, for any N
```

```lean
-- Basic/AbelJacobi.lean

/-- Classification of intermediate Jacobian targets -/
inductive AJTarget where
  | abelianVariety   -- J²(X) is an abelian variety (h^{3,0} = 0)
  | nonAlgebraic     -- J²(X) is a non-algebraic complex torus (h^{3,0} ≥ 1)
  | noAJMap          -- No well-defined Abel-Jacobi (higher K-theory)

/-- Hodge number criterion for target type -/
def hodgeDeterminesTarget (h30 : ℕ) : AJTarget :=
  if h30 = 0 then AJTarget.abelianVariety
  else AJTarget.nonAlgebraic

/-- Abel-Jacobi map is an isomorphism for certain threefolds -/
structure AJIsomorphism where
  target : AJTarget
  isIso : target = AJTarget.abelianVariety
  -- When target is abelian, AJ: CH²(X)_hom → J²(X) is an isomorphism
```

### Theorem A: Northcott Transfer via Abel-Jacobi

```lean
-- Transfer/AbelianTarget.lean

/-- If the Abel-Jacobi map is an isomorphism onto an abelian variety,
    then the Néron-Tate height on the abelian variety transfers to
    a height on the cycle group satisfying Northcott.
    
    Proof sketch:
    1. J²(X) is an abelian variety (hypothesis)
    2. AJ: CH²(X)_hom → J²(X) is an isomorphism (hypothesis)
    3. Néron-Tate height on J²(X) satisfies Northcott (classical)
    4. Pull back height via AJ⁻¹: height on CH²(X)_hom satisfies Northcott
    5. Because AJ is algebraic (parameterized by Fano surface),
       bounding Néron-Tate height bounds naive height of cycle representatives
    
    Key reference: Clemens-Griffiths (1972), Annals of Math 95, 281-356
    Bloch-Murre (1979), Compositio Math 39, 47-105 -/
theorem abelian_target_gives_northcott
    (aj : AJIsomorphism) :
    NorthcottProperty := by
  exact ⟨fun B => ⟨0, trivial⟩⟩  -- placeholder; content is the algebraic argument
```

```lean
-- Transfer/CubicThreefold.lean

/-- The cubic threefold X ⊂ P⁴: explicit verification.
    
    Data (Clemens-Griffiths 1972):
    - h^{3,0}(X) = 0 (cubic threefold is Fano)
    - J²(X) is a principally polarized abelian 5-fold
    - dim J²(X) = 5
    
    Data (Bloch-Murre 1979, Voisin 2012):
    - AJ: CH²(X)_hom → J²(X) is an isomorphism
    - The map is algebraic (parameterized by the Fano surface of lines)
    
    Conclusion: Northcott holds for CH²(X)_hom.
    Decidability: MP for rank ≥ 2 (same as abelian varieties).
    Gate to BISH: Lang's conjecture for abelian 5-folds. -/

def cubicThreefold_h30 : ℕ := 0

theorem cubic_threefold_target :
    hodgeDeterminesTarget cubicThreefold_h30 = AJTarget.abelianVariety := by
  native_decide

theorem cubic_threefold_stays_MP :
    -- Cubic threefold: Northcott holds, decidability is MP (not LPO)
    -- The LPO escalation does NOT occur
    NorthcottProperty := by
  exact abelian_target_gives_northcott ⟨_, rfl⟩
```

### Theorem B: Northcott Failure

```lean
-- Failure/Mumford.lean

/-- Mumford's theorem (1968, J. Math. Kyoto Univ.):
    For a smooth surface F with p_g(F) > 0,
    CH_0(F)_hom is "infinite-dimensional" —
    not parameterizable by a finite-dimensional algebraic variety.
    
    CRM consequence: bounded height does NOT imply finite cycle count.
    Northcott fails for 0-cycles on surfaces with p_g > 0. -/
axiom mumford_theorem (pg : ℕ) (hpg : pg > 0) :
    NorthcottFails

/-- For K3 surfaces: p_g = 1, so Mumford applies to CH²(X)_0.
    However: Bloch's conjecture predicts CH²(X)_0 is trivial over ℚ.
    Northcott failure is structural but may be vacuous over ℚ. -/
def k3_pg : ℕ := 1

theorem k3_mumford_applies : k3_pg > 0 := by native_decide
```

```lean
-- Failure/NonAlgebraicTorus.lean

/-- For a Calabi-Yau threefold X with h^{3,0} = 1:
    J²(X) = H³(X,ℂ)/(F²H³ + H³(X,ℤ)) is a complex torus
    but NOT an abelian variety (no algebraic polarization).
    
    Consequence: no algebraic Néron-Tate height on J²(X).
    Beilinson-Bloch height exists but cannot be tied to projective naive height.
    Bounded canonical height does not bound geometric degree.
    Northcott fails. -/
theorem cy3_northcott_fails (h30 : ℕ) (hh : h30 ≥ 1) :
    hodgeDeterminesTarget h30 = AJTarget.nonAlgebraic ∧ NorthcottFails := by
  constructor
  · simp [hodgeDeterminesTarget]; omega
  · exact mumford_theorem h30 (by omega)  
  -- NOTE: This is slightly sloppy — Mumford is about surfaces.
  -- For CY3, the argument is different: non-algebraic J² lacks Northcott.
  -- Lean agent should formalize the CY3 argument directly.
```

### Theorem C: No Weak Northcott

```lean
-- NoWeakNorthcott/GradedBISH.lean

/-- For fixed degree d, the set of cycles of height ≤ B AND degree ≤ d
    is finite (contained in a Chow variety, which is of finite type).
    Checking lattice membership within this finite set is BISH. -/
theorem fixed_degree_is_BISH (d : ℕ) (B : ℚ) :
    -- Decision: ∀ z with ĥ(z) ≤ B and deg(z) ≤ d, z ∈ ℤ-span(generators)
    -- is a finite conjunction of decidable predicates = BISH
    True := by
  trivial
```

```lean
-- NoWeakNorthcott/QuantifyDegrees.lean

/-- To verify lattice SATURATION (generators span the FULL lattice),
    must check all degrees d ∈ ℕ. This is:
    
    ∀ d ∈ ℕ, ∀ z with ĥ(z) ≤ B and deg(z) ≤ d, z ∈ ℤ-span(g₁,...,g_r)
    
    Each inner quantifier is BISH (Theorem: fixed_degree_is_BISH).
    The outer quantifier ∀ d ∈ ℕ has no a priori bound.
    
    This is a universal quantification over ℕ without stopping criterion.
    Constructively equivalent to LPO.
    
    KEY REDUCTION: Given f : ℕ → ℤ, define cycle z_d of degree d
    that lies in span iff f(d) = 0.
    Then (∀ d, z_d ∈ span) ⟺ (∀ d, f(d) = 0) ⟺ LPO. -/
theorem no_weak_northcott_saves_you :
    -- There is no condition weaker than Northcott but stronger than
    -- "no condition" that prevents the LPO escalation.
    -- Proof: reduce LPO to the saturation decision problem.
    ¬ (∃ (weakNorthcott : Prop),
        -- weakNorthcott is strictly weaker than Northcott
        -- but saturation under weakNorthcott avoids LPO
        True) := by
  sorry
  -- LEAN AGENT: The real proof is the explicit reduction.
  -- Construct: given f : ℕ → ℤ, build cycle z_d of degree d
  -- such that z_d ∈ ℤ-span(generators) ⟺ f(d) = 0.
  -- Then "all z_d in span" ⟺ "∀ d, f(d) = 0".
  -- The latter is exactly one disjunct of LPO.
  -- 
  -- The filtration argument:
  -- degree ≤ d slice is BISH (finite)
  -- degree ≤ d+1 slice is BISH (finite)
  -- ...
  -- but ∀ d, (degree ≤ d slice OK) has no stopping criterion
  -- 
  -- This is the MAIN NEW THEOREM of Paper 62.
  -- Formalize carefully as a reduction from LPO.
```

### Theorem D: The Sharp Boundary (Hodge Criterion)

```lean
-- Boundary/HodgeCriterion.lean

/-- The Sharp Boundary Theorem:
    
    The Hodge numbers of M determine the MP/LPO classification:
    
    |p - q| ≤ 1 for all nonzero h^{p,q}:
      → Intermediate Jacobian is an abelian variety
      → Abel-Jacobi transfers Northcott
      → Decidability: MP (with Lang gate to BISH)
    
    ∃ (p,q) with |p - q| ≥ 2 and h^{p,q} ≠ 0:
      → Intermediate Jacobian is non-algebraic complex torus
      → Northcott fails
      → Decidability: LPO
    
    Examples:
    - Elliptic curve: h^{1,0} = h^{0,1} = 1. |1-0| = 1 ≤ 1. MP.
    - Cubic threefold: h^{2,1} = h^{1,2} = 5, h^{3,0} = 0. |2-1| = 1 ≤ 1. MP.
    - CY3 (quintic): h^{3,0} = 1. |3-0| = 3 ≥ 2. LPO.
    - K3 surface CH¹: h^{1,1} = 20. |1-1| = 0 ≤ 1. MP.
    
    Reference: This criterion follows from the classical fact that
    Griffiths' intermediate Jacobian is an abelian variety iff
    the Hodge structure is of level ≤ 1 (all h^{p,q} = 0 for |p-q| ≥ 2).
    See: Griffiths, "Periods of integrals" (1968), 
    Griffiths-Harris, "Principles of Algebraic Geometry" Ch. 3. -/

/-- Hodge level: maximum |p - q| among nonzero h^{p,q} -/
def hodgeLevel (hodge_numbers : List (ℕ × ℕ × ℕ)) : ℕ :=
  hodge_numbers.foldl (fun acc (p, q, h) => 
    if h > 0 then max acc (if p ≥ q then p - q else q - p) else acc) 0

/-- Sharp boundary theorem -/
theorem sharp_boundary (hodge : List (ℕ × ℕ × ℕ)) :
    (hodgeLevel hodge ≤ 1 → True)  -- MP domain
    ∧ (hodgeLevel hodge ≥ 2 → True)  -- LPO domain
    := by
  exact ⟨fun _ => trivial, fun _ => trivial⟩
  -- LEAN AGENT: The real content is the chain:
  -- hodgeLevel ≤ 1 → J is abelian → Northcott → MP
  -- hodgeLevel ≥ 2 → J non-algebraic → no Northcott → LPO
  -- Formalize the chain, not just the endpoint.

-- Explicit examples
def ellipticCurve_hodge : List (ℕ × ℕ × ℕ) := [(1, 0, 1), (0, 1, 1)]
def cubicThreefold_hodge : List (ℕ × ℕ × ℕ) := [(2, 1, 5), (1, 2, 5)]
def quinticCY3_hodge : List (ℕ × ℕ × ℕ) := [(3, 0, 1), (2, 1, 101), (1, 2, 101), (0, 3, 1)]

theorem elliptic_is_MP : hodgeLevel ellipticCurve_hodge ≤ 1 := by native_decide
theorem cubic_is_MP : hodgeLevel cubicThreefold_hodge ≤ 1 := by native_decide
theorem quintic_is_LPO : hodgeLevel quinticCY3_hodge ≥ 2 := by native_decide
```

### Theorem E: Isolation Gap Duality

```lean
-- Boundary/IsolationGap.lean

/-- The isolation gap and Northcott failure are dual:
    
    Abelian variety J²(X):
    - Néron-Tate height is positive-definite (algebraic polarization)
    - Baker's theorem: linear forms in logarithms bounded away from 0
    - Computable isolation gap exists
    - Northcott holds
    
    Non-algebraic torus J²(X):
    - No algebraic positive-definite Riemann form
    - Periods evaluated by transcendental integration
    - Distinguishing period = 0 from period ≈ 0 requires exact real arithmetic
    - No computable isolation gap
    - Northcott fails
    
    Both failures stem from same root: J²(X) not being an abelian variety. -/
theorem isolation_gap_duality :
    -- Abelian target ↔ isolation gap exists ↔ Northcott holds
    -- Non-algebraic target ↔ no isolation gap ↔ Northcott fails
    True := by
  trivial
  -- LEAN AGENT: This is primarily a logical/structural theorem.
  -- The key formalization is:
  -- (1) Define "isolation gap" as ∃ ε > 0, ∀ nonzero x, ĥ(x) ≥ ε
  -- (2) Show: isolation gap + bounded height → finite set → Northcott
  -- (3) Show: no isolation gap → height can be arbitrarily small positive
  --     → bounded height region infinite → Northcott fails
```

### Main.lean Summary

```lean
-- Main.lean

import Paper62_Northcott_LPO.Transfer.CubicThreefold
import Paper62_Northcott_LPO.Failure.NonAlgebraicTorus
import Paper62_Northcott_LPO.NoWeakNorthcott.QuantifyDegrees
import Paper62_Northcott_LPO.Boundary.HodgeCriterion

/-- Paper 62 Summary: The Complete DPT Hierarchy for Mixed Motives
    
    The decidability of Ext¹(ℚ(0), M) is determined by THREE invariants:
    
    1. Analytic rank r = ord L(M, s₀)
    2. Hodge level ℓ = max |p-q| among nonzero h^{p,q}
    3. Effective Lang constant c(A)
    
    FULL HIERARCHY:
    
    | Rank | Hodge Level | Northcott | Logic | Gate to BISH        |
    |------|-------------|-----------|-------|----------------------|
    | r=0  | any         | —         | BISH  | —                    |
    | r=1  | ℓ ≤ 1       | Yes       | BISH  | —                    |
    | r≥2  | ℓ ≤ 1       | Yes       | MP    | Lang                 |
    | any  | ℓ ≥ 2       | No        | LPO   | Structurally blocked |
    
    The boundary between MP and LPO is the algebraicity of the
    intermediate Jacobian, determined by the Hodge level.
    
    Cubic threefold: ℓ = 1, stays at MP.
    CY3 (quintic): ℓ = 3, escalates to LPO.
    K3 (divisors): ℓ = 0, stays at MP.
    K3 (0-cycles): Mumford applies, but Bloch predicts trivial over ℚ.
-/
```

### Priority Notes for Lean Agent

1. **MAIN NEW THEOREM: No Weak Northcott (Theorem C).** The filtration-by-degree argument is the key contribution. Each degree-d slice is BISH, but ∀d is LPO. This needs the explicit reduction from LPO. Invest the most time here.

2. **Hodge level computation (Theorem D)** should be concrete. The `native_decide` on elliptic curve / cubic threefold / quintic CY3 Hodge numbers is the verification that the classification works on known examples.

3. **Theorem A (Northcott transfer)** is classical — the Lean content is the chain: AJ isomorphism + abelian target + Néron-Tate + classical Northcott → Northcott on cycle group. State this as a theorem with axioms for the classical inputs.

4. **Theorem B (Northcott failure)** has a subtlety: Mumford's theorem is about surfaces, but the CY3 argument is different (non-algebraic J²). Don't conflate them. Formalize separately.

5. **Import from Paper 61** — reuse BISH/MP/LPO definitions and the Lang gate theorem. Paper 62 extends Paper 61's hierarchy, doesn't replace it.

6. **The Clemens (1983) reference** needs careful handling. The claim is that the Griffiths group of a general quintic threefold is not finitely generated (Clemens, Publ. Math. IHÉS 58, 1983, pp. 19-38). This is about homological-mod-algebraic equivalence being infinite. It supports the non-representability claim but isn't identical to it.
