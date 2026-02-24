# Paper 51: The Constructive Archimedean Rescue in BSD
## Design Document

### Status: DESIGN PHASE (not yet in Lean formalization)

---

## 0. Honest Framing

The algorithms described here are not mathematically new. They are
the engines inside Cremona's mwrank, Magma, and SageMath, developed
by Cohen, Watkins, and Siksek in the 1990s and 2000s.

The novelty of Paper 51 is foundational and architectural. It formally
proves that what computational number theorists treat as a "heuristic
trick to make the computer halt" is a rigorous logical theorem: the
positive-definite Archimedean metric (u = 1) is the unique topological
modality that lowers the logical complexity of Diophantine equations
from MP (unbounded search) to BISH (bounded exhaustive search).

Paper 51 provides the axiom budget and dependency graph for the first
formally verified BSD solver in Lean 4.

---

## 1. Constructive Rank 0 Algorithm

### 1.1 The BISH Algorithm

Given E/ℚ of conductor N:

(a) Compute L(E,1) via the rapidly converging series:
    L(E,1) = 2 Σ (aₙ/n) exp(-2πn/√N)
    Truncation error after M terms bounded by incomplete gamma function.
    Use interval arithmetic. If L(E,1) ≠ 0, the interval eventually
    excludes 0. (If L(E,1) = 0, it loops forever — semi-decidability.)

(b) Once L(E,1) ≠ 0 certified, Kolyvagin's theorem guarantees
    E(ℚ) and Ш(E/ℚ) are finite.

(c) Output: "rank E(ℚ) = 0" with explicit bounds on |Ш| and
    E(ℚ)_tors via Lutz-Nagell (purely BISH).

### 1.2 Constructive Status of Kolyvagin's Argument

Kolyvagin's Euler system requires "Kolyvagin primes" ℓ where Frob_ℓ
is in specific conjugacy classes. Classically uses Chebotarev Density
Theorem (analytic, no search bound — MP).

CRM fix: the Effective Chebotarev Theorem (Lagarias-Odlyzko) gives
an explicit upper bound on the smallest such prime, converting MP
to bounded BISH search.

### 1.3 Precision Bound

Assuming the BSD formula:
  L(E,1) = Ω_E · |Ш| · ∏cₚ / |E(ℚ)_tors|²
  ≥ Ω_E / |E(ℚ)_tors|²
  ≥ Ω_E / 256  (by Mazur's torsion theorem)

The real period Ω_E is computable via AGM. So the algorithm needs
precision Ω_E / 512 to certify L(E,1) ≠ 0. The discrete skeleton
(Mazur's theorem) bounds the continuous analysis.

---

## 2. Constructive Rank 1 Algorithm

### 2.1 The Gross-Zagier Pipeline

If L(E,1) = 0 and L'(E,1) ≠ 0:

(a) Find Heegner field K = ℚ(√-D) with Heegner hypothesis
    (bounded BISH search in D)
(b) Compute Heegner point y_K via modular parametrization X₀(N) → E
(c) Gross-Zagier: L'(E,1) = c_GZ · ĥ(y_K)
(d) Positive-definiteness: L'(E,1) > 0 ⟹ ĥ(y_K) > 0 ⟹ y_K non-torsion
(e) Kolyvagin: rank ≤ 1
(f) Bounded search for exact generator within height bound

### 2.2 The Height Bound (The CRM Core)

This is the heart of the "Archimedean Rescue":

(a) Canonical height: ĥ(y_K) = L'(E,1) / c_GZ
    where c_GZ = 8π² ‖f‖² / (u² c_E² √D)

(b) Silverman's explicit bound (1990):
    -⅛ h(j) - 1/12 h(Δ) - 0.973 ≤ ĥ(P) - ½h(P) ≤ 1/12 h(j) + 1/12 h(Δ) + 1.07
    Let μ(E) be the computable absolute value of the lower bound.
    Then: h(y_K) ≤ 2ĥ(y_K) + 2μ(E)

(c) Explicit search space: the generator P_gen has
    x-coordinate p/q with:
    
    B(N, L'(E,1)) = exp( 2·L'(E,1)/c_GZ + 2μ(E) )
    
    |p|, |q| ≤ B

(d) The unbounded Diophantine search (MP) is squashed into a
    finite grid of size O(B²). This is BISH-decidable.

### 2.3 What Makes This Work (CRM Analysis)

The conversion MP → BISH requires THREE ingredients:
1. Gross-Zagier formula (connects analytic to algebraic)
2. Positive-definiteness of ĥ (CRM Axiom 3, u(ℝ) = 1)
3. Silverman's explicit height difference bound

Without positive-definiteness, the height bound doesn't exist.
Over ℚ_p (u = 4), ĥ_p can be zero for non-torsion points
(the p-adic height is NOT positive-definite). This is why
p-adic BSD has the exceptional zero pathology: the MP → BISH
conversion fails because the metric cannot bound the search.

---

## 3. Lean 4 Formalization Plan

### 3.1 Mathlib Infrastructure

Available:
- Elliptic curves over ℚ (Mathlib.AlgebraicGeometry.EllipticCurve)
- Basic height functions (naive)
- Interval arithmetic (partial)
- Finset API

NOT available (must axiomatize):
- L-functions
- Modular parametrization / Heegner points
- Néron-Tate canonical height properties
- Kolyvagin's Euler system
- Gross-Zagier formula

### 3.2 Axiom Budget

AXIOMATIZE (LPO-dependent, unformalizeable today):
1. Modularity of E/ℚ (Wiles-Taylor-Breuil-Conrad-Diamond)
2. L'(E,1) exists and is computable
3. Gross-Zagier formula: L'(E,1) = c_GZ · ĥ(y_K)
4. Kolyvagin's theorem: ĥ(y_K) > 0 ⟹ rank ≤ 1

PROVE (BISH, sorry-free target):
5. Silverman's height difference bound: |ĥ(P) - ½h(P)| ≤ μ(E)
6. Bounded naive height ⟹ Finset of rational points
7. Height bound B(N, L'(E,1)) is computable
8. The search space is finite (Finset)
9. If generator exists in Finset, it is findable (decidable)

### 3.3 File Structure

```
P51_BSD/
├── SilvermanBounds.lean   -- ~1000 lines, the engine
│   Height difference bounds from Weierstrass data
│   Explicit μ(E) computation
│   Target: 0 sorries
├── SearchSpace.lean       -- ~200 lines
│   Bounded height → Finset
│   Enumeration of rational points below bound
│   Target: 0 sorries
├── BSDAxioms.lean         -- ~100 lines
│   Axiom class quarantining LPO-dependent data
│   Gross-Zagier, Kolyvagin, modularity
├── ConstructiveBSD.lean   -- ~300 lines
│   Main theorem: axioms + Silverman → finite search
│   Target: 0 sorries (modulo axiom class)
└── Main.lean              -- Assembly
```

### 3.4 Main Theorem Signature

```lean
class BSDAxioms (E : EllipticCurve ℚ) where
  L_prime_1 : ℝ
  c_GZ : ℝ
  heegner_height : ℝ  -- ĥ(y_K)
  gross_zagier : L_prime_1 = c_GZ * heegner_height
  kolyvagin : heegner_height > 0 → E.MordellWeilRank = 1

theorem bsd_rank_one_search_bounded
    (E : EllipticCurve ℚ) [BSDAxioms E]
    (h_deriv : BSDAxioms.L_prime_1 E > 0) :
    ∃ (B : ℕ) (S : Finset (ℚ × ℚ)),
      (∀ P ∈ E.rationalPoints,
        P.isGenerator → P.naiveHeight ≤ B) ∧
      S.card < ∞ := by
  -- From Gross-Zagier + positive-definiteness + Silverman
  sorry -- Target: fill with actual proof
```

---

## 4. Achievable First Milestone

The entire chain is too long for Paper 51 alone. The first
achievable, independently publishable milestone:

**"Formal Verification of Silverman's Height Difference Bounds
for Elliptic Curves in Lean 4"**

This has NEVER been formally verified in any proof assistant.
It relies purely on explicit algebraic geometry: Weierstrass
coordinates, j-invariant, discriminant, real absolute values.
No L-functions, no modular forms, no Euler systems.

Estimated: 1000–1500 lines of Lean 4, 2–4 weeks.
Dependencies: Mathlib elliptic curve API + real analysis.

This is the mathematical engine that makes the search space
finite. Once verified, it becomes infrastructure for any future
BSD formalization.

---

## 5. Novelty Assessment

**Mathematically:** The algorithms recover Cremona/Watkins/Siksek.
CRM adds the logical dependency graph, not new number theory.

**Foundationally:** The "height bound converts MP to BISH"
observation is novel in formal logic and reverse mathematics.
Traditional reverse mathematics (Simpson, Friedman) studies
classical analysis. CRM pioneers reverse mathematics for
arithmetic geometry, proving the Archimedean metric is the
exact logical modality lowering complexity from Π₁⁰ (unbounded
search) to Δ₀ (bounded verification).

**For formalization:** Paper 51 is the master architecture
document for a Lean 4 BSD project. It proves that the vast
unformalizable analytic literature interfaces with discrete
type theory through exactly one chokepoint: the real-valued
bound on the Archimedean polarization. Everything above the
chokepoint is axiomatized. Everything below is proved.

**Honest verdict:** Paper 51 is a formalization exercise dressed
in CRM language — but that framing is precisely what makes it
architecturally significant. It bridges the gap between deep
analytic theorems (Langlands/Gross-Zagier) and executable
formal verification (Lean 4/Mathlib) by identifying the exact
axiom/theorem boundary.
