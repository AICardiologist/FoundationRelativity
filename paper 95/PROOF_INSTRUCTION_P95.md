# Paper 95 — Proof Instruction

## Working Title

**The BSD Squeeze: CRMLint Decomposition of the Gross-Zagier-Kolyvagin Proof**

Paper 95, Constructive Reverse Mathematics Series.
Fourteenth CRMLint Squeeze application.

---

## 0. Strategic Position

Papers 48 and 51 were *diagnostic*: they calibrated the BSD *conjecture* (BSD = LPO for zero-testing; Archimedean rescue converts MP to BISH for generator search). They did not touch the *proof*.

Paper 95 is *generative*: it applies the CRMLint Squeeze protocol to the actual **proof** of BSD for analytic rank ≤ 1 — the Gross-Zagier formula and Kolyvagin's Euler system. The goal is a BISH/CLASS decomposition of the proof pipeline, verified in Lean 4, identifying the Classical Boundary Nodes and measuring the constructive content of the only proven case of a Clay Millennium Problem.

### Why Now

Paper 94 (Normal Function Squeeze) built the CY3 bridge: it showed the BISH/CLASS bifurcation pattern (detection BISH, existence CLASS) transfers from abelian varieties to Calabi-Yau threefolds via normal functions and inhomogeneous Picard-Fuchs equations. The BSD proof uses the *same* technology:

| Paper 94 (CY3) | Paper 95 (BSD) |
|---|---|
| Mirror quintic X₅ | Elliptic curve E/Q |
| Walcher's RP³ Lagrangian | Heegner cycle on Kuga-Sato |
| 4th-order PF operator L | 2nd-order PF operator (Legendre, Paper 80) |
| Source: (15/8)√z | Source: Heegner normal function |
| Detection: algebraic source = BISH | Detection: modular symbols for L'(E,1) = BISH |
| Existence: Abel-Jacobi + Baire = CLASS | Existence: Kolyvagin Euler system = CLASS |

The parallel is exact. Paper 95 completes the cycle: Hodge → CY3 → BSD.

### Connection to Prior Infrastructure

- **Paper 80** (DOI: 10.5281/zenodo.18791985): Legendre PF operator t(1-t)D² + (1-2t)D - 1/4 formalized over Q(t). Griffiths pole reduction verified by `ring`. The *same* operator governs the period integral of E_t: y² = x(x-1)(x-t). Paper 95 reuses this operator with an inhomogeneous source.
- **Paper 94** (DOI pending): Inhomogeneous PF framework. Walcher's equation L·T(z) = (15/8)√z verified algebraically. Recurrence coefficients verified by `norm_num`. Paper 95 follows the identical pattern: the Heegner normal function satisfies an inhomogeneous PF equation whose source term is algebraic.
- **Paper 51** (DOI: 10.5281/zenodo.18732168): BSDRankOneData structure, Silverman bounds, search space finiteness. Paper 95 extends this with the proof decomposition.
- **Paper 48** (DOI: 10.5281/zenodo.18683400): LPO ↔ zero-testing, regulator positivity in BISH, p-adic contrast.

---

## 1. The Classical Proof to be Squeezed

### 1.1 Statement (Gross-Zagier-Kolyvagin, 1986-1990)

Let E/Q be an elliptic curve of analytic rank ≤ 1. Then:
- rank E(Q) = ord_{s=1} L(E,s)
- Sha(E/Q) is finite

The proof pipeline has five stages:

**Stage 1: Modularity.** E/Q is modular (Wiles-Taylor-BCDT). There exists f ∈ S₂(Γ₀(N)) with L(f,s) = L(E,s).

**Stage 2: Heegner point construction.** Choose imaginary quadratic K = Q(√-D) satisfying the Heegner hypothesis (all primes dividing N split in K). Construct Heegner point y_K ∈ E(K) via the modular parametrization φ: X₀(N) → E applied to the CM point τ_K ∈ X₀(N)(H_K).

**Stage 3: Gross-Zagier formula.**
L'(E,1) = c_GZ · ĥ(y_K)
where c_GZ = 8π²‖f‖²/(u²c_E²√D) > 0. Proof uses Rankin-Selberg convolution of f with a theta series.

**Stage 4: Kolyvagin's Euler system.** If y_K is non-torsion (guaranteed by L'(E,1) ≠ 0 via Gross-Zagier), then:
- rank E(Q) = 1
- Sha(E/Q) is finite, with explicit order bound

Uses derivative classes c_ℓ ∈ H¹(K, E[p]) for Kolyvagin primes ℓ (primes where Frob_ℓ has specific properties). Chebotarev density guarantees existence of such primes.

**Stage 5: Generator recovery.** Silverman height bounds + Gross-Zagier height value → finite search (Paper 51).

### 1.2 Test Case: Curve 37a1

y² + y = x³ - x, conductor N = 37, analytic rank 1.

Known data:
- L'(37a1, 1) = 0.3059997738... (computable via modular symbols)
- Heegner discriminant: D = 3 (smallest satisfying Heegner hypothesis for N = 37)
- Heegner point: y_K = (0, 0) ∈ E(Q) (rational, not just defined over K)
- ĥ(y_K) = 0.0511114082...
- Regulator = ĥ(y_K) = 0.0511114082... (rank 1, single generator)
- Sha(37a1/Q) trivial
- Tamagawa number c₃₇ = 1
- E(Q)_tors = trivial
- Generator: P = (0,0), since (0,-1) = -P

This is the simplest possible test case: rank 1, trivial torsion, trivial Sha, prime conductor.

---

## 2. CRMLint Squeeze Decomposition

### 2.1 X-Ray: BISH Components

**(B1) Modular symbol computation of L'(E,1).**
The modular symbol ⟨f, {0,∞}⟩ = ∫₀^{i∞} f(τ)dτ is a finite algebraic computation over Q. For 37a1:
- The space S₂(Γ₀(37)) is 2-dimensional
- The newform f is identified by Hecke eigenvalues a_p ∈ Z
- L'(E,1) = -2 Re(∑ₙ aₙ/n · e^{-2πn/√37}) converges rapidly
- The key point: the leading term of L'(E,1)/Ω is a rational number times a period. The *rationality* of the algebraic part is BISH.

**Lean strategy:** Verify that aₚ for p ≤ 100 satisfy the Hecke recurrence. Verify L'(E,1)/Ω ∈ Q via `norm_num`. This is the BSD analog of Paper 94's disk count b₀ = 30.

**(B2) Heegner discriminant search.**
Finding D with Heegner hypothesis: for each D = 3, 4, 7, 8, 11, ..., check whether all primes dividing N = 37 split in Q(√-D). Since 37 is prime, need (-D/37) = 1 (Legendre symbol). For D = 3: (-3/37) = (37 mod 3) ... need 37 ≡ 1 mod 3, which holds (37 = 12·3 + 1). Bounded decidable search. Pure BISH.

**Lean strategy:** Verify `(-3 : ZMod 37).IsSquare` by `native_decide` or `decide`.

**(B3) Heegner point computation.**
The modular parametrization φ: X₀(37) → E is an algebraic map. The CM point τ_K = (-1+√-3)/2 in the upper half-plane corresponds to a point on X₀(37)(H_3) where H_3 = Q(√-3) is the Hilbert class field (h(-3) = 1, so H_3 = K). The image y_K = φ(τ_K) has coordinates in Q (since h(-3) = 1 and the curve has trivial torsion over Q). Explicit computation: y_K = (0, 0).

**Lean strategy:** Verify that (0,0) lies on y² + y = x³ - x by `norm_num`: 0² + 0 = 0³ - 0 ↔ 0 = 0. Verify ĥ(0,0) > 0 (axiomatize the Néron-Tate value, verify positivity).

**(B4) Silverman height bounds.**
|ĥ(P) - ½h(P)| ≤ μ(E). For 37a1, μ(37a1) is computable from j-invariant and minimal discriminant. Already formalized in Paper 51 (HeightBounds.lean). Pure BISH.

**(B5) Finite search space.**
h(P) ≤ 2ĥ(y_K) + 2μ(E) → |p|, |q| ≤ B = ⌈exp(2ĥ(y_K) + 2μ(E))⌉. Already formalized in Paper 51 (SearchSpace.lean). Pure BISH.

**(B6) Tamagawa numbers and torsion.**
c₃₇ = 1 (37a1 has good reduction away from 37, and split multiplicative reduction at 37 with c₃₇ = 1). E(Q)_tors = {O} (trivial, by Lutz-Nagell or by checking small multiples). Both finite decidable computations. Pure BISH.

**(B7) Effective Chebotarev bound.**
The effective Chebotarev theorem (Lagarias-Odlyzko 1977, with GRH: Bach 1990) gives an explicit upper bound B_Cheb on the smallest Kolyvagin prime ℓ. For a given Galois representation, the smallest ℓ with Frob_ℓ in a specified conjugacy class satisfies ℓ ≤ c · (log disc)² under GRH. This converts the Kolyvagin prime existence from CLASS (Chebotarev density) to BISH (bounded search).

**Lean strategy:** Axiomatize the effective Chebotarev bound. Verify for 37a1 that specific small primes (ℓ = 2, 3, 5, ...) satisfy the Kolyvagin condition by `native_decide`.

**(B8) PF operator verification.**
The Legendre PF operator t(1-t)D² + (1-2t)D - 1/4 from Paper 80, specialized to the modular curve parameter. The modular symbol integral satisfies this ODE. Algebraic identity verification by `ring`. Already formalized.

### 2.2 X-Ray: CLASS Components

**(C1) Analytic continuation of L(E,s).**
The functional equation L(E,s) = w·N^{1-s}·(2π)^{2s-2}·Γ(2-s)/Γ(s)·L(E,2-s) requires complex analysis (Γ-function, contour integration). Irreducibly CLASS: the Γ-function is a transcendental object over C, and the functional equation is proven via Mellin transform (integral over R⁺).

**CRM classification:** CLASS. Cannot be eliminated — needed to define L'(E,1).

**(C2) Rankin-Selberg integral in Gross-Zagier proof.**
The Gross-Zagier formula is proven by computing both sides as the central value of a Rankin-Selberg convolution L(f⊗θ_K, s) at s = 1. This involves:
- Eisenstein series E(τ,s) on GL₂ (analytic continuation, CLASS)
- Petersson inner product ⟨f, f⟩ (integration over fundamental domain, CLASS)
- Local height computations at archimedean and non-archimedean places (archimedean: CLASS via Green's functions on Riemann surfaces; non-archimedean: BISH via intersection theory on regular models)

**CRM classification:** CLASS. The archimedean local heights are irreducibly CLASS. The non-archimedean local heights are algebraic (intersection multiplicities on the Néron model) and descend to BISH.

**(C3) Chebotarev density theorem (non-effective form).**
The full Chebotarev density theorem states that Frobenius elements are equidistributed in conjugacy classes. Uses PNT for Dedekind zeta functions (CLASS). However, Paper 95 replaces this with the effective version (B7), so this CLASS input is *excised*.

**(C4) Kolyvagin's local duality and Selmer bounding.**
The heart of Kolyvagin's argument: derivative classes c_ℓ + local Tate duality → bound on Selmer groups → bound on Sha. The local duality theorem (Tate) requires:
- Local class field theory (algebraic, BISH after axiomatization)
- Poitou-Tate exact sequence (homological, requires countable choice for direct limits)
- Shafarevich-Tate group finiteness (from the Selmer bound, but the bound itself requires...)

**CRM classification:** Mixed. The cohomological algebra (cup products, Galois cohomology exact sequences) is BISH once the coefficient modules are decided. The passage from "Selmer group is finite" to "Sha is finite with explicit bound" requires Cassels' pairing (symmetric, but the symmetry proof uses global duality = CLASS).

**(C5) Abel-Jacobi integration (if normal function approach used).**
If Paper 95 connects to Paper 94's normal function framework: the Abel-Jacobi map AJ: CH²(X)_hom → J²(X) involves integration of differential forms over topological cycles. Irreducibly CLASS.

### 2.3 Expected Score

| Component | Count | Classification |
|---|---|---|
| B1: Modular symbol rationality | 3 sub-results | BISH |
| B2: Heegner discriminant | 1 | BISH |
| B3: Heegner point verification | 2 | BISH |
| B4: Silverman bounds | 2 (from P51) | BISH |
| B5: Finite search space | 2 (from P51) | BISH |
| B6: Tamagawa + torsion | 2 | BISH |
| B7: Effective Chebotarev | 1 | BISH (conditional on GRH) |
| B8: PF operator | 1 (from P80) | BISH |
| **BISH total** | **~14** | |
| C1: Analytic continuation | 1 | CLASS |
| C2: Rankin-Selberg / Gross-Zagier proof | 3 | CLASS |
| C4: Kolyvagin local duality | 2 | CLASS |
| **CLASS total** | **~6** | |
| **BISH percentage** | **~70%** | |

This is between the Hodge Squeeze (90% BISH, P90 Theorem B) and the Markman audit (44% BISH, P91). The gap is because BSD has deeper analytic inputs than the Hodge Squeeze but more algebraic content than Markman's K3 proof.

---

## 3. The Four Theorems

### Theorem A: The Modular Symbol Core

**Statement:** For E = 37a1, the algebraic part of L'(E,1) — specifically, the leading coefficient of the modular symbol expansion — is a rational number verifiable by `norm_num`. The Hecke eigenvalues a_p for p ≤ 100 satisfy the multiplicative recurrence a_{mn} = a_m·a_n (for gcd(m,n)=1) and a_{p²} = a_p² - p, verifiable by `native_decide`.

**Lean strategy:**
```lean
-- Hecke eigenvalues for 37a1
def a : ℕ → ℤ
| 2 => -2 | 3 => -3 | 5 => -2 | 7 => -2 | 11 => 0
| 13 => 5 | 17 => -2 | 19 => 0 | 23 => -1 | 29 => 6
| 31 => -4 | 37 => -1 | 41 => 9 | 43 => -3 | 47 => -8
| _ => 0  -- extend as needed

-- Verify multiplicativity
theorem hecke_mult_2_3 : a 6 = a 2 * a 3 := by native_decide
-- Verify Hecke recurrence at p²
theorem hecke_sq_2 : a 4 = a 2 ^ 2 - 2 := by native_decide
```

**CRM classification:** BISH. Pure finite arithmetic.

### Theorem B: The Gross-Zagier-Kolyvagin Squeeze

**Statement:** The Gross-Zagier-Kolyvagin proof of BSD for analytic rank ≤ 1 decomposes into N_BISH + N_CLASS components, where:
- The BISH components are: modular symbol computation, Heegner discriminant search, Heegner point construction, Silverman bounds, finite search, Tamagawa/torsion computation, effective Chebotarev, non-archimedean local heights
- The CLASS components are: analytic continuation of L(E,s), Rankin-Selberg convolution (archimedean local heights, Petersson norm, Eisenstein series), Cassels pairing symmetry, Poitou-Tate sequence

The BISH components are verified in Lean 4. The CLASS components are quarantined as axiom stubs.

**Lean strategy:** Structure `BSDSqueezeData` extending Paper 51's `BSDRankOneData` with:
```lean
structure BSDSqueezeData (E : ECData) extends BSDRankOneData E where
  -- Modular symbol data
  hecke_eigenvalues : ℕ → ℤ
  hecke_multiplicative : ∀ m n, Nat.Coprime m n →
    hecke_eigenvalues (m * n) = hecke_eigenvalues m * hecke_eigenvalues n
  -- Heegner data
  heegner_disc : ℤ
  heegner_hypothesis : IsSplitAt E.N heegner_disc
  -- Kolyvagin data (axiomatized CLASS)
  kolyvagin_bound : ℕ  -- effective Chebotarev bound
  selmer_bounded : SelmerRank E ≤ 1  -- consequence of Euler system
```

### Theorem C: The Detection/Existence Bifurcation

**Statement:** The BISH/CLASS split in the BSD proof follows the same pattern as Paper 94 (Normal Function Squeeze) and the entire Hodge arc (Papers 84-93):

- **Detection** (is the Heegner point non-torsion? is L'(E,1) ≠ 0?) is BISH: modular symbols compute L'(E,1) as a finite rational linear combination of periods; the Gross-Zagier formula converts this to ĥ(y_K) > 0; positive-definiteness (from u(R) = ∞) gives the constructive witness.

- **Existence/Abundance** (does the Euler system produce enough derivative classes? is Sha bounded?) is CLASS: Chebotarev density for Kolyvagin primes, Cassels pairing for Sha finiteness.

**This is the BSD instance of CRM Discovery #32** (Paper 94): detection of arithmetic objects by algebraic source terms is BISH; existence of the objects themselves requires CLASS.

### Theorem D: The Inhomogeneous PF Connection

**Statement:** The Heegner normal function ν_K on the modular curve X₀(N) satisfies an inhomogeneous Picard-Fuchs equation whose structure parallels Walcher's equation in Paper 94:

| | Paper 94 (Mirror quintic) | Paper 95 (BSD) |
|---|---|---|
| Base | ψ-parameter space P¹ | Modular curve X₀(N) |
| PF operator | L₄ (4th order, CDGP) | L₂ (2nd order, Legendre-type) |
| Source term | (15/8)√z (algebraic) | Heegner kernel Θ_K (algebraic) |
| Leading coefficient | b₀ = 30 (disk count) | ĥ(y_K)·c_GZ (Gross-Zagier) |
| Detection | Source algebraic → BISH | Modular symbols → BISH |
| Existence | Abel-Jacobi → CLASS | Euler system → CLASS |

For 37a1: the PF operator is the Legendre operator from Paper 80, specialized at the CM point corresponding to D = 3. The inhomogeneous source is the Heegner kernel function, whose algebraicity is the content of the Gross-Zagier formula (the fact that the source is determined by a finite computation on modular symbols).

**Lean strategy:** Reuse Paper 80's `legendre_pf_operator` and Paper 94's `InhomogPFData` structure. Verify that the specialized recurrence coefficients at the 37a1 CM point satisfy the Gross-Zagier compatibility by `norm_num`.

---

## 4. Lean 4 Engineering Specification

### 4.1 Bundle Structure

```
paper 95/P95_BSDSqueeze/
├── Papers.lean                 -- root module
├── Papers/
│   ├── Defs.lean              -- ECData for 37a1, Hecke eigenvalue table
│   ├── ModularSymbols.lean    -- Theorem A: Hecke verification, rationality
│   ├── HeegnerData.lean       -- B2+B3: discriminant search, point verification
│   ├── GrossZagierAxiom.lean  -- CLASS axiom stubs for GZ formula
│   ├── KolyvaginAxiom.lean    -- CLASS axiom stubs for Euler system
│   ├── SilvermanBounds.lean   -- B4: reuse/extend Paper 51 infrastructure
│   ├── FiniteSearch.lean      -- B5: reuse Paper 51 infrastructure
│   ├── PFConnection.lean      -- Theorem D: inhomogeneous PF (reuse P80+P94)
│   ├── SqueezeAudit.lean      -- Theorem B: CRM decomposition assembly
│   └── Main.lean              -- Assembly, #print axioms
├── lakefile.lean
└── lean-toolchain             -- leanprover/lean4:v4.29.0-rc2
```

### 4.2 Estimated Scope

- ~600 lines Lean 4
- ~15 verified theorems
- 0 sorry
- 0 Classical.choice in constructive path
- Reuses: Paper 51 structures, Paper 80 PF operator, Paper 94 inhomogeneous framework

### 4.3 Python CAS Support

A companion `solve_bsd_37a1.py` script should:
1. Compute Hecke eigenvalues a_p for 37a1 up to p = 100 using SageMath/SymPy
2. Verify modular symbol rationality: L'(37a1,1)/Ω = rational
3. Compute Silverman's μ(37a1) from the minimal Weierstrass model
4. Compute the effective Chebotarev bound for 37a1 and identify small Kolyvagin primes
5. Emit all constants as Lean 4 definitions

---

## 5. Anticipated Difficulties

### 5.1 Difficulty: Gross-Zagier Formula Depth

**Problem:** The Gross-Zagier formula is proven via Rankin-Selberg convolution involving Eisenstein series E(τ,s), Petersson inner products, and archimedean local height computations. The proof spans 100+ pages (Gross-Zagier 1986) and involves deep complex analysis. Cannot formalize; must axiomatize.

**Mitigation:** The CRMLint Squeeze does not require formalizing the proof. It requires:
(a) Axiomatizing the *statement* L'(E,1) = c_GZ · ĥ(y_K) with c_GZ > 0
(b) Verifying the *algebraic consequences* (height bound, search finiteness) in BISH
(c) Classifying the axiom as CLASS in the CRM audit

This is exactly the pattern from Paper 94 (Walcher's equation axiomatized, algebraic consequences verified) and Paper 51 (Gross-Zagier axiomatized via BSDRankOneData).

### 5.2 Difficulty: Kolyvagin Formalization

**Problem:** Kolyvagin's Euler system is a sophisticated piece of arithmetic involving:
- Galois cohomology (H¹(K, E[p]) for varying K, p)
- Local Tate duality (local-global principle for Selmer groups)
- Chebotarev density (existence of Kolyvagin primes)
- Inductive construction of derivative classes

**Mitigation:** Axiomatize the *conclusion*: "If y_K non-torsion then rank ≤ 1 and #Sha < ∞." The CRM audit classifies the specific ingredients that make this CLASS:
- Chebotarev density (existence) → CLASS, but excisable via effective version (B7)
- Tate local duality (symmetry of Cassels pairing) → CLASS, not excisable
- Cohomological exact sequences → BISH once coefficients are decided

Partial excision: effective Chebotarev replaces one CLASS input with BISH. The remaining CLASS inputs (local duality, Cassels pairing) are irreducible.

### 5.3 Difficulty: Connecting P80 PF to BSD

**Problem:** Paper 80 formalized the Legendre PF operator for the family y² = x(x-1)(x-t). The 37a1 curve y² + y = x³ - x has a different Weierstrass model. The PF connection requires transforming between models.

**Mitigation:** The isomorphism between y² + y = x³ - x and the Legendre form is:
- Complete the square: y² + y = x³ - x → (y + 1/2)² = x³ - x + 1/4
- Substitute Y = y + 1/2: Y² = x³ - x + 1/4 = (x - 1/2)(x² + x/2 - 1/2)
- This is a short Weierstrass form, not Legendre. The Legendre parametrization comes via the modular parameter on X₀(37), not directly from the Weierstrass model.

**Alternative approach:** Work with the modular curve directly. The universal elliptic curve over X₀(37) has a 2nd-order PF operator whose coefficients are rational functions on X₀(37). The Heegner CM point is an algebraic point on X₀(37). The PF operator specialized at this point gives a constant-coefficient ODE (since the CM point is a fixed point of the Galois action). This specialization is analogous to Paper 92's Zariski Grid Specialization: evaluate the PF operator at a concrete algebraic point and verify by `norm_num`.

### 5.4 Difficulty: Modular Symbol Computation in Lean

**Problem:** Computing L'(E,1) via modular symbols requires:
- The Manin symbol basis for S₂(Γ₀(37))
- Hecke operator action
- Period integrals ∫ f(τ)dτ along paths in H

The period integrals are CLASS (complex integration). The algebraic part (Hecke action on a finite-dimensional Q-vector space) is BISH.

**Mitigation:** Separate the computation into:
1. **Hecke eigenvalue table** (BISH): a_2 = -2, a_3 = -3, a_5 = -2, ... — finite data, verified by `native_decide`
2. **Multiplicativity and recurrence** (BISH): a_{mn} = a_m · a_n for (m,n)=1, verified by `native_decide`
3. **Period ratio** (CLASS axiom stub): Ω⁺ = 2.993... and L'(E,1)/Ω⁺ ∈ Q — axiomatize the rationality
4. **Convergence of L-series** (CLASS axiom stub): the rapidly converging series for L'(E,1) converges

This gives the BISH/CLASS decomposition of the modular symbol computation: the algebraic part (Hecke eigenvalues, recurrence, rationality) is BISH; the analytic part (period integral, convergence) is CLASS.

### 5.5 Difficulty: What Is Novel?

**Problem:** The underlying mathematics is classical (Gross-Zagier 1986, Kolyvagin 1988-1990, Cremona algorithms 1990s). We cannot claim new number theory.

**What is novel:**
1. The CRM decomposition of the Gross-Zagier-Kolyvagin proof — never done before
2. The identification of the same detection/existence bifurcation pattern found in Paper 94 (CY3) and Papers 84-93 (Hodge)
3. The connection to the Picard-Fuchs inhomogeneous framework (linking BSD to the Hodge arc via normal functions)
4. Lean 4 verification of the BISH core — first formal verification of any component of the BSD proof pipeline beyond Paper 51
5. The measurement: BSD proof is ~70% BISH, placing it between the Hodge Squeeze (90%) and Markman (44%), and establishing the CRM "cost" of a Clay Millennium Problem proof

---

## 6. LaTeX Writing Specification

### 6.1 Structure (following paper_format_guide.md)

1. **Title:** "The BSD Squeeze: CRMLint Decomposition of the Gross-Zagier-Kolyvagin Proof (Paper 95, Constructive Reverse Mathematics Series)"
2. **Abstract:** 150 words. State: GZK proof decomposes into ~14 BISH + ~6 CLASS. Test case 37a1. Lean 4 verified. Detection/existence bifurcation matches P94.
3. **Introduction (2-3pp):** Theorems A/B/C/D. CRM primer (brief, cite earlier papers). State of art: no prior CRM audit of BSD proof. Atlas fit: this is the BSD instance of the universal bifurcation pattern.
4. **Preliminaries (1p):** Modular symbols, Heegner points, Gross-Zagier formula statement, Kolyvagin statement. Definitions only, no proofs.
5. **Main Results (5-8pp):**
   - §3.1 Theorem A: Modular Symbol Core (Hecke eigenvalues, rationality)
   - §3.2 Theorem B: GZK Squeeze (full BISH/CLASS decomposition)
   - §3.3 Theorem C: Detection/Existence Bifurcation
   - §3.4 Theorem D: Inhomogeneous PF Connection
6. **CRM Audit (1p):** Classification table. What descends: generator search from MP to BISH. Where: L'(E,1) detection from CLASS to BISH via modular symbols. CBN: Rankin-Selberg integral.
7. **Formal Verification (2-3pp):** Lean file structure, axiom inventory, `#print axioms` output, key code snippets.
8. **Discussion (1p):** Connection to P48/P51 (diagnostic → generative). Connection to P94 (CY3 bridge). The 70% figure and what it means.
9. **Conclusion (0.5p):** First CRM audit of a Millennium Problem proof. The detection/existence pattern is universal.
10. **Acknowledgments:** AI disclosure, Mathlib citation.
11. **References (15-30):** Gross-Zagier, Kolyvagin, Cremona, Silverman, Wiles-Taylor, Mazur-Tate-Teitelbaum, Lagarias-Odlyzko (effective Chebotarev), Papers 48, 51, 80, 87, 90, 94, CRM Format Guide.

### 6.2 Figure

At least one TikZ figure: the **BSD Squeeze Pipeline Diagram** showing the five stages with BISH (green) and CLASS (red) coloring. Similar to Paper 51's dependency graph but extended to include Kolyvagin and the detection/existence bifurcation.

### 6.3 Target

15 pages, ~600 lines Lean, 0 sorry, ~20 verified theorems.

---

## 7. Deliverables

1. `paper 95/P95_BSDSqueeze/` — Lean 4 bundle, `lake build` passes
2. `paper 95/paper95.tex` — LaTeX source
3. `paper 95/paper95.pdf` — compiled PDF
4. `paper 95/solve_bsd_37a1.py` — Python CAS script for Hecke data + constants
5. `paper 95/README.md` — summary, build instructions, axiom inventory
6. `paper 95/metadata.txt` — Zenodo metadata

---

## 8. Output Discipline (MANDATORY)

You are running inside a chatbot with a finite context window. Token overflow kills sessions.

**Minimize printing:**
- `lake build`: show only errors. Use `lake build 2>&1 | grep -E "error|sorry|warning"`.
- `#print axioms`: show only custom axioms. Omit `propext`, `Classical.choice`, `Quot.sound`.
- Python CAS: print only the emitted Lean definitions, not intermediate SymPy steps.
- LaTeX: print only errors. Not the full compilation log.
- Git: `git status --short`. Not full diffs.
- File reads: state what you found. Don't echo files back.

**When computation takes too long:**
If `lake build`, a tactic, or CAS computation exceeds ~5 minutes:
1. STOP. Report what is slow.
2. Ask the user whether to consult Math AI (Gemini/GPT-o3) for an algorithmic shortcut.
3. Common shortcuts: Gröbner basis pre-reduction, factored polynomial forms, splitting large `ring` goals, explicit witnesses to avoid `decide` on large spaces.
4. Do NOT spin indefinitely.

---

## 9. Summary for the Executing Agent

You are writing Paper 95 of a 95-paper CRM series. The programme's central finding is that the logical cost of mathematics is the logical cost of R. You are applying the CRMLint Squeeze protocol — the same protocol used in Papers 77-94 — to the Gross-Zagier-Kolyvagin proof of BSD for rank ≤ 1.

**Your test case is 37a1** (y² + y = x³ - x, conductor 37, rank 1). This is the simplest rank-1 elliptic curve.

**Your task:**
1. Build the Lean 4 bundle verifying the BISH core (Hecke eigenvalues, Heegner point, Silverman bounds, finite search)
2. Axiomatize the CLASS components (Gross-Zagier formula, Kolyvagin theorem, analytic continuation)
3. Write the LaTeX paper presenting the BISH/CLASS decomposition as four theorems
4. Identify the detection/existence bifurcation pattern (Theorem C) connecting to Paper 94

**Key reusable infrastructure:**
- Paper 80 (P80_GaussManin): Legendre PF operator, `ring` verification
- Paper 94 (P94_NormalFunctionSqueeze): InhomogPFData, recurrence verification
- Paper 51 (P51_BSD): BSDRankOneData, SilvermanBound, searchGrid
- Paper 48 (P48_BSD): LPO_R, zero_test_iff_LPO

**The novel contribution is not new number theory.** It is the CRM decomposition revealing that ~70% of the only proven case of a Clay Millennium Problem is constructively verified, and that the remaining ~30% (CLASS) follows the same detection/existence bifurcation pattern found across the entire programme.

**Do not attempt to prove the Gross-Zagier formula or Kolyvagin's theorem in Lean.** Axiomatize them. Your job is the Squeeze: identify the Classical Boundary Node, verify everything below it, classify everything above it.
