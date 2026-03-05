# Paper 89 — Proof Instruction

## Title
The Universal Hyperelliptic Squeeze: Absolute Hodge Classes for the Full Weil Locus

Paper 89 of the Constructive Reverse Mathematics Series

## Thesis
The exotic Weil class on the Jacobian of the universal genus-4 hyperelliptic Weil family
C_{a,b,c} : y² = x⁹ + ax⁷ + bx⁵ + cx³ + x
is a global flat section of the Gauss-Manin connection over the full 3-dimensional parameter space Q(a,b,c), and is algebraic at the Fermat anchor (a,b,c) = (0,0,0). Conditional on the Variational Hodge Conjecture, the exotic Weil class is algebraic across the entire hyperelliptic Weil locus. This is the eleventh CRMLint Squeeze application.

## Why This Paper Exists

Paper 85 proved τ₊ = 0 (trace vanishing) computationally for y² = x⁹ + tx⁷ + x (1-parameter). Paper 88 proved conditional algebraicity for the same 1-parameter family via Fermat domination at t = 0. But this is a single 1-dimensional slice of the full 3-parameter space of genus-4 hyperelliptic curves with Q(i)-action. Why not go for the full family?

**Why piecemeal fails (Baire Category argument):** The set of parameter triples (a,b,c) admitting additional algebraic structure (palindromic core, CM specialization, extra automorphisms) is a countable union of proper algebraic subvarieties of A³ — hence measure zero and meagre. Any theorem covering only these special loci is vacuous on the generic point. The universal family is the only honest target.

## The Universal Family

The most general genus-4 hyperelliptic curve with Q(i)-action σ(x,y) = (-x, iy) is:
```
C_{a,b,c} : y² = f(x) = x⁹ + ax⁷ + bx⁵ + cx³ + x
```
where a, b, c are independent parameters. The Q(i)-action forces:
- f is odd: f(-x) = -f(x)
- f factors as x · g(x), where g(x) = x⁸ + ax⁶ + bx⁴ + cx² + 1
- The eigenspace V₊ (eigenvalue i of σ*) has dimension g = 4

### Special cases already done:
- (a,b,c) = (0,-t,0): Paper 84/86 family y² = x⁹ - tx⁵ + x (palindromic core, Kani-Rosen applies)
- (a,b,c) = (t,0,0): Paper 85/88 family y² = x⁹ + tx⁷ + x (non-palindromic, Fermat anchor)
- (a,b,c) = (0,0,0): Fermat specialization C₀: y² = x⁹ + x, dominated by F₁₆

## Strategy

### Step 1: CAS Computation (Python, SageMath)

Compute the Gauss-Manin connection on V₊ for the universal family over Q(a,b,c).

**Basis:** ωₖ = xᵏ dx/(2y) for k = 0, 1, 2, 3 (the eigenvalue-i differentials under σ*).

**Method:** Griffiths pole reduction in H¹_dR(C_{a,b,c}/Q(a,b,c)).

For each parameter derivative ∂/∂a, ∂/∂b, ∂/∂c:
1. Compute ∂ωₖ/∂p (p ∈ {a,b,c}) as a meromorphic differential.
2. Apply pole reduction: subtract exact differentials d(h/yⁿ) to bring poles below degree 2g+1 = 9.
3. Express the result in the basis {ω₀, ω₁, ω₂, ω₃}.
4. Extract the 4×4 connection matrix M_p(a,b,c) for each parameter direction.

**Output:** Three 4×4 matrices M_a, M_b, M_c with entries in Q(a,b,c).

### Step 2: Trace Computation

Compute τ₊(a,b,c) = tr(M_a(a,b,c)) for the connection in the ∂/∂a direction, and similarly for ∂/∂b, ∂/∂c.

**Expected result:** τ₊ = 0 for all three directions, as a polynomial identity in Q(a,b,c).

**Rationale:** Paper 85 found τ₊ = 0 for 8 specializations across genera 2–5. The universal computation would confirm this as an algebraic identity rather than a numerical coincidence.

### Step 3: Lean Formalization

Encode the polynomial identities from Step 2 as Lean 4 theorems, verified by `ring`.

**Key theorems to formalize:**
1. f is odd: f(-x,a,b,c) = -f(x,a,b,c)
2. Factorization: f = x · g
3. Core polynomial: g(x,a,b,c) = x⁸ + ax⁶ + bx⁴ + cx² + 1
4. Palindromic obstruction: g - g_rev = ax²(x⁴-1) + (b-b)x²·? + ... (characterize which (a,b,c) give palindromic core)
5. Specialization identities: f(x,0,0,0) = x⁹ + x, f(x,t,0,0) = x⁹ + tx⁷ + x, f(x,0,-t,0) = x⁹ - tx⁵ + x
6. Fermat domination at (0,0,0): same as Paper 88
7. Trace vanishing: tr(M_a) = 0, tr(M_b) = 0, tr(M_c) = 0 (as polynomial identities)
8. Paper 85 data: dim V₊ = 4, dim ∧⁴(V₊) = 1

### Step 4: CLASS Boundary Nodes

Same two axioms as Paper 88:
1. **Shioda's Fermat Hodge Conjecture (1982):** At (0,0,0), the exotic class on J(C₀) is algebraic.
2. **Variational Hodge Conjecture:** A flat section algebraic at one fiber is algebraic generically.

The upgrade from P88: "generically" now means over the full 3-dimensional base, not just a 1-dimensional slice.

## Technical Challenges

### Expression Size
The Griffiths pole reduction for the 3-parameter family produces connection matrix entries that are rational functions in (a,b,c) — potentially large. Key challenge: keeping intermediate expressions manageable.

**Mitigation:**
- Use sparse representation in the CAS.
- Factor common denominators early (the discriminant of f appears in all denominators).
- Verify each matrix entry separately rather than the full trace at once.

### Lean `ring` on Multivariate Polynomials
Lean's `ring` tactic handles multivariate polynomial identities (demonstrated in Papers 80–83 for single variable). The 3-variable case is feasible but may require:
- Splitting large identities into intermediate lemmas.
- Working over ℤ[a,b,c] rather than ℚ(a,b,c) where possible.

### Palindromic Locus
The core g(x,a,b,c) = x⁸ + ax⁶ + bx⁴ + cx² + 1 is palindromic iff a = c (coefficient of x⁶ equals coefficient of x²). This defines the Kani-Rosen locus (a 2-dimensional subvariety). Paper 89 must verify the trace vanishing holds on the COMPLEMENT of this locus as well — hence the need for the full Q(a,b,c) computation.

## Relationship to Prior Papers

| Paper | Family | Parameters | Method | Result |
|-------|--------|-----------|--------|--------|
| 84 | y²=x⁹-tx⁵+x | 1 (b=-t) | Gauss-Manin block | τ₊ = 0 (flat) |
| 85 | y²=x⁹+tx⁷+x | 1 (a=t) | CAS trace | τ₊ = 0 (flat, computational) |
| 86 | y²=x⁹-tx⁵+x | 1 (b=-t) | Kani-Rosen | Hodge (unconditional) |
| 88 | y²=x⁹+tx⁷+x | 1 (a=t) | Fermat anchor + VHC | Hodge (conditional on VHC) |
| **89** | **y²=x⁹+ax⁷+bx⁵+cx³+x** | **3 (a,b,c)** | **Universal trace + VHC** | **Universal Hodge (conditional)** |

## Deliverables

1. **Python CAS script** (`verify_universal_family.py`): Computes M_a, M_b, M_c over Q(a,b,c). Verifies trace vanishing. Emits Lean 4 code.
2. **Lean 4 bundle** (`P89_UniversalSqueeze/`): Polynomial identity verification (0 sorry).
3. **LaTeX paper** (`paper89.tex`): ~15 pages, ≥25 references. Eleventh CRMLint Squeeze.
4. **README.md** + **metadata.txt**: Standard packaging.

## CRM Classification

- **BISH content:** All polynomial identities (oddness, factorization, palindromic obstruction characterization, specialization, Fermat domination, trace vanishing τ₊(a,b,c) = 0, dimension data).
- **CLASS content:** Shioda's Fermat Hodge Conjecture + Variational Hodge Conjecture.
- **Overall:** CLASS (conditional on VHC). The BISH core is strictly larger than Paper 88 (3-parameter vs 1-parameter).

## Dependencies

- Papers 84–85: V₊ Lagrangian structure, trace vanishing for specializations
- Paper 88: Fermat anchor at (0,0,0), Shioda + VHC framework
- Paper 80: Griffiths pole reduction pipeline over function fields
- Mathlib: `ring` tactic for multivariate polynomial verification
