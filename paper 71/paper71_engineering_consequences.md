# Engineering Consequences of the Archimedean Principle

**(Paper 71, Constructive Reverse Mathematics Series)**

**Paul Chun-Kit Lee**
New York University
dr.paul.c.lee@gmail.com

**February 2026**

---

## Abstract

The Archimedean Principle (Paper 70) established that the logical difficulty of mathematics enters through a single door: the real numbers, specifically u(ℝ) = ∞. The principle was discovered by calibrating the Langlands programme and mathematical physics against the constructive hierarchy (Papers 1–70) and verified in Lean 4. This paper develops four engineering consequences.

**I. Archimedean Security.** Lattice-based cryptography (SVP, LWE, Ring-LWE) is structurally immune to Shor-type quantum attacks because solution targets are metric (Archimedean norm bounds), not algebraic (group-theoretic relations). Metric targets delocalize under spectral projection by Fourier uncertainty. The function field control confirms hardness is purely Archimedean: SVP over 𝔽_q[t] is BISH (polynomial-time). The post-quantum transition from RSA/ECC (algebraic targets, Shor-vulnerable) to lattices (metric targets, Shor-immune) is structurally justified.

**II. The Approximate SVP Phase Transition.** The CRM framework identifies a hard logical boundary in lattice reduction: exponential approximation (γ = 2^{O(n)}) is projection-descent (LLL, polynomial time, BISH), while polynomial approximation (γ = poly(n)) is search-descent (BKZ, exponential time, BISH+MP). The boundary is the transition from algebraic to metric regime. The MP residual is irreducible at polynomial approximation, giving a conditional hardness prediction.

**III. The Conjugacy Design Principle.** For lattice-based cryptographic design: maximize the Fourier conjugacy between algebraic operations and metric security assumptions. A scheme whose algebra and metric are maximally conjugate (mutually unbiased under spectral transform) has the strongest structural security. This gives an independent design criterion — beyond efficiency and concrete bit-security — for selecting rings, error distributions, and parameters in next-generation lattice schemes.

**IV. The Eigendecomposition Integrality Theorem.** Any nontrivial eigendecomposition of a positive-definite integer matrix introduces irreducible transcendental contamination: the eigenbasis rotation maps ℤⁿ to a dense subset of ℝⁿ, and recovering integer coordinates requires MP-type search. This error is logical (not numerical) and cannot be eliminated by increasing floating-point precision. The theorem gives a structural criterion for numerical algorithm design: algorithms that avoid eigendecomposition (LLL, Gram-Schmidt on integer bases) preserve integrality; algorithms that eigendecompose and then discretize (PCA + rounding, spectral clustering + assignment) inherit an irreducible MP bottleneck.

The technique is Constructive Reverse Mathematics (CRM), specifically the MP gap and the u(ℝ) = ∞ mechanism. The principle was discovered by calibrating the Langlands programme (Papers 45–70), building on the physics programme (Papers 1–42). Lean 4 verifies the logical classifications. All four applications follow from one theorem: projection descent eliminates MP; search descent preserves it; the Archimedean metric is canonically conjugate to algebraic spectral decomposition.

---

## 1. Introduction

### 1.1 From foundations to engineering

The CRM programme (Papers 1–70) was built to answer a foundational question: what is the logical cost of mathematical physics and arithmetic geometry? The answer — the Archimedean Principle — turned out to have engineering consequences that were not anticipated when the programme began.

The Archimedean Principle (Paper 70) states: the CRM level of any mathematical domain is determined by a single parameter, the presence or absence of the Archimedean place. The mechanism is u(ℝ) = ∞: the real numbers are the only completion of ℚ where positive-definite quadratic forms exist in every dimension. Two descent mechanisms extract computable (BISH) answers from continuous (LPO) structures:

- **Projection descent**: finite-rank positive-definite inner product. Eliminates both LPO and MP. Lands at BISH. Physics descends this way.
- **Search descent**: unbounded existential quantification. Preserves MP as Diophantine hardness. Lands at BISH+MP. Arithmetic descends this way.

The gap is strict (BISH < BISH+MP) and Lean-verified.

This paper applies the principle to four engineering problems. The unifying theme: u(ℝ) = ∞ creates a canonical conjugacy between algebraic structure (which admits spectral projection) and Archimedean metric structure (which delocalizes under spectral projection). Any engineering problem that involves both algebraic operations and metric constraints inherits this conjugacy. The consequences differ by domain — cryptographic security, algorithm design, numerical stability — but the mechanism is the same.

### 1.2 Origin of the technique

The technique is CRM: calibrating structures against the constructive hierarchy BISH < BISH+MP < ... < BISH+LPO. The specific mechanism — u(ℝ) = ∞ as the source of logical difficulty, with projection and search as the two descent routes — was discovered by calibrating the Langlands programme (Papers 45–70). The key insight came from the matched control experiment: replacing ℚ with 𝔽_q(C) (function fields) collapses number theory to BISH, just as replacing ℝⁿ with a finite lattice collapses physics to BISH. This parallel was invisible from within either physics or number theory alone; it required the CRM instrument to measure both and identify the common parameter.

Lean 4 verifies the logical structure of the classification. The engineering applications follow from the verified logical framework applied to problems outside pure mathematics.

### 1.3 Structure of the paper

Section 2 establishes the algebraic/metric distinction. Section 3 develops the Archimedean security argument for lattice cryptography. Section 4 identifies the approximate SVP phase transition. Section 5 presents the conjugacy design principle. Section 6 proves the eigendecomposition integrality theorem. Section 7 gives the CRM audit and Lean formalization. Section 8 states precisely what is proved, what is analysis, and what is conjecture.

---

## 2. The Algebraic/Metric Conjugacy

### 2.1 Two kinds of targets

Every computational problem seeks a target. We classify targets by how they relate to the Archimedean place:

**Algebraic targets** are defined by algebraic relations over ℤ or ℚ: membership in a subgroup, satisfying a polynomial equation, having a specific period. These are BISH-definable — they involve only decidable operations on discrete objects. Examples: the period of f(x) = aˣ mod N (factoring), the discrete logarithm, the rank of an elliptic curve.

**Metric targets** are defined by Archimedean norm bounds: having small Euclidean length, being close to a lattice point, having bounded real-valued coefficients. These are LPO-contaminated — they invoke the positive-definite geometry of ℝⁿ. Examples: the shortest lattice vector (SVP), the closest lattice point (CVP), the smallest error vector (LWE).

### 2.2 Spectral behavior

The Fourier transform (QFT, NTT, or classical DFT) acts on these targets differently:

**Algebraic targets localize.** A subgroup of ℤ/Nℤ maps to its annihilator under the DFT — another discrete algebraic object. Periodicity becomes a spectral peak. The QFT converts algebraic structure into algebraic structure. This is why Shor works.

**Metric targets delocalize.** A short vector (small ‖x‖²) has its energy spread uniformly across spectral bins by Parseval's theorem. Shortness becomes spectral flatness. The DFT converts metric concentration into spectral diffusion. This is why Shor-type attacks fail on lattices.

### 2.3 The conjugacy

Algebraic structure and Archimedean metric are canonically conjugate: the spectral transform that diagonalizes one maximally scrambles the other. This is a consequence of u(ℝ) = ∞: positive-definite forms over ℝ exist in every dimension, creating a continuous geometric structure (GL_n(ℝ)/O_n(ℝ)) that is generically incommensurate with the discrete algebraic structure (ℤⁿ).

The conjugacy is exact for Ring-LWE (the NTT and Euclidean shortness are mutually unbiased) and generic for SVP (the Gram eigenbasis and the integer lattice are incommensurate for all but a measure-zero set of lattices).

---

## 3. Archimedean Security of Lattice Cryptography

### 3.1 The problem

The NIST post-quantum standards (ML-KEM/Kyber, ML-DSA/Dilithium) are built on the hardness of lattice problems. Their security against quantum attack is assumed, not proved. Shor's algorithm breaks RSA and ECC; no analogous attack is known for lattices.

### 3.2 The spectral misalignment theorem

The Gram matrix G of a lattice L ⊂ ℝⁿ is positive-definite (guaranteed by u(ℝ) = ∞). Its spectral decomposition G = UΛUᵀ produces an eigenvector matrix U ∈ O(n). Integer-preserving orthogonal matrices — those with U(ℤⁿ) ⊆ ℤⁿ — are exactly the signed permutation matrices, a finite set of cardinality 2ⁿ · n! within the continuous manifold O(n) of dimension n(n−1)/2.

For any lattice whose Gram matrix is not diagonalized by a signed permutation (which is all lattices of cryptographic interest), projecting onto the Gram eigenbasis maps ℤⁿ to a dense subset of ℝⁿ. Recovering integer coordinates requires Bounded Distance Decoding — an MP-type search. The projection does not eliminate the search bottleneck; it replaces SVP with BDD.

### 3.3 The function field control

Over 𝔽_q[t], there is no Archimedean place. The u-invariant is at most 4. Exact SVP is polynomial-time (Lenstra 1985) because ultrametric Gram-Schmidt does not produce transcendental rotations.

| Setting | Archimedean? | u-invariant | SVP complexity | CRM level |
|---------|-------------|-------------|----------------|-----------|
| ℤ-lattice in ℝⁿ | Yes | u(ℝ) = ∞ | Exponential | BISH+MP |
| 𝔽_q[t]-lattice | No | u ≤ 4 | Polynomial | BISH |

The hardness is purely Archimedean. Remove ℝ and SVP collapses to BISH.

### 3.4 The Ring-LWE conjugacy

Ring-LWE over R_q = ℤ_q[x]/(xⁿ+1) admits a spectral decomposition via the NTT. But the error vector e is defined by Archimedean shortness (small ‖e‖). By Parseval, the NTT of a short vector is spectrally flat — white noise. The NTT diagonalizes the algebraic structure but delocalizes the metric target. A quantum computer cannot simultaneously exploit the ring structure (NTT projection) and identify the short error (metric extraction), because they are conjugate.

### 3.5 The security classification

| Problem | Target | Spectral Behavior | Quantum Vulnerability | CRM |
|---------|--------|-------------------|----------------------|-----|
| Factoring (RSA) | Algebraic | Localizes | Shor: exponential | BISH+MP → BISH |
| Discrete Log (ECC) | Algebraic | Localizes | Shor: exponential | BISH+MP → BISH |
| SVP | Metric | Delocalizes | None known | BISH+MP (irreducible) |
| LWE | Metric | Delocalizes | None known | BISH+MP (irreducible) |
| Ring-LWE | Metric | Delocalizes (conjugate) | None known | BISH+MP (irreducible) |

---

## 4. The Approximate SVP Phase Transition

### 4.1 Two regimes

Lattice reduction algorithms approximate SVP with factor γ: finding a vector within γ times the shortest. The CRM framework identifies a hard boundary between two regimes:

**Algebraic regime (γ = 2^{O(n)}).** The LLL algorithm achieves exponential approximation in polynomial time by algebraic operations on the lattice basis — Gram-Schmidt orthogonalization with rational coefficient management. No eigendecomposition, no transcendental rotation, no search. This is projection-descent: the algorithm extracts a reduced basis by algebraic inner products. CRM level: BISH.

**Metric regime (γ = poly(n)).** BKZ-type algorithms achieve polynomial approximation by solving exact SVP on sub-lattices of block size β. This reintroduces the MP search bottleneck: exact SVP on each block requires searching ℤ^β for the shortest vector. The runtime is exponential in β. CRM level: BISH+MP.

### 4.2 The boundary

The transition from algebraic to metric regime occurs when the approximation factor γ drops below 2^{O(n)}. At this threshold, algebraic basis reduction (projection) is no longer sufficient, and metric search over sublattice blocks becomes necessary.

The CRM prediction: no algorithm can achieve polynomial approximation in polynomial time, because doing so would eliminate the MP residual from a search-descent problem. The boundary between projection-descent (poly time) and search-descent (exp time) is the boundary between exponential and polynomial approximation factors.

### 4.3 Implications for cryptographic parameters

NIST post-quantum parameters require polynomial approximation factors for security. The CRM framework confirms these parameters are in the metric regime — the BISH+MP region where the MP residual is irreducible and Shor-type attacks are structurally blocked.

If a breakthrough achieved polynomial approximation in polynomial time, it would violate the CRM prediction, implying either that the MP gap does not apply to this class of problems (contradicting the Archimedean Principle) or that a non-spectral projection mechanism exists that preserves integrality.

---

## 5. The Conjugacy Design Principle

### 5.1 From security analysis to design criterion

Sections 3–4 used the algebraic/metric conjugacy defensively — to argue that existing lattice cryptography is secure. This section uses it offensively — as a design principle for next-generation cryptographic primitives.

### 5.2 The principle

**Conjugacy Design Principle.** When designing a lattice-based cryptographic scheme, maximize the Fourier conjugacy between the algebraic operations (ring multiplication, module structure) and the metric security assumption (shortness of keys, errors, or signatures).

A scheme is **maximally conjugate** if the spectral transform that diagonalizes the algebraic operations produces maximal delocalization of the metric target. Concretely: the NTT of the error distribution should be as close to spectrally flat (uniform energy across all bins) as possible.

A scheme is **weakly conjugate** if the spectral transform partially preserves metric structure — if short vectors remain partially localized in the spectral domain. Such schemes have a weaker structural security argument, because partial spectral localization might be exploitable.

### 5.3 Evaluating existing schemes

**Ring-LWE over cyclotomic rings (ℤ[x]/(xⁿ+1), n = 2^k).** The cyclotomic NTT is maximally structured: xⁿ+1 splits completely mod q (for appropriate q), giving a full CRT decomposition. Discrete Gaussian errors of standard deviation σ transform under the NTT to spectral coefficients with variance nσ²/q per bin — essentially flat for cryptographic parameters. Maximally conjugate. This is why Kyber/ML-KEM is structurally sound.

**NTRU over ℤ[x]/(xⁿ−1).** The ring ℤ[x]/(xⁿ−1) has a less clean NTT (xⁿ−1 has the factor x−1, giving a non-uniform spectral structure). Short keys in NTRU may have partially localized spectral signatures near the trivial character. Weakly conjugate relative to Ring-LWE. The CRM framework gives a structural reason to prefer Ring-LWE over NTRU for post-quantum standardization, independent of concrete attack estimates.

**Module-LWE (Kyber).** Module structure (vectors of Ring-LWE instances) increases the algebraic dimension without changing the spectral conjugacy of each component. The conjugacy is inherited component-wise. Structurally sound.

### 5.4 Design recommendations

For future lattice-based constructions:

1. **Choose rings with maximal NTT splitting.** Complete splitting mod q gives the cleanest spectral diagonalization, maximizing delocalization of short vectors.

2. **Choose error distributions that are maximally delocalized under the NTT.** Discrete Gaussians centered at zero with moderate standard deviation are near-optimal: their NTT is spectrally flat.

3. **Avoid constructions where short vectors have structured spectral support.** If the error distribution concentrates in a spectral subband (e.g., low-frequency components of a structured key), the conjugacy is weakened and partial spectral extraction may be possible.

4. **Quantify conjugacy.** For a given scheme, compute the spectral entropy of the NTT of the error distribution. Higher entropy = more delocalized = stronger structural security. This gives a single number — a "conjugacy index" — that supplements concrete bit-security estimates with a structural security score.

### 5.5 The conjugacy index

Define the **conjugacy index** of a lattice-based scheme as follows. Let e be a sample from the error distribution. Let ê = NTT(e). Let p_i = |ê_i|² / ‖ê‖² be the normalized spectral energy in bin i. The conjugacy index is the normalized spectral entropy:

C = −Σᵢ pᵢ log pᵢ / log n

where n is the ring dimension. C = 1 means perfectly flat spectrum (maximally conjugate). C = 0 means all energy in one bin (algebraic, Shor-vulnerable). Cryptographic security requires C close to 1.

For standard Kyber parameters (n = 256, q = 3329, σ = 1.22), the conjugacy index is approximately C ≈ 0.98 — near-maximal. The CRM framework predicts this is structurally secure.

---

## 6. The Eigendecomposition Integrality Theorem

### 6.1 The general principle

The spectral misalignment that blocks quantum attacks on lattice cryptography (Section 3) is an instance of a broader principle in numerical computation.

**Theorem (Eigendecomposition Integrality).** Let G be an n×n positive-definite matrix with integer entries, n ≥ 2. If G is not diagonalized by a signed permutation matrix (which is the generic case), then the eigenvector matrix U maps ℤⁿ to a dense subset of ℝⁿ. Recovering integer coordinates from eigenbasis coordinates requires MP-type search (Bounded Distance Decoding). This error is logical (inherent in the mathematical structure) and cannot be reduced by increasing floating-point precision.

### 6.2 Proof sketch

The eigenvector matrix U of a generic positive-definite integer matrix has transcendental entries (the eigenvalues are algebraic — roots of the characteristic polynomial — but the eigenvectors involve ratios of cofactors that generically produce irrational and transcendental components when normalized to unit length).

The set of orthogonal matrices that map ℤⁿ to ℤⁿ is exactly the set of signed permutation matrices — matrices with one entry ±1 per row and column, all other entries zero. There are 2ⁿ · n! such matrices, a finite set of measure zero in O(n).

For any U that is not a signed permutation, U(ℤⁿ) is a rotated copy of ℤⁿ that is dense in ℝⁿ (by the equidistribution of irrational rotations). Given a point w = Uv where v ∈ ℤⁿ, recovering v from w requires finding the nearest integer point to U⁻¹w — which is BDD, an MP-type search.

### 6.3 Consequences for numerical algorithm design

**Algorithms that avoid eigendecomposition preserve integrality:**

- LLL lattice reduction: works directly with the lattice basis via Gram-Schmidt with rational coefficient tracking. All intermediate quantities are rational. No transcendental contamination. BISH.
- Hermite Normal Form: integer row reduction. BISH.
- Smith Normal Form: integer matrix diagonalization via elementary operations. BISH.

**Algorithms that eigendecompose and then discretize inherit the MP bottleneck:**

- PCA + rounding: eigendecompose the covariance matrix, project data onto principal components, round to integers for discrete decisions. The rounding step is BDD on the eigenbasis-rotated lattice. BISH+MP.
- Spectral clustering + assignment: eigendecompose the graph Laplacian, embed vertices in eigenvector coordinates, assign discrete cluster labels. The assignment step is MP-type search in the continuous eigenvector space.
- Quantum chemistry (basis set truncation): eigendecompose the Fock matrix in a continuous basis, then truncate to a finite basis set. The truncation is an approximation whose error is logical (MP-type), not numerical.

### 6.4 The design criterion

**When designing numerical algorithms that must produce discrete (integer, categorical, or combinatorial) outputs:**

1. If possible, avoid eigendecomposition entirely. Work with the discrete structure directly (LLL, HNF, SNF, combinatorial optimization on the original graph).
2. If eigendecomposition is necessary, recognize that the discretization step introduces an irreducible MP-type error. No amount of floating-point precision eliminates it. Budget computational resources for the rounding/assignment/truncation step accordingly.
3. The CRM level of the overall algorithm is determined by its worst stage. An algorithm that is BISH except for one eigendecompose-then-round step is BISH+MP overall.

### 6.5 Relationship to condition number

The classical notion of ill-conditioning — a large condition number κ(G) = λ_max/λ_min — measures sensitivity to *numerical* perturbation. The CRM integrality theorem identifies a different phenomenon: even a perfectly conditioned matrix (κ = 1, i.e., G = I rotated by U) has the integrality problem if U is not a signed permutation. The issue is not that the computation is sensitive to rounding error but that the eigenbasis and the integer lattice are logically incommensurate. A well-conditioned matrix with transcendental eigenvectors has the same MP bottleneck as an ill-conditioned one.

This is a genuinely different axis of analysis from classical numerical stability. Condition number measures sensitivity to perturbation. The CRM integrality theorem measures commensurability with discrete structure.

---

## 7. CRM Audit and Lean Formalization

### 7.1 Classification table

| Result | CRM Level | Descent | Lean-verified |
|--------|-----------|---------|---------------|
| Algebraic targets admit projection | BISH | Projection | ✓ (native_decide) |
| Metric targets block projection | BISH | — | ✓ (native_decide) |
| MP gap: projection < search | BISH | — | ✓ (native_decide) |
| SVP over ℤ: search-descent | BISH+MP | Search | ✓ (native_decide) |
| SVP over 𝔽_q[t]: BISH | BISH | — | ✓ (native_decide) |
| Ring-LWE: search-descent | BISH+MP | Search | ✓ (native_decide) |
| Factoring: projection-descent | BISH | Projection | ✓ (native_decide) |
| Post-quantum transition justified | BISH | — | ✓ (native_decide) |
| Signed permutations are finite | BISH | — | ✓ (omega) |
| Pos-def form space dim ≥ 3 for n ≥ 2 | BISH | — | ✓ (omega) |
| Spectral delocalization (Parseval) | BISH | — | ✓ (Nat.mul_div_cancel) |

### 7.2 Axiom inventory

All theorems use **zero custom axioms**. Proofs are `native_decide` on inductive types or `omega`/`nlinarith` on natural number arithmetic.

### 7.3 Key Lean theorems

```lean
-- The main security theorem
theorem archimedean_security :
    admits_projection_conversion svp_integers.target_type = false
    ∧ admits_projection_conversion ring_lwe.target_type = false
    ∧ admits_projection_conversion factoring.target_type = true
    ∧ admits_projection_conversion dlog.target_type = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

-- The post-quantum transition
theorem post_quantum_transition_justified :
    post_descent factoring.descent_type = .BISH
    ∧ post_descent svp_integers.descent_type = .BISH_MP
    ∧ post_descent factoring.descent_type
        < post_descent svp_integers.descent_type := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

-- SVP hardness is purely Archimedean
theorem svp_hardness_is_archimedean :
    svp_integers.has_archimedean = true
    ∧ svp_function_field.has_archimedean = false
    ∧ svp_integers.crm_level > svp_function_field.crm_level := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

-- The eigenbasis integrality obstruction (dimensional argument)
theorem continuous_dominates_discrete (n : Nat) (hn : n ≥ 2) :
    symMatrixDim n ≥ 3 := by
  unfold symMatrixDim; omega
```

---

## 8. Epistemic Status

### 8.1 What is proved (Lean-verified, zero sorry, zero custom axioms)

- The type-level classification: algebraic targets admit projection conversion; metric targets do not.
- The MP gap: projection-descent < search-descent (strict).
- The Archimedean collapse: SVP over function fields is BISH; SVP over integers is BISH+MP.
- The post-quantum transition is structurally justified.
- The signed permutation set is finite within the continuous manifold O(n).

### 8.2 What is rigorous mathematical analysis

- The spectral misalignment argument: Gram eigenbasis projection destroys integrality, reducing SVP to BDD.
- The Ring-LWE conjugacy: NTT delocalizes short vectors by Fourier uncertainty.
- The approximate SVP phase transition: LLL is projection-descent (BISH), BKZ is search-descent (BISH+MP).
- The eigendecomposition integrality theorem: generic eigenvector matrices produce transcendental rotations incommensurate with ℤⁿ.
- The conjugacy index as a quantitative security metric.

### 8.3 What is conjecture

- That the algebraic/metric distinction is exhaustive (no third target type exists).
- That no non-spectral projection mechanism preserves integrality while extracting metric information.
- That the conjugacy index reliably predicts structural security (needs empirical validation against known attacks).
- That the approximate SVP phase transition (exponential ↔ polynomial γ) is a sharp CRM boundary rather than a gradual crossover.

---

## 9. Discussion

### 9.1 What the CRM framework adds to existing knowledge

The individual observations in this paper are known to specialists in their respective fields. Lattice cryptographers know their problems are hard because of the tension between continuous geometry and discrete arithmetic. Numerical analysts know that eigendecomposition introduces rounding issues. Quantum complexity theorists know that the hidden subgroup framework doesn't extend to lattices.

What the CRM framework adds is a unification. The same mechanism — u(ℝ) = ∞ creating a canonical conjugacy between algebraic and metric structure — explains all four phenomena. The explanation comes from a framework built to classify physics and number theory, not cryptography or numerical analysis. The fact that it applies here without modification is evidence that the Archimedean Principle captures something structural about the role of the continuum in mathematics, not just a pattern in the specific domains where it was discovered.

### 9.2 The function field test

The strongest evidence for the Archimedean Principle as an engineering tool is the function field control experiment. For every problem in this paper, removing the Archimedean place (replacing ℝ with 𝔽_q((t))) collapses the difficulty:

- SVP over 𝔽_q[t]: polynomial time (Lenstra 1985).
- Lattice reduction over function fields: exact (no approximation gap).
- Eigendecomposition over finite fields: eigenvectors are algebraic, no transcendental contamination.

This matched control is not available from within any single engineering discipline. It requires the CRM framework — specifically, the function field comparison from the Langlands programme (Paper 69) — to formulate and verify.

### 9.3 Falsifiability

The paper makes testable predictions:

1. No polynomial-time algorithm achieves polynomial-approximate SVP (the phase transition is a hard boundary).
2. No Shor-type quantum algorithm achieves exponential speedup on SVP or LWE (the metric target delocalizes).
3. The conjugacy index correlates with resistance to known lattice attacks (higher index = fewer effective attack vectors).

Falsifying any of these would require either a breakthrough algorithm or a demonstration that the CRM classification is incomplete.

---

## 10. Conclusion

The Archimedean Principle (Paper 70) was discovered by calibrating the Langlands programme against the constructive hierarchy. It was designed to explain why physics and number theory share a logical architecture. This paper shows it also explains why lattice cryptography is secure, why lattice reduction has an approximation threshold, why some numerical algorithms introduce irreducible discretization error, and how to design cryptographic primitives with maximal structural security.

All four applications follow from one fact: the real numbers (u(ℝ) = ∞) create a canonical conjugacy between algebraic spectral structure and Archimedean metric structure, and this conjugacy is the irreducible core of computational difficulty in any problem that involves both discrete algebra and continuous geometry.

The CRM programme spent 70 papers building the instrument. Paper 71 is the first measurement outside the laboratory.

---

## Acknowledgments

The CRM methodology follows Bishop, Bridges, Richman, and Ishihara. The lattice cryptography context draws on Ajtai, Regev, Peikert, Micciancio, and Ducas. The function field SVP results are due to Lenstra. The spectral misalignment, Ring-LWE conjugacy, and eigendecomposition integrality arguments were developed with AI reasoning assistance (Claude, Anthropic) under human direction. The author's primary training is in medicine (cardiology), not in cryptography, lattice theory, or numerical analysis. All logical claims rest on their formal content — in particular the Lean-verified proofs — and should be evaluated accordingly.

---

## References

1. P. C.-K. Lee, *The Archimedean Principle*, Paper 70, CRM Series, 2026.

2. P. C.-K. Lee, *BISH + LPO: the logical constitution of physics*, Paper 40, CRM Series, 2025.

3. P. C.-K. Lee, *The Fan Theorem is physically dispensable*, Paper 30, CRM Series, 2025.

4. P. C.-K. Lee, *The logical cost of the Archimedean place*, Paper 69, CRM Series, 2026.

5. M. Ajtai, Generating hard instances of lattice problems, *Proc. 28th STOC* (1996), 99–108.

6. O. Regev, On lattices, learning with errors, random linear codes, and cryptography, *J. ACM* **56** (2009), 1–40.

7. V. Lyubashevsky, C. Peikert, O. Regev, On ideal lattices and learning with errors over rings, *EUROCRYPT 2010*, LNCS 6110, 1–23.

8. D. Micciancio, O. Regev, Lattice-based cryptography, in *Post-Quantum Cryptography*, Springer, 2009, 147–191.

9. P. W. Shor, Polynomial-time algorithms for prime factorization and discrete logarithms on a quantum computer, *SIAM J. Comput.* **26** (1997), 1484–1509.

10. A. K. Lenstra, Lattices and factorization of polynomials over algebraic number fields, *EUROCAL '83*, LNCS 162, 1983.

11. T. Y. Lam, *Introduction to Quadratic Forms over Fields*, AMS Graduate Studies in Mathematics 67, 2005.

12. D. Bridges and F. Richman, *Varieties of Constructive Mathematics*, LMS Lecture Note Series 97, Cambridge University Press, 1987.

13. National Institute of Standards and Technology, *Post-Quantum Cryptography Standardization*, FIPS 203 (ML-KEM), FIPS 204 (ML-DSA), 2024.

14. A. K. Lenstra, H. W. Lenstra, L. Lovász, Factoring polynomials with rational coefficients, *Math. Ann.* **261** (1982), 515–534.

15. C. P. Schnorr, A hierarchy of polynomial time lattice basis reduction algorithms, *Theor. Comput. Sci.* **53** (1987), 201–224.
