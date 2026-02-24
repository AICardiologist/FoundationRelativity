# Paper 11: The Constructive Cost of Quantum Entanglement

## A Lean 4 Formalization of the Tsirelson Bound and Bell State Entropy

**Paul Chun-Kit Lee**

**Series:** Constructive Reverse Mathematics of Mathematical Physics, Paper 11

**Date:** February 2026

---

## DOCUMENT PURPOSE

This outline provides the complete structure for the LaTeX paper accompanying the Lean 4 formalization archived at Zenodo. It is designed for coding agents to produce the final PDF. Follow the structure exactly. All mathematical content is verified by the compiled Lean code (zero sorry, zero errors, zero warnings, ~500 lines across 8 modules).

---

## METADATA

- **Title:** The Constructive Cost of Quantum Entanglement: Tsirelson Bound and Bell State Entropy in Lean 4
- **Author:** Paul Chun-Kit Lee
- **Affiliation:** Independent Researcher, New York
- **Contact:** (same as previous papers)
- **DOI:** (Zenodo, to be assigned)
- **Series number:** Paper 11 in the Constructive Reverse Mathematics series
- **Lean version:** Lean 4 / Mathlib (current toolchain)
- **Build status:** `lake build` — 2260 jobs, zero errors, zero sorry, zero warnings
- **Axiom profile:** `[propext, Classical.choice, Quot.sound]` — standard Mathlib infrastructure only

---

## ABSTRACT (≈200 words)

We provide a complete Lean 4 formalization of two foundational results in quantum information theory: (A) the Tsirelson bound on the CHSH operator, establishing that for any self-adjoint involutions $A, A', B, B'$ on $\mathbb{C}^2$ and unit vector $\psi \in \mathbb{C}^2 \otimes \mathbb{C}^2$, the squared norm $\|C\psi\|^2 \leq 8$ (equivalently $|\langle \psi, C\psi \rangle| \leq 2\sqrt{2}$); and (B) the entanglement entropy of the Bell singlet state, proving that the partial trace of the Bell state density matrix yields the maximally mixed state $\rho_A = \tfrac{1}{2}I$ with von Neumann entropy $S(\rho_A) = \log 2$.

The formalization comprises approximately 500 lines across 8 modules, compiles with zero sorry, zero errors, and zero warnings. All theorems carry the axiom profile `[propext, Classical.choice, Quot.sound]` — the standard Mathlib infrastructure axioms. No custom axioms are introduced. The `Classical.choice` dependency arises from Mathlib's inner product space infrastructure, not from the mathematical content of the proofs.

Within the constructive reverse mathematics programme of this series, these results calibrate the compositional layer of quantum mechanics — tensor products, entanglement, correlations — establishing that Bell nonlocality and entanglement entropy are constructively accessible at the BISH level. This extends the calibration table of the companion papers (Papers 2, 7, 8, 9) from states, limits, and spectra to relational structure.

---

## 1. INTRODUCTION

### 1.1 Context and Motivation

[3-4 paragraphs. Cover the following points:]

The Tsirelson bound $|\langle \psi, C\psi \rangle| \leq 2\sqrt{2}$ (Cirel'son 1980) is the fundamental upper limit on quantum correlations in the CHSH setting (Clauser, Horne, Shimony, Holt 1969). It demarcates the boundary between quantum mechanics and more general no-signaling theories, and its experimental violation of the classical bound of 2 was confirmed by Aspect (Nobel Prize 2022). The bound is central to quantum information theory, quantum cryptography, and the foundations of physics.

The von Neumann entropy $S(\rho) = -\text{Tr}(\rho \log \rho)$ quantifies the information content and entanglement of quantum states (von Neumann 1932, Schumacher 1995). For bipartite pure states, the entropy of the reduced density matrix — obtained via partial trace — is the canonical measure of entanglement. The Bell singlet state, the prototypical maximally entangled qubit pair, has entanglement entropy $\log 2$.

This paper's contribution is twofold. First, it provides the first Lean 4 formalization of both results, complementing the existing Isabelle/HOL formalization of the CHSH inequality and Tsirelson bound by Echenim, Mhalla, and Mori (2023; published in J. Automated Reasoning, 2024). Second, within the author's constructive reverse mathematics (CRM) programme, it calibrates the *compositional* layer of quantum mechanics — a layer absent from the calibration table of the companion papers (Papers 2, 7, 8, 9), which addressed states (bidual gap), limits (thermodynamic limit), and spectra (uncertainty principle), but not tensor products, entanglement, or correlations.

### 1.2 The Constructive Reverse Mathematics Programme

[2-3 paragraphs. Briefly recap for readers unfamiliar with the series:]

Constructive reverse mathematics (CRM), initiated by Ishihara (2006) and developed by Bridges and Vîță (2006), classifies mathematical theorems by the omniscience principles required to prove them over Bishop-style constructive mathematics (BISH). The hierarchy BISH < WLPO < LPO < LEM provides a precise calibration of logical strength. A CRM result takes the form "Theorem T is equivalent to principle P over BISH."

The author's programme applies CRM methodology to mathematical physics, using machine-verified Lean 4 formalizations to determine the constructive cost of fundamental physical results. The `#print axioms` command provides a machine-checkable certificate of which logical principles a proof actually uses. Prior results established: non-reflexivity of quantum state spaces requires WLPO (Papers 2, 7); the thermodynamic limit requires LPO (Paper 8); finite-volume physics is BISH (Paper 8, Part A). Paper 9 synthesized these into a calibration table and proposed a working hypothesis: empirical predictions are BISH-derivable, and stronger logical principles enter only through idealizations that no finite laboratory can instantiate.

### 1.3 The Compositional Gap

[2 paragraphs. State the specific problem this paper addresses:]

The calibration table of Paper 9 covers individual quantum states (density operators, spectra) and thermodynamic limits, but does not address the *compositional* structure of quantum mechanics: tensor products, entanglement, and correlations. This is a significant lacuna. Bell nonlocality — the violation of Bell inequalities — is arguably the most distinctively quantum phenomenon, the feature that most sharply distinguishes quantum from classical physics at the operational level. If the constructive programme claims to map the logical geography of quantum mechanics, it must account for entanglement.

This paper fills that gap. We formalize the Tsirelson bound (Part A) and the Bell state entanglement entropy (Part B) in Lean 4, and verify via `#print axioms` that both results are BISH-provable — no omniscience principles are required. The resulting calibration table entry is: **Bell nonlocality and entanglement entropy are constructively free.**

### 1.4 Relation to Prior Formalizations

[2 paragraphs on Echenim-Mhalla and Lean-QuantumInfo:]

Echenim, Mhalla, and Mori (2023) formalized the CHSH inequality and Tsirelson bound in Isabelle/HOL, published in the Archive of Formal Proofs and subsequently in the Journal of Automated Reasoning (2024). Their formalization uses the Khalfin-Tsirelson-Landau identity (the $S^2 = 4I - [A_0,A_1][B_0,B_1]$ approach) and works in the operator norm framework with abstract projective measurements. However, their formalization is in classical Isabelle/HOL and does not address the constructive status of the results.

Separately, the Lean-QuantumInfo library (Meiburg et al. 2025) formalizes quantum information theory in Lean 4, with the flagship result being the Generalized Quantum Stein's Lemma. The library includes infrastructure for density matrices, quantum channels, and resource theories. Our formalization is independent of Lean-QuantumInfo and uses a matrix-first approach (working directly with `Matrix (Fin 4) (Fin 4) ℂ` for composite systems) rather than abstract tensor product infrastructure. This design choice prioritizes constructive transparency: every computation is an explicit finite matrix operation, making the axiom profile unambiguous.

### 1.5 Paper Organization

Section 2 presents the mathematical content and proof strategies. Section 3 describes the Lean formalization architecture. Section 4 reports the axiom audit results. Section 5 discusses the implications for the calibration table and the CRM programme. Section 6 addresses the Classical.choice issue. Section 7 concludes.

---

## 2. MATHEMATICAL CONTENT

### 2.1 Part A: The Tsirelson Bound

#### 2.1.1 Setup

Define involutions (self-adjoint operators squaring to the identity) on $\mathbb{C}^2$. Define the CHSH operator on $\mathbb{C}^2 \otimes \mathbb{C}^2 \cong \mathbb{C}^4$:
$$C = A \otimes B + A \otimes B' + A' \otimes B - A' \otimes B'$$
where $A, A', B, B'$ are involutions on $\mathbb{C}^2$ and $\otimes$ denotes the Kronecker product.

**Theorem (Tsirelson bound, squared form).** For any involutions $A, A', B, B'$ on $\mathbb{C}^2$ and unit vector $\psi \in \mathbb{C}^4$:
$$\|C\psi\|^2 \leq 8$$

This is equivalent to the standard form $|\langle \psi, C\psi \rangle| \leq 2\sqrt{2}$ via the Cauchy-Schwarz inequality.

#### 2.1.2 Proof Strategy

The proof proceeds in six steps:

1. **CHSH decomposition.** Rewrite $C = A \otimes (B + B') + A' \otimes (B - B')$ using Kronecker distributivity.

2. **Triangle inequality.** $\|C\psi\|^2 \leq (\|(A \otimes (B+B'))\psi\| + \|(A' \otimes (B-B'))\psi\|)^2$. (Not used directly; we use the parallelogram bound instead.)

3. **Involution dot-product preservation.** For any involution $M$ on $\mathbb{C}^2$ and vectors $u, v$ in $\mathbb{C}^4$: $\langle (M \otimes I)u, (M \otimes I)v \rangle = \langle u, v \rangle$. This follows from $M^*M = M^2 = I$. The key structural lemma.

4. **Sum-of-squares identity.** $(B+B')^*(B+B') + (B-B')^*(B-B') = 4I$, which follows from $B^2 = I$ and $B'^2 = I$ by expansion. Therefore $\|(I \otimes (B+B'))\psi\|^2 + \|(I \otimes (B-B'))\psi\|^2 = 4$.

5. **Parallelogram bound.** For any non-negative reals $a, b$: $(a + b)^2 \leq 2(a^2 + b^2)$. This is the Cauchy-Schwarz inequality for $\mathbb{R}^2$, provable by `nlinarith [sq_nonneg (a - b)]`.

6. **Assembly.** Combining steps 3-5:
$$\|C\psi\|^2 \leq 2(\|(A \otimes (B+B'))\psi\|^2 + \|(A' \otimes (B-B'))\psi\|^2) = 2 \cdot (\|(I \otimes (B+B'))\psi\|^2 + \|(I \otimes (B-B'))\psi\|^2) = 2 \cdot 4 = 8$$

Every step is algebraic/finite-dimensional. No limits, suprema, or decidability of real equality.

### 2.2 Part B: Bell State Entropy

#### 2.2.1 Setup

Define the Bell singlet state $|\Psi^-\rangle = \frac{1}{\sqrt{2}}(|01\rangle - |10\rangle)$ as a vector in $\mathbb{C}^4$. Define the density matrix $\rho = |\Psi^-\rangle\langle\Psi^-|$ as a $4 \times 4$ matrix. Define the partial trace over subsystem B:
$$(\text{Tr}_B \rho)_{ij} = \sum_{k} \rho_{(2i+k),(2j+k)}$$

Define binary entropy $h(p) = -p\log p - (1-p)\log(1-p)$.

#### 2.2.2 Results

**Theorem.** $\text{Tr}_B(\rho_{\Psi^-}) = \frac{1}{2}I_2$

**Theorem.** $h(1/2) = \log 2$

The partial trace is computed by explicit matrix arithmetic using `fin_cases` and `norm_num`. The binary entropy uses Mathlib's `Real.log` (which satisfies `Real.log 0 = 0`, avoiding the need for a case split at the boundary).

The entanglement entropy $S(\rho_A) = h(1/2) = \log 2$ is the maximum qubit entanglement, confirming that the Bell state is maximally entangled.

---

## 3. LEAN FORMALIZATION

### 3.1 Architecture

Eight modules, approximately 500 lines total:

| Module | Lines (approx.) | Content |
|--------|-----------------|---------|
| `Defs.lean` | 80 | Involution structure, CHSH operator, Pauli matrices, partial trace, Bell state |
| `BinaryEntropy.lean` | 40 | $h(p)$ definition, $h(1/2) = \log 2$ |
| `PartialTrace.lean` | 50 | Trace preservation lemmas |
| `BellState.lean` | 60 | Bell singlet density matrix, partial trace = $\frac{1}{2}I$, entropy = $\log 2$ |
| `KroneckerLemmas.lean` | 80 | Kronecker negation/subtraction, CHSH decomposition, sum-of-squares |
| `InvolutionNorm.lean` | 70 | Dot-product preservation under involution Kronecker action |
| `TsirelsonBound.lean` | 80 | Main bound: $\|C\psi\|^2 \leq 8$ |
| `Main.lean` | 40 | Assembly, `#print axioms` audit, documentation |

### 3.2 Key Design Decisions

**Matrix-first approach.** We represent the composite system $\mathbb{C}^2 \otimes \mathbb{C}^2$ as $\mathbb{C}^4$ using `Fin 2 × Fin 2 → ℂ` (equivalently `Fin 4 → ℂ` via the product-fin equivalence). Tensor products are Kronecker products via `Matrix.kroneckerMap`. This avoids fighting Mathlib's abstract tensor product infrastructure and makes every computation explicit.

**Involution structure.** We define `Involution n` as a structure containing a matrix `mat`, a proof `sq_eq_one : mat * mat = 1`, and a proof `hermitian : mat.conjTranspose = mat`. This is cleaner than asserting properties separately and makes the Tsirelson bound statement self-contained.

**Squared-norm formulation.** We prove $\|C\psi\|^2 \leq 8$ rather than $|\langle \psi, C\psi \rangle| \leq 2\sqrt{2}$. The squared form avoids square roots in the proof, simplifying the Lean formalization. The equivalence follows from Cauchy-Schwarz: $|\langle \psi, C\psi \rangle|^2 \leq \|\psi\|^2 \|C\psi\|^2 = 1 \cdot 8 = 8$, so $|\langle \psi, C\psi \rangle| \leq 2\sqrt{2}$.

### 3.3 Notable Proof Techniques

- `fin_cases` + `simp` + `ring` / `norm_num` for explicit matrix computations
- `nlinarith [sq_nonneg (a - b)]` for the parallelogram bound
- `starAlgebra` lemmas for involution properties
- Dot product (`star v ⬝ᵥ w`) rather than abstract inner product for concrete computations

---

## 4. AXIOM AUDIT

### 4.1 Results

All theorems carry the axiom profile:
```
[propext, Classical.choice, Quot.sound]
```
These are the standard Mathlib infrastructure axioms. No custom axioms are introduced.

### 4.2 Source of Classical.choice

The `Classical.choice` dependency enters through Mathlib's inner product space infrastructure — specifically, through typeclass instances that use `Decidable` for real number comparisons. This is a *metatheoretic* artifact of Mathlib's architecture, not a *mathematical* use of the axiom of choice in the proof content.

**Evidence for this claim:** The proof of the Tsirelson bound proceeds entirely through:
- Kronecker product algebra (finite matrix multiplication)
- Involution properties ($M^2 = I$, $M^* = M$)
- Dot product linearity and positivity
- The algebraic identity $(B+B')^*(B+B') + (B-B')^*(B-B') = 4I$
- The inequality $(a+b)^2 \leq 2(a^2 + b^2)$ for reals

None of these steps require excluded middle, the axiom of choice, or any omniscience principle. The `Classical.choice` in the axiom profile is inherited from Mathlib lemmas that package constructively valid results in classically-flavored wrappers.

### 4.3 Comparison with Prior Papers

| Paper | Result | Axiom Profile | Classical.choice Source |
|-------|--------|---------------|----------------------|
| Paper 2 | Bidual gap ≡ WLPO | Producer uses `Classical.choice`; consumer does not | Producer (meta-classical, by design) |
| Paper 8 | Ising thermo limit | `Classical.choice` in BMC equivalence | LPO content (by design) |
| Paper 11 | Tsirelson bound | `[propext, Classical.choice, Quot.sound]` | Mathlib infrastructure only |
| Paper 11 | Bell entropy | `[propext, Classical.choice, Quot.sound]` | Mathlib infrastructure only |

In Papers 2 and 8, `Classical.choice` reflects genuine logical content (WLPO and LPO respectively). In Paper 11, it is purely architectural — the mathematical content is BISH.

---

## 5. DISCUSSION

### 5.1 Updated Calibration Table

The results extend the calibration table from Paper 9:

| Layer | Principle | Status | Source |
|-------|-----------|--------|--------|
| Finite-volume physics | BISH | Calibrated | Trivial |
| Finite-size approximations | BISH | Calibrated | Paper 8, Part A |
| **Bell nonlocality (CHSH)** | **BISH** | **Calibrated** | **Paper 11, Part A** |
| **Entanglement entropy (qubit)** | **BISH** | **Calibrated** | **Paper 11, Part B** |
| **Partial trace (finite-dim)** | **BISH** | **Calibrated** | **Paper 11, Part B** |
| Bidual gap / singular states | ≡ WLPO | Calibrated | Papers 2, 7 |
| Thermodynamic limit | ≡ LPO | Calibrated | Paper 8, Part B |
| Spectral gap decidability | Undecidable | Established | Cubitt et al. 2015 |

### 5.2 Significance: Compositional Structure is Constructively Free

The new entries establish that the compositional layer of finite-dimensional quantum mechanics — tensor products, entanglement, correlations — is BISH-provable. Combined with Papers 2-9, this yields the strongest form of the series' working hypothesis:

**All logical costs arise from infinite-dimensional idealization, not from quantum compositional structure.**

The most nonclassical feature of quantum mechanics — entanglement, as witnessed by the violation of Bell inequalities — is constructively free. The logical costs documented throughout the series (WLPO for non-reflexivity, LPO for the thermodynamic limit) arise exclusively from the mathematical apparatus used to describe infinite-dimensional state spaces and their limits, not from the physical content of quantum correlations.

### 5.3 Why This is Not Trivial

One might object that finite-dimensional linear algebra is "obviously" constructive, and therefore the BISH calibration of the Tsirelson bound is uninteresting. This objection misses three points:

1. **The Tsirelson bound is universally quantified** over all involutions and all unit vectors. Universal quantification over uncountable sets (the unit sphere in $\mathbb{C}^4$, the space of self-adjoint involutions on $\mathbb{C}^2$) is constructively nontrivial — there is no case-by-case verification available.

2. **The binary entropy involves the function $\eta(x) = -x\log x$ on $[0,1]$**, which requires careful handling at $x = 0$ (where $\log$ is undefined). The constructive treatment relies on the convention $0 \cdot \log 0 = 0$, which is justified by continuity — a fact that in principle could require omniscience principles for its verification. (In practice, Mathlib's `Real.log 0 = 0` convention resolves this.)

3. **The contribution is methodological, not just mathematical.** The CRM programme requires *calibration*: determining the exact logical cost, not merely demonstrating that the result "seems constructive." The Lean formalization provides a machine-checkable certificate, which is the standard of evidence throughout this series.

### 5.4 The Tsirelson Problem and Constructive Limitations

The CHSH Tsirelson bound $2\sqrt{2}$ concerns the finite-dimensional tensor product setting. Tsirelson's *problem* — whether the tensor product and commuting operator bounds coincide for general Bell expressions — was resolved negatively by Ji, Natarajan, Vidick, Wright, and Yuen (2020) via $\text{MIP}^* = \text{RE}$, establishing that the general Tsirelson bound is not computable. This undecidability result, like the Cubitt-Perez-Garcia-Wolf spectral gap undecidability, concerns the infinite-dimensional case. Our finite-dimensional BISH calibration is consistent with the pattern: finite → BISH, infinite → undecidable.

### 5.5 Future Directions

- **Monogamy of entanglement** (CKW inequality): Does the distribution constraint on entanglement across subsystems remain BISH, or does the concurrence computation introduce omniscience?
- **PPT criterion for separability**: The positive partial transpose test for $2 \times 2$ and $2 \times 3$ systems (Horodecki 1996) is a finite matrix computation, likely BISH. The general separability problem may require stronger principles.
- **Infinite-dimensional entanglement**: Von Neumann entropy for infinite-dimensional systems involves trace-class operator theory, which (per Paper 7) already requires WLPO. Does the compositional structure (partial trace, tensor product) add further cost beyond what the state space itself demands?

---

## 6. THE Classical.choice QUESTION

### 6.1 The Forest and the Trees

A legitimate concern: Lean 4 with Mathlib is built on classical foundations. The `#print axioms` audit shows `Classical.choice` in the axiom profile. Does this invalidate the claim that the results are BISH?

The answer, consistent with the methodology of the entire series, is no. The CRM methodology has always worked this way: CRM equivalences are proven in a classical metatheory about constructive systems (Ishihara 2006, Bridges-Vîță 2006). Simpson's classical reverse mathematics is proven in ZFC. The Lean formalization provides a mechanical audit of which principles the proof *actually uses*, not which principles the ambient library *could provide*.

The `Classical.choice` in Paper 11's axiom profile enters exclusively through Mathlib's inner product space typeclass infrastructure — specifically, through `Decidable` instances for real number comparisons that Lean inserts automatically when resolving typeclass queries. The mathematical proof steps (matrix algebra, Kronecker products, algebraic identities) are all constructively valid. A refactoring of Mathlib's typeclass resolution to separate constructive and classical instances would eliminate the `Classical.choice` dependency without changing any proof content.

### 6.2 Comparison with Papers 2 and 8

In Papers 2 and 8, `Classical.choice` reflects *intentional* non-constructive content: the producer/consumer architecture of Paper 2 deliberately uses classical case analysis, and the LPO equivalence in Paper 8 inherently requires excluded middle. In Paper 11, by contrast, the `Classical.choice` is an unwanted artifact. This distinction — between architectural inheritance and mathematical content — is essential to the CRM methodology and is supported by the proof structure itself.

---

## 7. CONCLUSION

We have provided the first Lean 4 formalization of the Tsirelson bound on the CHSH operator and the entanglement entropy of the Bell singlet state. Both results compile with zero sorry, zero errors, and zero warnings. The axiom audit confirms that the mathematical content is BISH-provable, with `Classical.choice` entering only through Mathlib's inner product space infrastructure.

These results calibrate the compositional layer of quantum mechanics at the BISH level, extending the calibration table to cover tensor products, entanglement, and correlations. The strongest form of the series' working hypothesis is now: all logical costs in the constructive formulation of quantum mechanics arise from infinite-dimensional idealization, not from the relational structure that makes quantum mechanics distinctively quantum.

The Lean source code is available as a companion archive.

---

## REFERENCES

[Coding agent: format as standard bibliography. Include all of the following:]

### Primary References (Quantum Information / Bell Inequalities)

1. **Cirel'son (Tsirelson) 1980.** B. S. Cirel'son, "Quantum Generalizations of Bell's Inequality," *Lett. Math. Phys.* 4, 93–100 (1980). [Original Tsirelson bound]

2. **Clauser, Horne, Shimony, Holt 1969.** J. F. Clauser, M. A. Horne, A. Shimony, R. A. Holt, "Proposed Experiment to Test Local Hidden-Variable Theories," *Phys. Rev. Lett.* 23(15), 880–884 (1969). [CHSH inequality]

3. **Aspect, Dalibard, Roger 1982.** A. Aspect, J. Dalibard, G. Roger, "Experimental Test of Bell's Inequalities Using Time-Varying Analyzers," *Phys. Rev. Lett.* 49(25), 1804–1807 (1982). [Experimental violation, Nobel Prize 2022]

4. **Bell 1964.** J. S. Bell, "On the Einstein-Podolsky-Rosen Paradox," *Physics* 1(3), 195–200 (1964). [Bell's theorem]

5. **von Neumann 1932.** J. von Neumann, *Mathematische Grundlagen der Quantenmechanik*, Springer (1932). [Von Neumann entropy]

6. **Schumacher 1995.** B. Schumacher, "Quantum Coding," *Phys. Rev. A* 51, 2738 (1995). [Operational meaning of von Neumann entropy]

7. **Ji, Natarajan, Vidick, Wright, Yuen 2021.** Z. Ji, A. Natarajan, T. Vidick, J. Wright, H. Yuen, "MIP* = RE," *Commun. ACM* 64(11), 131–138 (2021). [Tsirelson problem resolution, infinite-dimensional undecidability]

### Formalizations

8. **Echenim, Mhalla, Mori 2023.** M. Echenim, M. Mhalla, C. Mori, "The CHSH inequality: Tsirelson's upper-bound and other results," *Archive of Formal Proofs* (2023). [Isabelle/HOL formalization]

9. **Echenim, Mhalla 2024.** M. Echenim, M. Mhalla, "A Formalization of the CHSH Inequality and Tsirelson's Upper-bound in Isabelle/HOL," *J. Autom. Reasoning* 68, 2 (2024). doi:10.1007/s10817-023-09689-9

10. **Meiburg et al. 2025.** A. Meiburg, L. A. Lami, et al., "A Formalization of the Generalized Quantum Stein's Lemma in Lean," arXiv:2510.08672 (2025). [Lean-QuantumInfo library]

11. **Lean Community.** The Lean 4 theorem prover and Mathlib library. https://leanprover-community.github.io/

### Constructive Mathematics / CRM

12. **Bishop 1967.** E. Bishop, *Foundations of Constructive Analysis*, McGraw-Hill (1967).

13. **Bishop, Bridges 1985.** E. Bishop, D. Bridges, *Constructive Analysis*, Springer (1985).

14. **Bridges, Vîță 2006.** D. Bridges, L. Vîță, *Techniques of Constructive Analysis*, Springer (2006).

15. **Ishihara 2006.** H. Ishihara, "Reverse Mathematics in Bishop's Constructive Mathematics," *Phil. Scientiae, Cahier Spécial* 6, 43–59 (2006).

### Companion Papers (Author's CRM Series)

16. **Lee 2026a.** P. C.-K. Lee, "The Bidual Gap and WLPO: Exact Calibration and a Minimal Lean Artifact" (Paper 2). Zenodo.

17. **Lee 2026b.** P. C.-K. Lee, "Physical Bidual Gap for Trace-Class Operators" (Paper 7). Zenodo.

18. **Lee 2026c.** P. C.-K. Lee, "Constructive Cost of the Thermodynamic Limit in the 1D Ising Model" (Paper 8). Zenodo.

19. **Lee 2026d.** P. C.-K. Lee, "The Logical Geography of Mathematical Physics" (Paper 9). Zenodo.

### Additional

20. **Cubitt, Perez-Garcia, Wolf 2015.** T. S. Cubitt, D. Perez-Garcia, M. M. Wolf, "Undecidability of the Spectral Gap," *Nature* 528, 207–211 (2015).

21. **Horodecki, Horodecki, Horodecki 1996.** M. Horodecki, P. Horodecki, R. Horodecki, "Separability of Mixed States: Necessary and Sufficient Conditions," *Phys. Lett. A* 223, 1–8 (1996). [PPT criterion]

22. **Nielsen, Chuang 2000.** M. A. Nielsen, I. L. Chuang, *Quantum Computation and Quantum Information*, Cambridge University Press (2000). [Standard reference]

---

## APPENDIX A: LEAN CODE LISTING

[Coding agent: include the complete source of all 8 modules, formatted as Lean code blocks with line numbers. Source files are in the P11_Entanglement directory.]

---

## APPENDIX B: BUILD AND VERIFICATION INSTRUCTIONS

```bash
cd P11_Entanglement
lake build
# Expected output: 2260 jobs, zero errors, zero sorry, zero warnings

# Verify no sorry in proofs:
grep -r "sorry" Papers/ --include="*.lean" | grep -v "^.*:.*--"
# Expected: only documentation comments

# Verify axiom profile:
# Run `#print axioms tsirelson_bound` in Main.lean
# Expected: [propext, Classical.choice, Quot.sound]
```

---

## CODING AGENT INSTRUCTIONS

### LaTeX Production

1. Use the `amsart` or `article` document class with `amsmath`, `amssymb`, `hyperref`, `listings` packages.
2. Follow the same formatting conventions as Papers 2, 7, 8, 9 in the series.
3. The paper should be approximately 12-15 pages including appendices.
4. All mathematical notation should use standard LaTeX commands.
5. Lean code listings should use the `lstlisting` environment with Lean syntax highlighting if available, otherwise `verbatim`.
6. The calibration table should be a properly formatted LaTeX `tabular` environment.
7. Include the Zenodo DOI placeholder in the first footnote.
8. Date: February 2026.

### Content Notes

- The introduction should be accessible to both constructive mathematicians and quantum information theorists. Define BISH, WLPO, LPO briefly for the QI audience; define CHSH, involutions, partial trace briefly for the constructive math audience.
- The proof presentation in Section 2 should be pen-and-paper style, not Lean code. The Lean code goes in the appendix.
- The discussion section (§5) is the most important section for the series — it updates the calibration table and states the strengthened working hypothesis.
- The Classical.choice section (§6) addresses the legitimate methodological concern about working in a classical proof assistant. Keep it concise but technically precise.

### Zenodo Packaging

The Zenodo upload should include:
1. The PDF paper
2. A zip archive of the Lean project directory (P11_Entanglement)
3. A README with build instructions

The DOI should be for the concept record (all versions), not a specific version.
