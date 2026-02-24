# Paper 15: Writing Instructions for Coding Agent

## Title

**Noether's Theorem and the Logical Cost of Global Conservation Laws**

P.C.K. Lee

## Target

12–15 pages, academic paper. LaTeX-style formatting in Markdown (to be converted to PDF or docx). Equations in LaTeX math mode. Same tone and format as Papers 8, 13, 14 in the programme.

---

## Abstract (~150 words)

Noether's theorem — that every continuous symmetry of the action yields a conserved current — is the most fundamental structural principle in physics. We show it splits cleanly across the constructive hierarchy. The local conservation law (∂_μ J^μ = 0) is an algebraic identity provable in Bishop's constructive mathematics (BISH). The finite-volume conserved charge is a computable real number (BISH). The global conserved charge — the assertion that the total energy of an infinite system exists as a definite real number — is equivalent to the Limited Principle of Omniscience (LPO) via Bounded Monotone Convergence (BMC), precisely when the conserved density is non-negative (as for energy, via the weak energy condition). All results are formalised in Lean 4 with machine-checked proofs (520 lines, zero sorry). This constitutes a fourth independent domain — after statistical mechanics, general relativity, and quantum decoherence — exhibiting the same BISH/LPO boundary at bounded monotone convergence, and the first to calibrate a structural law rather than a physical prediction.

---

## 1. Introduction (1.5 pages)

### Content

Open with Noether 1918. State the theorem in its classical form: every continuous symmetry of the action functional yields a conserved current. Note the theorem's centrality — it generates conservation of energy (time translation), momentum (space translation), angular momentum (rotation), electric charge (U(1) gauge), and every other conservation law in the Standard Model. Quote Lederman & Hill's assessment (from their book *Symmetry and the Beautiful Universe*) that it is "one of the most important mathematical theorems ever proved in guiding the development of modern physics."

State the question this paper addresses: **What is the logical cost of Noether's theorem?** More precisely: does the theorem, or its consequences, require non-constructive principles?

State the answer in one paragraph: The theorem itself — local current conservation — is constructive (BISH). It is an algebraic identity that follows from the equations of motion by finite manipulation. The finite-volume conserved charge is a computable real number. The non-constructive content enters only when one asserts that the *total* conserved charge of an infinite system exists as a definite real number. For positive-definite densities (energy), this is a bounded monotone limit, equivalent to LPO. For signed densities (electric charge), the convergence is oscillatory and does not fit the BMC pattern.

State the programme context: This is the fourth independent domain in a programme of constructive calibration of mathematical physics. The previous three domains are:
- **Statistical mechanics** (Paper 8): Ising free energy. Finite-volume free energy f_N is BISH; thermodynamic limit f_∞ = lim f_N is LPO via BMC.
- **General relativity** (Paper 13): Schwarzschild singularity. Finite geodesic computations are BISH; the assertion r(τ) → 0 is LPO via BMC.
- **Quantum mechanics** (Paper 14): Decoherence. Finite-step coherence bounds are BISH; exact decoherence (c → 0) is LPO via BMC.

All four domains produce bounded monotone sequences whose completed limits cost exactly LPO. The physics differs completely — partition functions, geodesic equations, density matrices, energy densities — but the logical structure is identical.

State what makes Paper 15 different: Papers 8, 13, 14 calibrate *predictions* (free energy values, singularity formation, measurement outcomes). Paper 15 calibrates a *structural law* — the principle that symmetries generate conservation laws. The local form of this law (the algebraic content of Noether's theorem) is constructive. The global form (total conserved charge exists) is the idealization.

### Key references to cite

- Noether, E. (1918). "Invariante Variationsprobleme." *Nachr. d. König. Gesellsch. d. Wiss. zu Göttingen, Math-phys. Klasse*, 235–257.
- Bañados, M. & Reyes, I.A. (2016). "A short review on Noether's theorems, gauge symmetries and boundary terms, for students." arXiv:1601.03616.
- Skopenkov, M. (2023). "Discrete field theory: symmetries and conservation laws." *Math. Phys. Anal. Geom.* 26, 19. arXiv:1709.04788.
- Previous papers in the programme (8, 13, 14).

---

## 2. Background: Constructive Reverse Mathematics (1 page)

### Content

Brief recap (readers of Papers 8, 13, 14 will know this; new readers need context):

**BISH** (Bishop's constructive mathematics): mathematics with intuitionistic logic, no excluded middle, no omniscience principles. All existence proofs are constructive — they produce the object, not just deny its non-existence. Finite computations, explicit bounds, computable real arithmetic all live here.

**LPO** (Limited Principle of Omniscience): For every binary sequence (a_n), either ∃n (a_n = 1) or ∀n (a_n = 0). Classically trivial; constructively strong. Equivalent to: every bounded monotone sequence converges (BMC, the monotone convergence theorem). This equivalence is due to Mandelkern (1988) and is a standard result of constructive reverse mathematics.

**BMC** (Bounded Monotone Convergence): Every bounded monotone sequence of reals has a limit. LPO ↔ BMC is the key equivalence exploited in this programme.

**The diagnostic:** When a physical theorem asserts the existence of a completed infinite limit (thermodynamic limit, singularity, decoherence, global charge), check whether the underlying sequence is bounded and monotone. If yes, the assertion costs exactly LPO. If the sequence has computable modulus of convergence, the limit is BISH and LPO is not needed. The programme identifies physical theorems where the modulus is naturally absent.

**NPSC** (Non-negative Partial Sum Convergence): A new abstraction introduced in this paper. A series Σ d_n with d_n ≥ 0 converges iff the partial sums (which are monotone increasing and bounded) converge. NPSC ↔ BMC ↔ LPO. This is the abstract framework connecting energy partial sums to the omniscience hierarchy.

### Key references

- Bishop, E. (1967). *Foundations of Constructive Analysis*. McGraw-Hill.
- Bishop, E. & Bridges, D. (1985). *Constructive Analysis*. Springer.
- Bridges, D. & Richman, F. (1987). *Varieties of Constructive Mathematics*. Cambridge University Press.
- Bridges, D. & Vîță, L. (2006). *Techniques of Constructive Analysis*. Springer.
- Ishihara, H. (2006). "Reverse Mathematics in Bishop's Constructive Mathematics." *Philosophia Scientiæ*, CS 6, 43–59.
- Diener, H. (2018). "Constructive Reverse Mathematics." arXiv:1804.05495.
- Mandelkern, M. (1988). "Limited omniscience and the Bolzano-Weierstrass principle." *Bull. London Math. Soc.* 20, 319–320.
- Ishihara, H. & Nemoto, T. (2019). "The Monotone Completeness Theorem in Constructive Reverse Mathematics." In *Mathesis Universalis, Computability and Proof*, Synthese Library 412, Springer.

---

## 3. The Physics: Noether's Theorem on the Lattice (2 pages)

### 3.1 The Model

Scalar field on a 1D lattice with periodic boundary conditions. N sites, field values φ_i ∈ ℝ, conjugate momenta π_i ∈ ℝ.

Lattice Lagrangian:
$$L_N = \sum_{i=1}^{N} \left[ \frac{1}{2} \pi_i^2 - \frac{1}{2}(\phi_{i+1} - \phi_i)^2 - V(\phi_i) \right]$$

with V(φ) ≥ 0 (non-negative potential) and periodic BC: φ_{N+1} = φ_1.

Equations of motion (discrete Euler-Lagrange):
$$\dot{\phi}_i = \pi_i, \qquad \dot{\pi}_i = (\phi_{i+1} - 2\phi_i + \phi_{i-1}) - V'(\phi_i)$$

Energy (conserved quantity from time-translation invariance):
$$E_N = \sum_{i=1}^{N} \left[ \frac{1}{2} \pi_i^2 + \frac{1}{2}(\phi_{i+1} - \phi_i)^2 + V(\phi_i) \right]$$

Note: every term in E_N is non-negative (squares and non-negative potential). This is the critical property.

### 3.2 Why the Lattice

Explain why we work on the lattice rather than in the continuum:

1. **Physical honesty:** Lattice field theory is how physics is actually computed (lattice QCD, lattice gauge theory). The continuum limit is itself an idealization whose logical cost could be separately calibrated.
2. **Lean practicality:** Everything is finite sums over Fin N. No Sobolev spaces, no distributions, no functional analysis infrastructure.
3. **Structural completeness:** The lattice model captures all three levels of the hierarchy — local conservation (algebraic identity), finite-volume energy (computable), infinite-volume energy (BMC).

Cite Skopenkov (2023) for the mathematical theory of discrete Noether theorems.

### 3.3 The Sign Observation

**Critical insight:** The logical cost of a global conservation law depends on whether the conserved density is positive definite.

- **Energy density** (T^{00}): Sum of squares plus non-negative potential. Always ≥ 0. Partial energies E_R are monotone increasing in R. → BMC → LPO.
- **Charge density** (J^0): Signed (positive for particles, negative for antiparticles). Partial charges Q_R oscillate as R grows. → Conditional convergence, does not fit BMC.

This parallels the weak energy condition in general relativity: T_{ab} v^a v^b ≥ 0 for all timelike v^a. The positivity of energy density is a physical assumption, not a mathematical one. The programme shows this physical assumption is precisely what makes the infinite-volume limit cost LPO rather than something else.

Cite:
- Witten, E. (1981). "A New Proof of the Positive Energy Theorem." *Commun. Math. Phys.* 80, 381–402.
- Kontou, E.-A. & Sanders, K. (2020). "Energy conditions in general relativity and quantum field theory." *Class. Quantum Grav.* 37, 193001. arXiv:2003.01815.

---

## 4. Finite Noether at BISH (2 pages)

### 4.1 The Conservation Identity

State and prove the conservation theorem:

**Theorem (noether_conservation).** For any solution of the discrete equations of motion with periodic boundary conditions, dE_N/dt = 0.

**Proof sketch:** Differentiate E_N with respect to t. The kinetic terms contribute π_i · π̇_i. The gradient terms contribute (φ_{i+1} - φ_i)(π_{i+1} - π_i). The potential terms contribute V'(φ_i) · π_i. Substitute the equations of motion: π̇_i = Δφ_i - V'(φ_i). The V'(φ_i)π_i terms cancel between kinetic and potential contributions. The gradient contributions telescope by periodic boundary conditions (the sum over i of (φ_{i+1} - φ_i)π_{i+1} minus (φ_{i+1} - φ_i)π_i gives a telescoping cancellation when summed over the periodic lattice). Result: dE_N/dt = 0.

**Logical status:** Every step is finite arithmetic over Fin N. The telescoping uses periodic BC (finite sum with wrapping indices). No limits, no compactness, no choice. BISH.

**Axiom certificate:** Lean `#print axioms` shows only propext, Classical.choice (Mathlib infrastructure for Fin.fintype and Real.instField), Quot.sound. No omniscience principles.

### 4.2 Non-negativity of Energy Density

**Theorem (energyDensity_nonneg).** If V(φ) ≥ 0 for all φ, then each term in E_N is non-negative.

**Proof:** ½π² ≥ 0 (square), ½(Δφ)² ≥ 0 (square), V(φ) ≥ 0 (hypothesis).

This is the theorem that makes Part B work.

### 4.3 Monotonicity of Partial Energies

**Theorem (partialEnergy_mono).** For a field on the infinite lattice ℕ, the partial energy E_N = Σ_{i=0}^{N-1} ε_i is monotone increasing in N.

**Proof:** E_{N+1} = E_N + ε_N ≥ E_N since ε_N ≥ 0.

**Logical status:** BISH. Uses only non-negativity and Finset.sum_le_sum_of_subset_of_nonneg.

---

## 5. Global Energy and LPO (2 pages)

### 5.1 The Abstract Framework: NPSC

**Definition.** NPSC (Non-negative Partial Sum Convergence): Every bounded sequence of partial sums Σ_{i=0}^{N-1} d_i with d_i ≥ 0 converges.

**Theorem (npsc_iff_bmc).** NPSC ↔ BMC.

**Proof sketch:** Forward: an NPSC sequence is bounded and monotone increasing, so it satisfies BMC. Reverse: given a bounded monotone increasing sequence (a_n), set d_n = a_{n+1} - a_n ≥ 0. The partial sums Σ d_i = a_{N} - a_0, so NPSC gives convergence of a_n.

**Logical status:** BISH. No omniscience principles needed for the abstract equivalence.

**Theorem (npsc_iff_lpo).** NPSC ↔ LPO.

**Proof:** Compose npsc_iff_bmc with bmc_iff_lpo (the latter axiomatised from Paper 8, citing Mandelkern 1988 / Bridges-Vîță 2006).

### 5.2 The Headline Result

**Theorem (global_energy_iff_LPO).** The assertion "for every bounded field configuration with non-negative energy density, the total energy E = lim_{N→∞} E_N exists" is equivalent to LPO.

**Proof:** The partial energy sequence {E_N} is monotone increasing (by non-negativity) and bounded (by hypothesis). Asserting its limit exists is NPSC. By npsc_iff_lpo, this is LPO.

**The encoding (reverse direction):** Given an arbitrary bounded monotone increasing sequence (a_n), construct a field configuration on ℕ whose partial energies are exactly a_N - a_0. (Set gradient and kinetic terms to zero; encode the increments a_{n+1} - a_n into the potential energy at each site.) This shows that if global energy always exists, then every bounded monotone sequence converges (BMC), which is LPO.

### 5.3 Axiom Certificate

Lean `#print axioms` for global_energy_iff_LPO shows propext, Classical.choice, Quot.sound, plus bmc_of_lpo and lpo_of_bmc (the only custom axioms, cited from Paper 8 and Bridges-Vîță 2006).

The abstract framework (npsc_iff_bmc) is pure BISH — no custom axioms. Same pattern as Paper 14's abc_iff_bmc.

---

## 6. The Sign Trap: Why Charge Doesn't Work (1 page)

### Content

Explain why the argument fails for electric charge (or any signed conserved density).

For a complex scalar field with U(1) symmetry, the conserved current is:
$$J^0 = i(\phi^* \dot{\phi} - \dot{\phi}^* \phi)$$

This is signed — positive for particles, negative for antiparticles. The partial charge Q_R = Σ_{i=0}^{R-1} J^0_i is not monotone. Adding more sites can increase or decrease Q_R depending on the charge distribution.

The convergence of Q_R as R → ∞ is a conditional convergence problem, not a monotone convergence problem. It does not map to BMC. Asserting convergence requires either:
- Explicit decay rates (collapsing to BISH), or
- Stronger principles than LPO (e.g., Bolzano-Weierstrass for subsequences).

**The lesson:** The constructive calibration depends not just on the theorem (Noether) but on the *physical content* of the conserved quantity. Positivity (the weak energy condition) is what makes the BMC pattern available. The sign structure of the density is logically significant.

This is analogous to the distinction in Paper 14 between uniform-angle decoherence (geometric decay, BISH) and variable-angle decoherence (general monotone, LPO). The specific model determines where in the hierarchy the result lands.

---

## 7. Domain Invariance (1.5 pages)

### 7.1 The Updated Calibration Table

Present the full table:

| Domain | Paper | Physical System | Bounded Monotone Sequence | BISH Content | LPO Content |
|--------|-------|----------------|--------------------------|--------------|-------------|
| Stat. Mech. | 8 | Ising model | Free energy f_N | f_N computed, ε-bounds | f_∞ = lim f_N |
| Gen. Relativity | 13 | Schwarzschild | Radial coordinate r(τ) | r(τ) computed to precision ε | r(τ) → 0 (singularity) |
| Quantum Mechanics | 14 | Decoherence | Off-diagonal coherence c(N) | c(N) < ε for explicit N₀ | c(N) → 0 (collapse) |
| **Conservation Laws** | **15** | **Scalar field energy** | **Partial energy E_N** | **dE/dt = 0, E_N computed** | **E = lim E_N exists** |

### 7.2 What Domain Invariance Means

Four independent physical domains. Different physics:
- **Paper 8:** Partition functions, Boltzmann weights, log-sums
- **Paper 13:** Geodesic equations, Schwarzschild metric, proper time
- **Paper 14:** Density matrices, Kronecker products, partial trace
- **Paper 15:** Lagrangians, symmetry flows, energy densities

Same logical structure: bounded monotone sequence, finite truncations at BISH, completed limit at LPO. Same abstract equivalence (BMC ↔ LPO) instantiated in each domain.

One instance is a result. Two is a pattern. Three is evidence. Four begins to look like a structural feature of how physical theories relate to mathematical frameworks.

### 7.3 What Paper 15 Adds

Paper 15 is qualitatively different from the other three. Papers 8, 13, 14 calibrate *predictions* — quantities physicists compute and compare to experiment. Paper 15 calibrates a *principle* — the structural law that symmetries generate conservation laws. The local form (Noether's algebraic identity) is constructive. The global form (total charge exists) is the idealization. This means:

**The architecture of physical law is constructive.** The idealization enters not in the law itself but in the totality assertion — the claim that the conserved quantity exists as a definite number summed over all of space. This is a statement about formalism, not nature. No finite experiment distinguishes "total energy = E" from "partial energy E_N agrees with E to within ε for all N we can probe."

---

## 8. Lean Formalisation (1.5 pages)

### 8.1 Module Structure

| File | Lines | Content |
|------|-------|---------|
| Defs.lean | ~90 | Lattice field types, energy density, total/partial energy, non-negativity |
| EulerLagrange.lean | ~80 | Equations of motion, conservation identity (Noether theorem) |
| LocalConservation.lean | ~90 | Periodic BC shift lemmas, telescoping sum, dE/dt = 0 |
| Monotonicity.lean | ~60 | partialEnergy_mono, partialEnergy_nonneg |
| LPO_BMC.lean | ~40 | LPO, BMC, NPSC definitions, axiomatised BMC ↔ LPO |
| GlobalEnergy.lean | ~160 | npsc_iff_bmc (BISH!), encoding, global_energy_iff_LPO |

Total: ~520 lines. Zero sorry. Zero warnings. Clean build (1950 jobs).

### 8.2 Axiom Certificates

**Part A (BISH):** noether_conservation, energyDensity_nonneg, totalEnergy_nonneg, partialEnergy_mono, sum_shift, sum_shift_prev, all periodic BC lemmas. Axioms: propext, Classical.choice (Mathlib infrastructure only: Fin.fintype, Real.instField), Quot.sound. No omniscience principles.

**Part B (LPO):** npsc_iff_bmc (pure BISH!), npsc_iff_lpo, global_energy_iff_LPO. Additional axioms: bmc_of_lpo, lpo_of_bmc (cited from Bridges-Vîță 2006 and Paper 8).

**Classical.choice tracing:** Every instance traces to Fin.fintype or Real.instField — type-theoretic infrastructure for finite types and real number construction, not logical uses of excluded middle. No Classical.em, no Classical.byContradiction, no decide on propositions anywhere in the source code.

### 8.3 CRM Audit

The formalisation passes the CRM (Constructive Reverse Mathematics) audit standard established in Papers 8, 13, 14:
- Clean stratification (Part A never touches LPO axioms)
- Only declared axioms are bmc_of_lpo and lpo_of_bmc, properly cited
- Abstract framework (npsc_iff_bmc) is pure BISH
- by_cases uses decidable Nat equality (zero axioms), not Classical.em

---

## 9. Discussion (1.5 pages)

### 9.1 The Local/Global Distinction

The result sharpens the local/global distinction in physics. Local conservation (∂_μ J^μ = 0) is the empirical content — it determines what happens in any finite region. Global conservation (total charge exists) is the totalising assertion — it sums over all of space.

The constructive hierarchy reveals these are logically different claims. The local law is algebraic (BISH). The global assertion is infinitary (LPO). Physicists routinely treat them as equivalent ("conservation of energy"), but the programme shows they have different logical costs.

This has implications for quantum gravity, where the definition of total energy is notoriously problematic (no local energy density for the gravitational field; see Witten 1981 for the positive energy theorem). The programme suggests this difficulty is not an accident — total energy is an LPO-level assertion, and it becomes harder to formulate precisely in regimes where the positive-definiteness of T^{00} is not guaranteed.

### 9.2 Why Four Domains Matter

The accumulation of four independent domains all producing BMC ↔ LPO at the boundary between finite physics and infinite formalism suggests this is a structural feature, not a coincidence. There is no obvious physical reason why Ising partition functions, Schwarzschild geodesics, decoherence coherence, and energy densities should share logical structure. They describe completely different phenomena.

The common feature is that all four involve sequences of finite computations (BISH) whose completed limits (LPO) are physically meaningful but experimentally indistinguishable from sufficiently close finite approximations. The programme has not proved this is universal — there may be physical theorems whose logical cost is different (e.g., DC rather than LPO, as in the strong law of large numbers). But four independent data points sharing the same boundary is suggestive.

### 9.3 Limitations

1. **Lattice model:** We work on a lattice, not in the continuum. The continuum limit is itself an idealization whose logical cost could be separately calibrated. We expect it to introduce additional non-constructive content (function spaces, compactness), but this is not formalised here.

2. **Encoding is abstract:** The reverse direction (global energy → LPO) uses an encoding that maps arbitrary bounded monotone sequences to lattice field configurations. This encoding is mathematically valid but not physically natural — the resulting field configurations may not correspond to any realistic physical system. This is standard in reverse mathematics (the encoding in Paper 8 similarly produces non-physical Ising configurations).

3. **Energy only:** The result applies cleanly only to positive-definite conserved densities (energy, probability, number density). Signed densities (electric charge) do not fit the BMC pattern. A complete calibration of all Standard Model conservation laws would require separate analysis for each type of charge.

---

## 10. Conclusion (0.5 pages)

Noether's theorem splits across the constructive hierarchy. The local conservation law — the algebraic content of the theorem — is BISH. The global conserved charge — the assertion that total energy exists — is LPO, equivalent to bounded monotone convergence.

This is the fourth independent domain in which the BISH/LPO boundary falls at exactly the same place: the passage from finite computation to completed infinite limit. Four domains (statistical mechanics, general relativity, quantum measurement, conservation laws) with completely different physics, all producing bounded monotone sequences whose completed limits cost LPO.

The result calibrates not just a physical prediction but a structural principle. The architecture of physical law — the connection between symmetry and conservation — is constructive. The idealization enters through the totality assertion, not through the law itself.

---

## Bibliography

### Primary Sources

1. Noether, E. (1918). "Invariante Variationsprobleme." *Nachr. d. König. Gesellsch. d. Wiss. zu Göttingen, Math-phys. Klasse*, 235–257.

### Constructive Mathematics & Reverse Mathematics

2. Bishop, E. (1967). *Foundations of Constructive Analysis*. McGraw-Hill.
3. Bishop, E. & Bridges, D. (1985). *Constructive Analysis*. Grundlehren der mathematischen Wissenschaften 279, Springer.
4. Bridges, D. & Richman, F. (1987). *Varieties of Constructive Mathematics*. London Mathematical Society Lecture Note Series 97, Cambridge University Press.
5. Bridges, D. & Vîță, L. (2006). *Techniques of Constructive Analysis*. Universitext, Springer.
6. Ishihara, H. (2006). "Reverse Mathematics in Bishop's Constructive Mathematics." *Philosophia Scientiæ*, CS 6, 43–59.
7. Diener, H. (2018). "Constructive Reverse Mathematics." arXiv:1804.05495.
8. Mandelkern, M. (1988). "Limited omniscience and the Bolzano-Weierstrass principle." *Bull. London Math. Soc.* 20, 319–320.
9. Ishihara, H. & Nemoto, T. (2019). "The Monotone Completeness Theorem in Constructive Reverse Mathematics." In *Mathesis Universalis, Computability and Proof*, Synthese Library 412, Springer.

### Noether's Theorem & Symmetry

10. Bañados, M. & Reyes, I.A. (2016). "A short review on Noether's theorems, gauge symmetries and boundary terms, for students." arXiv:1601.03616.
11. Sardanashvily, G. (2016). *Noether's Theorems: Applications in Mechanics and Field Theory*. Studies in Variational Geometry, Springer.
12. Skopenkov, M. (2023). "Discrete field theory: symmetries and conservation laws." *Math. Phys. Anal. Geom.* 26, 19. arXiv:1709.04788.
13. Kosmann-Schwarzbach, Y. (2011). *The Noether Theorems: Invariance and Conservation Laws in the Twentieth Century*. Springer.
14. Byers, N. (1998). "E. Noether's Discovery of the Deep Connection Between Symmetries and Conservation Laws." arXiv:physics/9807044.

### Energy Conditions & Positive Energy

15. Witten, E. (1981). "A New Proof of the Positive Energy Theorem." *Commun. Math. Phys.* 80, 381–402.
16. Kontou, E.-A. & Sanders, K. (2020). "Energy conditions in general relativity and quantum field theory." *Class. Quantum Grav.* 37, 193001. arXiv:2003.01815.

### Lattice Field Theory

17. Creutz, M. (1983). *Quarks, Gluons and Lattices*. Cambridge University Press.

### Formal Verification

18. The Mathlib Community. (2020). "The Lean Mathematical Library." *Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs*, 367–381.
19. Jameson, T.R. et al. (2024). "Formalizing chemical physics using the Lean theorem prover." *Digital Discovery* 3, 264–280. (Notes Noether's theorem as a formalization target.)

### Programme Papers (cite as appropriate)

20. Lee, P.C.K. (2025). "Paper 8: The Ising Thermodynamic Limit and Bounded Monotone Convergence." [Programme reference]
21. Lee, P.C.K. (2025). "Paper 13: Singularity Formation in Schwarzschild Spacetime." [Programme reference]
22. Lee, P.C.K. (2026). "Paper 14: The Measurement Problem as a Logical Artefact." [Programme reference]

---

## Formatting Notes for Coding Agent

1. **Output format:** Create a Markdown file (.md) with LaTeX math. This can be converted to PDF via pandoc later.

2. **Equations:** Use $...$ for inline and $$...$$ for display math. Keep the LaTeX clean and standard.

3. **Tables:** Use Markdown tables. The calibration table (Section 7.1) is the most important visual element.

4. **Tone:** Technical, measured, not polemical. Same register as Papers 8, 13, 14. Let the results speak. Do not claim to have "solved" anything — claim to have *calibrated* the logical cost.

5. **Length:** Aim for 12–15 pages when typeset. Each section has its target length above.

6. **Critical warning (Section 6):** The sign trap section is essential. Without it, a reader might assume the result applies to all conservation laws. It applies only to positive-definite densities. Be precise.

7. **No follow-up questions.** End the paper with the conclusion, not a forward-looking question.

8. **Dedication:** None for this paper.

---

## Appendix: Lean Code Highlights

Include (in the paper itself, Section 8 or an appendix) the key theorem statements from the Lean source, typeset as code blocks:

```lean
/-- Noether's theorem: energy is conserved -/
theorem noether_conservation ...

/-- NPSC ↔ BMC (pure BISH, no omniscience) -/
theorem npsc_iff_bmc ...

/-- The headline result -/
theorem global_energy_iff_LPO ...
```

Pull the exact statements from the compiled Lean code. Do not paraphrase — show the actual theorem signatures.
