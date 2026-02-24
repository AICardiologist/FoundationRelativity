# Appendix: Guide to the Program — Significance and Structure of Papers 1–42

## Purpose

This appendix provides a structured guide to the 42 papers of the Constructive Reverse Mathematics and Physics program. Each paper is classified by its structural role (program-defining, major, significant, supporting, or confirmatory), and its principal finding is stated in a single sentence. The classification reflects the paper's contribution to the program as a whole, not its standalone technical difficulty.

---

## On the Necessity of Completeness

Individual calibrations in constructive reverse mathematics are, taken singly, unsurprising to specialists. That finite matrix arithmetic is BISH, that bounded monotone convergence requires LPO, that the extreme value theorem requires the Fan Theorem — these are textbook-level observations in the constructive analysis community, implicit in the work of Bishop (1967), Bridges and Richman (1987), and Ishihara (2006). No single entry in the calibration table constitutes a discovery.

*The discovery is the table.*

The BISH + LPO ceiling, the universality of Fekete's lemma as the sole mechanism for LPO entry, the dispensability of the Fan Theorem and Dependent Choice for every empirical prediction examined, the structural alignment between the BISH/LPO boundary and the perturbative/non-perturbative boundary in quantum field theory — none of these findings is visible from any single calibration, or from any five, or from any ten. They become visible only when the calibration is carried out systematically across the full landscape of mathematical physics: statistical mechanics, quantum mechanics, quantum field theory, general relativity, quantum information, classical mechanics, electrodynamics, particle physics, quantum gravity, holographic duality, and vacuum energy.

The program required approximately 60 calibrations across 12 domains before the pattern emerged with sufficient clarity to state as a thesis. This is why the work had not been done before: not because the individual calibrations are difficult — most can be reproduced by a specialist in an afternoon — but because the constructive analysis community and the mathematical physics community do not overlap, and neither community had reason to expect that a systematic survey would reveal a universal pattern. The present program is, to the author's knowledge, the first such survey, and the patterns it reveals — the ceiling, the universality, the dispensability — are its principal contribution.

---

## Principal Findings of the Program

Before cataloguing individual papers, we state the eleven findings that emerge from the calibration table taken as a whole. Each is a factual summary of results already established in the cited papers; none requires speculation.

### 1. The BISH + LPO Ceiling

Across approximately 60 calibrations in 12 physical domains — statistical mechanics, quantum mechanics, quantum field theory, general relativity, quantum information, thermodynamics, classical mechanics, electrodynamics, particle physics, quantum gravity, holographic duality, and vacuum energy — every empirical prediction requires at most BISH + LPO. No empirical prediction in the program has required LLPO, WLPO, the Fan Theorem, or Dependent Choice as irreducible logical cost. This is an observed pattern, not an assumed constraint. (Paper 35; calibration table in Paper 10.)

**Why this matters:** The entire mathematical apparatus of modern physics — Hilbert spaces, differential geometry, functional analysis, quantum field theory, general relativity — uses logical resources vastly exceeding BISH + LPO. Yet every number that can be compared to an experimental measurement requires only two ingredients: constructive computation (BISH) and one omniscience principle (LPO). The gap between the mathematics physicists use and the mathematics physics needs is enormous, and precisely measurable. This is the program's central empirical discovery.

### 2. Fan Theorem Dispensability

Compactness arguments — Arzelà–Ascoli, Banach–Alaoglu, the direct method of the calculus of variations, the existence of minimal surfaces — appear throughout mathematical physics but have not been required for any empirical prediction examined. The Fan Theorem governs the existence of extremizers, not the values of extrema. The values are computable at BISH or LPO; the existence claims are scaffolding. Paper 41 provides the sharpest instance: holography eliminates the FT cost of minimal surface existence entirely, computing the entropy (BISH) without constructing the surface (FT). (Paper 30; Paper 23; Paper 41.)

**Why this matters:** Compactness is the single most widely used tool in mathematical physics — it underpins the existence theorems for PDEs, the variational principles of mechanics, the convergence theorems of functional analysis, and the entirety of global differential geometry. Showing that none of this is needed for empirical predictions is a finding of the first magnitude: 150 years of mathematical infrastructure built on compactness is scaffolding over a simpler constructive core.

### 3. Dependent Choice Dispensability

Dependent Choice governs the strong law of large numbers and sequential construction arguments. Born probabilities are BISH; the frequentist convergence theorem requires DC. No empirical prediction in the program has required DC. The frequentist interpretation of probability is scaffolding over the BISH-computable Born rule. (Paper 31; Paper 25; Paper 16.)

**Why this matters:** Dependent Choice is the axiom that lets you build infinite sequences one step at a time — it is the engine behind every "take a sequence of approximations and extract a convergent subsequence" argument in analysis. The strong law of large numbers, ergodic theorems, and sequential compactness all depend on it. Showing that DC is dispensable for empirical predictions means that the entire statistical interpretation of quantum mechanics — the bridge from Born probabilities to observed frequencies — is scaffolding. Physics predicts individual probabilities (BISH); the story about what those probabilities "mean" in the long run costs DC and is logically unnecessary.

### 4. Fekete Universality

LPO enters physics through a single mechanism: the thermodynamic limit, mediated by Fekete's subadditive lemma (Fekete ≡ LPO, Paper 29). This mechanism is responsible for the LPO cost in every domain where LPO appears — the Ising phase transition (Paper 8), geodesic completeness (Paper 13), decoherence (Paper 14), Noether conservation laws (Paper 15), QCD confinement (Paper 33), and vacuum condensates (Paper 42). LPO is not a collection of unrelated non-constructivities. It is the single logical price of passing from finite-volume approximations to infinite-volume exact values.

**Why this matters:** Before this program, the non-constructive content of physics appeared to be scattered — a different obstacle in every domain, each requiring its own analysis. Fekete universality reveals that there is exactly one source of non-constructivity across all of physics: the passage from finite to infinite systems. Phase transitions, black hole horizons, decoherence, confinement, vacuum condensates — superficially unrelated phenomena across statistical mechanics, general relativity, quantum mechanics, and quantum field theory — all share a single logical mechanism. This is a unification result: the logical structure of physics is far simpler than its mathematical diversity suggests.

### 5. The Scaffolding Diagnostic Works

The framework correctly separates physically meaningful quantities from mathematical artifacts in cases where the answer is independently known. Casimir energy differences are BISH and experimentally verified; absolute vacuum energies are regulator-dependent and physically meaningless (Paper 42). Holographic entropy values are BISH; minimal surface existence is FT scaffolding that holography eliminates (Paper 41). Perturbative QES is BISH (Picard–Lindelöf); non-perturbative QES requires LPO (saddle-point competition). In each case, the framework's classification aligns with what physicists independently recognise as the physical content versus the mathematical infrastructure.

**Why this matters:** A diagnostic framework is only as good as its ability to recover known answers. The scaffolding diagnostic passes its most demanding tests: it correctly classifies Casimir differences as physical (BISH, experimentally verified) and absolute vacuum energies as unphysical (regulator-dependent, no convergence at any constructive level). It correctly identifies holographic entropy as the physical observable (BISH) and the bulk minimal surface as mathematical scaffolding (FT) — exactly what AdS/CFT practitioners already knew from the boundary theory. These are not cherry-picked examples; they are cases where physics has an independent answer, and the framework agrees with it. This track record is what justifies applying the diagnostic to open questions where the answer is not yet known.

### 6. Dissolution of the $10^{120}$

The cosmological constant "prediction" fails the scaffolding diagnostic. The unregularised vacuum energy does not converge to a real number at any level of the constructive hierarchy. Different regulators produce different finite values. A regulator-dependent quantity has no empirical content within the framework. The CRM analysis provides a formal expression of the post-naturalness position articulated by Martin (2012), Bianchi–Rovelli (2010), and Hossenfelder (2019): the $10^{120}$ is a property of a calculational choice, not of quantum field theory. (Paper 42.)

**Why this matters:** The 120-order-of-magnitude discrepancy between quantum field theory's "prediction" of vacuum energy and observation has been called the worst prediction in the history of physics. It has driven decades of research into supersymmetry, anthropic landscape arguments, and quintessence models. The CRM analysis shows that this entire research program may be addressing a non-problem: the quantity that disagrees with observation does not converge to a well-defined real number in the first place. The "prediction" is an artifact of treating a regulator-dependent intermediate step as if it were a physical quantity. This is not a philosophical opinion — it is a theorem about the convergence properties of the unregularised sum.

### 7. Duality as Axiom-Preserving Map

Paper 41 is the first test of a physical duality for logical consistency at the level of individual computational steps. The holographic dictionary preserves axiom cost across the bulk–boundary correspondence for every entry examined. This is a structural constraint on AdS/CFT that has not previously been articulated.

**Why this matters:** Dualities are the most powerful organising principle in modern theoretical physics. AdS/CFT — the correspondence between gravity in anti-de Sitter space and conformal field theory on its boundary — is the most studied duality of the past quarter-century. Yet no one had previously asked whether the dictionary preserves logical structure at the level of individual axioms. Finding that it does reveals a new structural property of holography: it is not merely a map between physical quantities but a map that preserves the constructive content of computations. This opens the question of whether axiom-preservation is a feature of all physical dualities or a special property of AdS/CFT.

### 8. Physical Undecidability Is Thermodynamic

The spectral gap undecidability of Cubitt–Perez-Garcia–Wolf, the most celebrated undecidability result in mathematical physics, reduces to LPO — the same principle governing every thermodynamic limit in the program (Papers 36–39). Undecidability in physics is not an exotic phenomenon requiring novel logical resources; it is the familiar non-computability of the infinite-volume limit, mediated by Fekete's lemma. Extensive observables at full precision cap at LPO; intensive observables without promise gaps can reach LPO′ (Σ₂⁰). No physical undecidability result examined has exceeded this stratification. (Paper 39.)

**Why this matters:** The Cubitt–Perez-Garcia–Wolf spectral gap result made international headlines as evidence that physics harbours deep undecidability. The natural reading was that physics is logically wild — potentially reaching arbitrary levels of the arithmetical hierarchy. The CRM analysis shows the opposite: physical undecidability is tame. It sits at exactly the same level (LPO) as every thermodynamic limit in statistical mechanics. The most undecidable thing in physics is precisely as undecidable as a boiling pot of water. This places a ceiling on physical undecidability that had not previously been conjectured, let alone established.

### 9. Bell ≡ Kochen–Specker

Bell's theorem and the Kochen–Specker theorem calibrate at the same level (LLPO) for a structural reason: both reduce to instances of the intermediate value theorem. Two theorems that the quantum foundations community treats as conceptually distinct are logically identical from the CRM perspective. LLPO enters quantum foundations through exactly one door — the IVT — just as LPO enters thermodynamics through Fekete. (Papers 21, 24, 27.)

**Why this matters:** Bell's theorem (nonlocality) and the Kochen–Specker theorem (contextuality) have been treated as separate pillars of quantum foundations for sixty years. They have distinct physical motivations, distinct proof strategies, and distinct literatures. The CRM analysis reveals that they are the same theorem at the logical level — both are instances of LLPO mediated by the intermediate value theorem. This is a genuine unification: two phenomena that appeared conceptually independent are logically identical. Moreover, just as LPO enters all of thermodynamics through a single mechanism (Fekete), LLPO enters all of quantum foundations through a single mechanism (IVT). The logical structure of quantum non-classicality is as unified as the logical structure of thermodynamics.

### 10. The Perturbative/Non-Perturbative Boundary Is the BISH/LPO Boundary

Perturbative QFT — tree-level amplitudes, one-loop corrections, RG running above ΛQCD — is BISH (algebraic operations on measured parameters). Non-perturbative QFT — exact condensates, confinement scale, thermodynamic limits of lattice approximations — requires LPO. The BISH/LPO boundary in the constructive hierarchy corresponds to the perturbative/non-perturbative boundary in quantum field theory. This is a structural alignment between two independently motivated distinctions — one logical, one physical — that has not previously been remarked. (Papers 32, 33, 34, 42.)

**Why this matters:** The perturbative/non-perturbative divide is the deepest methodological boundary in quantum field theory. Perturbative methods (Feynman diagrams, renormalisation group) are the workhorses of particle physics; non-perturbative methods (lattice QCD, instantons, exact results) are the frontier. The fact that this physical boundary aligns precisely with the BISH/LPO boundary in the constructive hierarchy is a striking coincidence that demands explanation. It means the distinction between "what we can calculate perturbatively" and "what we cannot" is not merely a practical limitation of current techniques — it is a logical boundary between finite algebraic computation (BISH) and infinite-volume limits (LPO). The perturbative/non-perturbative boundary has a logical explanation.

### 11. Born Probabilities Are BISH

The entire empirical content of quantum mechanics — every probability, every expectation value, every uncertainty bound — is BISH-computable. The measurement problem (LPO), the frequentist interpretation (DC), and the wavefunction collapse postulate are scaffolding over BISH-computable predictions. The framework provides a precise sense in which the interpretive debates in quantum foundations are debates about scaffolding, not about empirical content. (Papers 6, 11, 16.)

**Why this matters:** The measurement problem — how and why quantum superpositions yield definite outcomes — has been called the central unsolved problem of quantum mechanics. It has generated an entire field of interpretive debate (Copenhagen, many-worlds, pilot wave, decoherence, QBism). The CRM analysis does not solve the measurement problem, but it does something arguably more valuable: it shows that the measurement problem is logically orthogonal to empirical predictions. Every number that can be compared to an experiment — every Born probability, every expectation value, every uncertainty relation — is BISH-computable. The measurement problem lives at LPO. The interpretive debates are debates about scaffolding: logically real, but empirically inert. This is a precise, formal version of the "shut up and calculate" intuition, grounded in proof theory rather than philosophical preference.

### Open Question

Whether the BISH + LPO ceiling reflects a structural feature of physical law or a feature of its current mathematical formulations remains unresolved. The Noether charge/energy asymmetry (Paper 15) — where two physically equivalent conservation laws have different logical costs due to sign-definiteness of the integrand — is evidence that the hierarchy is partially sensitive to formulation choices. Paper 9's Ising invariance result is evidence in the other direction. The question of formulation-invariance is the program's principal open problem.

---

## Paper-by-Paper Catalogue

### Rating Key

- ★★★★★  Program-defining: the program cannot exist without this result
- ★★★★  Major structural contribution
- ★★★  Significant domain extension
- ★★  Important supporting calibration
- ★  Confirmatory or technical

---

### Program-Defining Results (★★★★★)

**Paper 29: Fekete's Subadditive Lemma Is Equivalent to LPO**
DOI: 10.5281/zenodo.18643617

The single most important technical result in the program. Every LPO calibration in every domain flows through this equivalence. Without Paper 29, the program has a collection of individual calibrations. With it, the program has a universal mechanism.

> *LPO enters physics through exactly one door — the thermodynamic limit — and Fekete's lemma is the key.*

---

**Paper 8: 1D Ising Model and LPO**
DOI: 10.5281/zenodo.18516813

The first complete bidirectional calibration: Ising thermodynamic limit ↔ LPO, proved in both directions with Lean verification. This is the template every subsequent LPO calibration follows. It proved the methodology works on real physics.

> *The phase transition in the simplest statistical mechanical model is equivalent to the limited principle of omniscience. Not "requires" — equivalent.*

---

**Paper 35: The Logical Constitution of Empirical Physics**
DOI: 10.5281/zenodo.18642616

The capstone theorem: BISH + LPO is the complete logical constitution of empirically accessible physics across all domains examined. This is the paper that states the ceiling as a thesis rather than a pattern.

> *Two principles — Bishop's constructive mathematics plus one omniscience principle — suffice for every empirical prediction in the Standard Model, general relativity, and quantum information theory.*

---

**Paper 30: Physical Dispensability of the Fan Theorem**
DOI: 10.5281/zenodo.18638394

Half of the deepest finding. Every compactness argument in mathematical physics — variational existence, Arzelà–Ascoli, Banach–Alaoglu — is scaffolding. No empirical prediction requires FT.

> *150 years of compactness arguments in physics bought mathematical elegance at zero empirical cost. The predictions survive without them.*

---

**Paper 31: Physical Dispensability of Dependent Choice**
DOI: 10.5281/zenodo.18645578

The other half. DC governs sequential constructions and the strong law of large numbers. No empirical prediction requires it.

> *The frequentist interpretation of probability is logically dispensable. Born probabilities are BISH. The convergence theorem that justifies interpreting them as frequencies costs DC and is scaffolding.*

---

**Paper 42: The Worst Prediction in Physics Is Not a Prediction**
DOI: 10.5281/zenodo.18654789

The strongest single application paper in the program. It dissolves a famous problem rather than merely classifying a known result. The unregularised vacuum energy does not converge to a real number at any level of the constructive hierarchy. The Casimir effect proves the diagnostic works: energy differences are BISH and experimentally verified; absolute energies are regulator-dependent and physically meaningless. The residual fine-tuning is an LPO equality — logically mundane.

> *The "worst prediction in physics" is not a prediction. The $10^{120}$ is a property of a calculational choice, not of quantum field theory. The genuine residual — 55-digit fine-tuning — lives at LPO, the same level as every thermodynamic limit in physics.*

---

### Summary and Synthesis Papers (★★★★★)

**Paper 10: The Logical Geography of Mathematical Physics**
DOI: 10.5281/zenodo.18636180

The calibration table itself. The reference document the entire program points to. Contains the methodology section (certification levels, Mathlib discussion, comparison to pen-and-paper CRM) and the comprehensive table of approximately 60 entries across 12 domains.

---

**Paper 40: [Synthesis — this paper]**
DOI: 10.5281/zenodo.18654773

The synthesis and defence of the program. Contains the eleven principal findings, the attack section addressing objections, and the articulation of why the calibration table matters.

---

**Paper 12: The Constructive History of Mathematical Physics (★★★★)**
DOI: 10.5281/zenodo.18636250

The historical narrative: how non-constructive mathematics entered physics through 19th-century choices (Weierstrass, Boltzmann, Hilbert) and what the calibration table means for the history and philosophy of physics. The paper most likely to reach non-specialists.

---

### Major Structural Contributions (★★★★)

**Paper 9: Ising Formulation-Invariance**
DOI: 10.5281/zenodo.18517570

The first and strongest test of whether the calibration tracks physics or formalism. Two independent formalisations of the Ising model — transfer-matrix and combinatorial — produce identical axiom profiles.

> *The logical cost is invariant under change of mathematical representation. The hierarchy is detecting physics, not notation.*

---

**Paper 36: Stratifying Spectral Gap Undecidability (Cubitt's Theorem)**
DOI: 10.5281/zenodo.18642620

The most celebrated undecidability result in mathematical physics reduces to LPO. This domesticates what had appeared to be an exotic phenomenon: undecidability in physics is not evidence of wild logical complexity, but the familiar cost of the thermodynamic limit. The spectral gap problem, which generated international headlines as proof that physics is "fundamentally undecidable," turns out to sit at precisely the same logical level as the Ising phase transition.

> *The most undecidable thing in physics is exactly as undecidable as a boiling pot of water.*

---

**Paper 39: Beyond LPO — Thermodynamic Stratification of Physical Undecidability**
DOI: 10.5281/zenodo.18642806

Establishes the ceiling on physical undecidability: extensive observables cap at LPO; intensive observables without promise gaps can reach LPO′ (Σ₂⁰). This is the program's most precise statement about the logical limits of physics: not only is every empirical prediction bounded by BISH + LPO, but even the undecidability phenomena are stratified and bounded. The arithmetical hierarchy, which in pure mathematics extends without limit, is effectively truncated at the second level when applied to physical systems.

> *Physics is not just computable at BISH + LPO — its undecidability is bounded too.*

---

**Paper 21: Bell Nonlocality and LLPO**
DOI: 10.5281/zenodo.18603251

Bell's theorem calibrates at LLPO.

> *Quantum nonlocality — the most philosophically provocative feature of quantum mechanics — costs exactly the lesser limited principle of omniscience, strictly below the thermodynamic limit.*

---

**Paper 24: Kochen–Specker Contextuality and LLPO**
DOI: 10.5281/zenodo.18604317

Kochen–Specker calibrates at the same level as Bell, for a structural reason — both reduce to IVT instances.

> *Bell and Kochen–Specker, treated as conceptually distinct by the foundations community, are logically identical from the CRM perspective.*

---

**Paper 27: IVT as the Mechanism Behind LLPO in Bell Physics**
DOI: 10.5281/zenodo.18615459

Identifies the intermediate value theorem as the common mechanism unifying Bell and KS at LLPO.

> *LLPO enters quantum foundations through exactly one door — the intermediate value theorem — just as LPO enters thermodynamics through Fekete.*

---

**Paper 41: The Diagnostic in Action — Axiom Calibration of the AdS/CFT Correspondence (★★★★)**
DOI: 10.5281/zenodo.18654780

The first deployment of the diagnostic on an active research frontier. Holography preserves axiom cost across the bulk–boundary correspondence and eliminates the Fan Theorem cost of bulk geometry. This paper demonstrates that the program's tools are applicable beyond textbook physics to the cutting edge of theoretical research. The finding that the holographic dictionary preserves constructive content — that every bulk computation and its boundary dual have the same axiom cost — is a new structural constraint on AdS/CFT that imposes a requirement no existing formulation violates.

> *The holographic dictionary is an axiom-preserving map. The Fan Theorem builds the bulk surface nobody observes; the boundary computes the entropy without it.*

---

**Paper 2: Bidual Gap and WLPO**
DOI: 10.5281/zenodo.17107493

The first calibration in the program. Established the methodology.

> *The existence of non-reflexive Banach spaces is equivalent to WLPO. The first entry in what became a 60-row table.*

---

**Paper 26: Bidual Gap Detection Is WLPO-Complete — Gödel Sequences**
DOI: 10.5281/zenodo.18615457

Proves WLPO-completeness via arithmetic, independent of the functional analysis route. Two independent proofs of the same calibration.

> *The result is robust — it doesn't depend on which mathematical path you take to get there.*

---

### Significant Domain Extensions (★★★)

**Paper 13: Event Horizon as Logical Boundary**
DOI: 10.5281/zenodo.18529007

Geodesic completeness costs LPO. The event horizon is where the constructive hierarchy places its boundary. This is a striking alignment between a logical concept (the boundary of constructive decidability) and a physical concept (the boundary of a black hole). It suggests that the event horizon is not merely a coordinate artifact or a property of spacetime geometry, but a manifestation of the same logical boundary that governs every thermodynamic limit.

> *The logical boundary of constructive computability and the physical boundary of a black hole coincide — both are the point where finite approximation fails to capture the infinite-volume limit.*

---

**Paper 15: Noether Theorem**
DOI: 10.5281/zenodo.18572494

Conservation laws calibrate — but with the charge/energy asymmetry that partially challenges the strong thesis.

> *The Noether calibration is where the program discovered its own limitation. Charge and energy have different logical costs due to sign-definiteness, not physics. This is the formulation-dependence counterexample.*

---

**Paper 33: QCD One-Loop Renormalization and Confinement**
DOI: 10.5281/zenodo.18642610

Lattice QCD calibrates at LPO via Fekete, confirming the pattern extends to non-abelian gauge theory. Confinement — the phenomenon that quarks cannot be isolated, which is closely related to one of the Clay Mathematics Institute's Millennium Prize Problems — is shown to have exactly the same logical structure as the Ising phase transition. This is Fekete universality at its most dramatic: the most complex gauge theory in the Standard Model reduces to the same logical mechanism as the simplest statistical mechanical model.

> *Confinement — the millennium-prize-adjacent phenomenon — is logically identical to the Ising phase transition. Same mechanism, same principle, same cost.*

---

**Paper 32: QED One-Loop Renormalization and the Landau Pole**
DOI: 10.5281/zenodo.18642598

Perturbative QED is BISH. The Landau pole is LPO.

> *The perturbative/non-perturbative boundary in QFT aligns with the BISH/LPO boundary in the constructive hierarchy.*

---

**Paper 34: Scattering Amplitudes Are Constructively Computable**
DOI: 10.5281/zenodo.18642612

Tree-level and one-loop amplitudes are BISH. This means that every number produced by the Large Hadron Collider's theoretical predictions — every cross-section, every branching ratio, every decay rate — is constructively computable without any omniscience principle. The empirical content of the Standard Model, the most precisely tested theory in the history of science, is fully constructive.

> *Everything the LHC actually measures — cross-sections, branching ratios, decay rates — is BISH-computable. The Standard Model's empirical content is constructive.*

---

**Paper 37: The Undecidability Landscape Is LPO**
DOI: 10.5281/zenodo.18642802

Surveys multiple undecidability results across physics and shows they all reduce to LPO. The significance is cumulative: any single undecidability result reducing to LPO might be coincidence, but the entire landscape reducing to the same level is a structural finding. There is no hierarchy of physical undecidability — it is flat at LPO.

> *There is no hierarchy of physical undecidability — it is flat at LPO.*

---

**Paper 19: WKB Tunneling and LLPO**
DOI: 10.5281/zenodo.18602596

Quantum tunneling turning points calibrate at LLPO via IVT.

> *The classical/quantum boundary in WKB — the turning point where classical motion stops and quantum tunneling begins — costs exactly LLPO.*

---

**Paper 23: Fan Theorem and Optimization**
DOI: 10.5281/zenodo.18604312

FT ↔ compact optimisation. Establishes what FT does so that Papers 30–31 can show it is dispensable.

> *The Fan Theorem is the logical price of asserting that continuous functions on compact sets attain their extrema. Physics computes the extremal values without paying this price.*

---

### Important Supporting Calibrations (★★)

**Paper 14: Quantum Decoherence**
DOI: 10.5281/zenodo.18569068

Decoherence costs LPO (thermodynamic limit of the environment). Decoherence is the mechanism by which quantum superpositions become effectively classical, and it is often invoked as the physical resolution of the measurement problem. Showing that its logical cost is LPO — the same as every other thermodynamic limit — integrates decoherence into the Fekete universality pattern and demonstrates that the quantum-to-classical transition is not logically special.

> *The transition from quantum to classical — decoherence — is the same thermodynamic limit as everything else.*

---

**Paper 17: Bekenstein–Hawking Formula**
DOI: 10.5281/zenodo.18597306

Black hole entropy calibrates at BISH (area formula) to LPO (thermodynamic origin).

> *The most famous formula in quantum gravity is BISH when you read the area; LPO when you derive the entropy from microstates.*

---

**Paper 20: Observable-Dependent Logical Cost — Ising Magnetization and WLPO**
DOI: 10.5281/zenodo.18603079

Different observables of the same system have different costs. This is a methodologically crucial finding: the calibration is not a property of the physical system but of the specific quantity being computed. It refines the grain of the analysis from "systems" to "observables" — the correct unit of analysis for the entire program.

> *Logical cost is observable-dependent, not system-dependent. The partition function costs LPO; the magnetisation costs WLPO; the finite-size energy costs BISH. Same Ising model, three different levels.*

---

**Paper 25: Ergodic Theorems Against Countable and Dependent Choice**
DOI: 10.5281/zenodo.18615453

Establishes DC dispensability for ergodic theory. Feeds into Paper 31.

> *The ergodic theorem — the foundation of statistical mechanics — requires DC, but the physical predictions it enables don't.*

---

**Paper 28: Classical Mechanics**
DOI: 10.5281/zenodo.18616620

Newton (ODE, BISH) vs. Lagrange (variational, FT).

> *The Newtonian and Lagrangian formulations of classical mechanics are constructively stratified — the equations are BISH, the optimisation principle is FT scaffolding.*

---

**Paper 18: Standard Model Yukawa RG**
DOI: 10.5281/zenodo.18626839

Standard Model Yukawa running is BISH.

> *The mass hierarchy of the Standard Model — why the top quark is heavy and the electron is light — is perturbatively BISH-computable.*

---

**Paper 22: Markov's Principle and Radioactive Decay**
DOI: 10.5281/zenodo.18603503

MP governs "not-not-decayed implies decayed." Independent of the main spine.

> *Markov's Principle — the assertion that a computation that cannot fail to terminate does terminate — governs radioactive decay. It is independent of both LPO and FT, confirming the hierarchy has genuine branching structure.*

---

**Paper 11: CHSH and Tsirelson Bound**
DOI: 10.5281/zenodo.18527676

Bell inequality violations and the Tsirelson bound are BISH.

> *The experimental verification of quantum nonlocality — the CHSH measurement, Tsirelson's bound — is fully constructive. The non-constructive cost (LLPO) enters only in the theorem about why local hidden variables fail, not in the computation of what experiments measure.*

---

### Confirmatory and Technical (★)

**Paper 4: Quantum Spectra Axiom Calibration**
DOI: 10.5281/zenodo.17059483

Early calibration confirming BISH for finite-dimensional quantum mechanics. Superseded by later, sharper results.

---

**Paper 5: Schwarzschild Curvature Verification**
DOI: 10.5281/zenodo.18489703

Curvature computation is BISH. Feeds into Paper 13.

---

**Paper 6: Heisenberg Uncertainty (v2)**
DOI: 10.5281/zenodo.18519836

Uncertainty principle is BISH. Clean but unsurprising — it is an algebraic inequality.

---

**Paper 7: Physical Bidual Gap — Trace-Class Operators**
DOI: 10.5281/zenodo.18527559

Physical instantiation of Paper 2's abstract result. Needed for completeness but not independently surprising.

---

**Paper 16: Technical Note — Born Rule**
DOI: 10.5281/zenodo.18575377

Born probabilities are BISH; frequentist convergence is DC. Feeds into Paper 31. Despite its modest "technical note" framing, this paper establishes a foundationally important separation: the empirical content of quantum mechanics (Born probabilities) and the interpretive superstructure (frequentist convergence, the measurement problem) live at different logical levels. This separation is the basis for Finding #11.

---

**Paper 38: Wang Tiling and the Origin of Physical Undecidability**
DOI: 10.5281/zenodo.18642804

Tiling undecidability reduces to LPO. Wang tiling is the combinatorial foundation on which many physical undecidability constructions rest (including Cubitt's spectral gap result). Showing that the tiling problem itself calibrates at LPO confirms that physical undecidability is bounded at its source, not just in its applications.

---

### Withdrawn

**Paper 1:** Withdrawn.
**Paper 3:** Withdrawn.

---

## The Arc

Build the instrument (Papers 1–39). Defend it (Paper 40). Deploy it on a duality (Paper 41). Dissolve a famous problem (Paper 42).

The calibration table in Paper 10 is the program's central artifact. This appendix is the reader's map to what the table means and how it was built.
