# The Logical Geography of Mathematical Physics: Constructive Calibration from Density Matrices to the Thermodynamic Limit

## A Companion to the Constructive Calibration Programme (Paper 10)

**Paul Chun-Kit Lee**

**Draft — February 2026**

---

## Abstract

This paper accompanies six companion papers in the author's constructive calibration programme — the Bidual Gap equivalence (Paper 2) [Lee 2026a], the Quantum Spectra axiom calibration (Paper 4) [Lee 2026f], the Heisenberg Uncertainty Principle calibration (Paper 6) [Lee 2026g], the Physical Bidual Gap for trace-class operators (Paper 7) [Lee 2026b], the Constructive Cost of the Thermodynamic Limit in the 1D Ising Model (Paper 8) [Lee 2026c], and the Formulation-Invariance of the Logical Cost (Paper 9) [Lee 2026e] — together with a supplementary note on digital physics [Lee 2026d]. It contains no new theorems. Its purpose is to synthesize the machine-verified results of those papers into a single interpretive framework and to pose a research program.

We propose that the constructive hierarchy of omniscience and choice principles — BISH, DCω, MP, WLPO, LPO, LEM — provides a precise calibration of the boundary between physically realizable content and mathematical idealization in quantum theory. The formalized results establish that preparation uncertainty (the Heisenberg inequality) is fully constructive, while measurement uncertainty requires Dependent Choice (DCω); that quantum spectral approximations are constructive but exact spectral membership requires Markov's Principle (MP); that non-reflexivity of the trace-class operators S₁(H) requires the Weak Limited Principle of Omniscience (WLPO); and that the existence of the thermodynamic limit as a completed real number is equivalent to the Limited Principle of Omniscience (LPO) via bounded monotone convergence. We observe that the logical strength required by different layers of quantum theory correlates systematically with the degree of physical idealization: finite-volume physics is fully constructive, finite-size approximations and preparation uncertainty are BISH-derivable, measurement uncertainty and spectral locale extraction require DCω, exact spectral membership requires MP (on an orthogonal axis), the ontological status of singular states requires WLPO, the thermodynamic limit requires LPO, and the spectral gap is undecidable. We argue this correlation demands explanation, and propose a working hypothesis: empirical predictions — the outputs of quantum theory for finite experimental specifications — are BISH-derivable, and stronger logical principles enter only through idealizations that no finite laboratory can instantiate. We present evidence for this hypothesis from a formulation-invariance result: the logical cost of the thermodynamic limit is identical whether derived via transfer matrices (Paper 8) or purely combinatorial methods (Paper 9), suggesting the cost is intrinsic to the physics rather than the formalism. We distinguish this position from operationalism by its formal precision, articulate the formulation-invariance test as a general methodology, and situate the proposal within the broader landscape of constructive approaches to physics, including the Döring-Isham topos program and the undecidability results of Cubitt, Perez-Garcia, and Wolf.

---

## 1. Introduction

Mathematical physics is written in the language of classical mathematics. Physicists invoke the law of excluded middle, the axiom of choice, and the full strength of Zermelo-Fraenkel set theory without hesitation, and the resulting formalism produces spectacularly accurate predictions. The question of whether this logical strength is *necessary* — whether the same physical content could be extracted from weaker principles — has been raised periodically since Brouwer, but has remained largely a philosophical curiosity. The practical success of classical mathematics leaves little incentive to investigate constructive alternatives.

This paper argues that the question deserves revival, and that recent machine-verified results in constructive reverse mathematics provide the tools to address it with unprecedented precision. The central observation is simple: when one examines the standard mathematical infrastructure of quantum statistical mechanics through a constructive lens, the logical principles required at each level of idealization fall into a structured hierarchy — predominantly a linear chain, but with orthogonal axes — that correlates with the degree of physical abstraction.

**Scope and status.** This paper contains no new proofs or formalizations. All formal results are machine-verified in the companion papers [Lee 2026a, 2026b, 2026c, 2026e, 2026f, 2026g]. Our contribution here is interpretive: we assemble the verified results into a calibration table mapping layers of quantum theory to positions in the constructive hierarchy, formulate a working hypothesis about what this mapping means, and report the outcome of a formulation-invariance test that provides evidence for the hypothesis. Papers 2, 6, 7, 8, and 9 employ constructive reverse mathematics (CRM) over Mathlib-based Lean 4 formalizations; Paper 4 employs the Axiom Calibration (AxCal) framework in mathlib-free Lean 4. The calibration results from both methodologies are compatible and jointly populate the table below. Papers 3A and 3B [Lee 2025h], which develop the AxCal framework itself, and Paper 5 (general relativity), are not directly synthesized here.

**The calibration table.** The following table summarizes the current state of the programme. Each row assigns to a layer of mathematical physics the constructive omniscience principle required for its standard formulation, together with the verification status. We maintain a distinction between two levels of evidence:

- **Calibrated**: a verified equivalence or tight bound — the physical statement is provably equivalent to (≡) or bounded by (≤) the corresponding principle over BISH, with both directions machine-checked.
- **Route-costed**: the logical cost of a *standard proof route* has been identified, but minimality has not been established — a lower-cost alternative route has not been ruled out.

All entries below are calibrated unless otherwise noted. Entries marked "≤" indicate an upper bound (the physical statement has been shown to require *at most* the stated principle, but the exact cost may be lower):

| Layer | Principle | Status | Source |
|---|---|---|---|
| Finite-volume physics | BISH | Calibrated | Trivial |
| Finite-size approximations | BISH | Calibrated | Papers 8, 9 (Part A) |
| Finite spectral approximations | BISH | Calibrated | Paper 4 (S0, S4)† |
| Preparation uncertainty (HUP) | BISH | Calibrated | Paper 6 |
| S₁(H) non-reflexivity (¬-form) | BISH | Calibrated | Paper 7 |
| Measurement uncertainty (HUP) | ≤ DCω | Calibrated | Paper 6 |
| Locale spatiality (separable) | DCω | Calibrated | Paper 4 (S2)† |
| Exact spectral membership | MP | Calibrated | Paper 4 (S1)† |
| Spectral separation (non-sep.) | WLPO | Calibrated | Paper 4 (S3, via Paper 2)† |
| Bidual-gap / singular states | ≡ WLPO | Calibrated | Papers 2, 7 |
| Thermodynamic limit existence | ≡ LPO | Calibrated | Papers 8, 9 (Part B) |
| Spectral gap decidability | Undecidable | Established | Cubitt et al. 2015 |

**Figure 1: The logical geography of mathematical physics.**

```
                    Undecidable
                  (Spectral gap)
                        |
                       LPO
               (Thermodynamic limit)
                        |
                      WLPO
            (Singular states / bidual gap)
                        |
            +-----------+-----------+
            |                       |
          DC_w                     MP
    (Measurement HUP,       (Exact spectral
     locale spatiality)      membership)
            |                       |
            +-----------+-----------+
                        |
                      BISH
          (Finite physics, prep. HUP,
         finite-size bounds, S_1 neg-form)
```

Arrows indicate strict implication over BISH. The omniscience spine (BISH < WLPO < LPO) forms the dominant vertical chain. DC_w and MP occupy orthogonal positions: neither implies the other, and neither implies WLPO. Physical layers are annotated with their calibrated logical cost.

†AxCal methodology — assembly proof verified in Lean, mathematical prerequisites axiomatized as bridge lemmas. See §2.3. Paper 6 v2 has been upgraded to CRM (Mathlib-based) and no longer carries this designation.

For the thermodynamic limit, the calibration has been verified across two independent mathematical formulations (transfer-matrix and combinatorial), establishing formulation-invariance [Lee 2026e]. The principal progression from BISH through WLPO, LPO, to undecidability is monotone in the degree of physical idealization: each step moves further from what a finite laboratory can instantiate. However, the table also reveals an orthogonal axis: Markov's Principle (MP), required for exact spectral membership (Paper 4), is independent of WLPO — neither implies the other over BISH. The logical geography of physics is thus a partial order rather than a simple linear chain, with the omniscience hierarchy (BISH < WLPO < LPO < LEM) as its dominant spine and choice/decidability principles (DCω, MP) providing lateral dimensions.

---

## 2. Background: Constructive Reverse Mathematics

### 2.1 The constructive hierarchy

Bishop-style constructive mathematics (BISH) is mathematics carried out with intuitionistic logic and dependent choice, but without the law of excluded middle (LEM), the full axiom of choice, or any continuity principles. It is a common core: every BISH theorem is valid in classical mathematics, in recursive mathematics, and in Brouwerian intuitionism. The constructive hierarchy consists of principles that extend BISH by calibrated amounts:

**WLPO** (Weak Limited Principle of Omniscience): For any binary sequence α : ℕ → {0,1}, either (∀n)(α(n) = 0) or ¬(∀n)(α(n) = 0). This is the weakest standard omniscience principle. It asserts that "all zeros" is decidable — not by producing a counterexample, but by deciding whether one exists.

**LPO** (Limited Principle of Omniscience): For any binary sequence α : ℕ → {0,1}, either (∀n)(α(n) = 0) or (∃n)(α(n) = 1). This is strictly stronger than WLPO. It asserts that a binary sequence either is identically zero or has a term equal to one — a genuine dichotomy, not merely the negation of universality.

**LEM** (Law of Excluded Middle): For any proposition P, either P or ¬P. Full classical logic.

The strict implications are: BISH < WLPO < LPO < LEM. Each inclusion is proper: there exist models of BISH + WLPO in which LPO fails, and models of BISH + LPO in which LEM fails.

These principles have a precise proof-theoretic location. In the classicality ladder — where stages iteratively add excluded middle for arithmetic formulas of increasing quantifier complexity — both WLPO and LPO sit at height 2 (requiring Σ⁰₁ excluded middle), while full LEM sits at height ω [Lee 2025h]. The omniscience hierarchy thus decomposes a specific fragment of the gap between intuitionistic and classical arithmetic.

### 2.2 The methodology: constructive reverse mathematics

Classical reverse mathematics (Friedman, Simpson) asks: which set-existence axioms are needed to prove the theorems of ordinary mathematics? The base theory is RCA₀ (recursive comprehension), and the programme classifies theorems by their equivalence to one of five standard systems.

Constructive reverse mathematics (CRM) asks the analogous question over BISH: which omniscience principles are needed? A CRM result takes the form "Theorem T is equivalent to principle P over BISH," meaning (i) BISH + P proves T, and (ii) BISH + T proves P. The equivalence is proven in a classical metatheory — this is essential and not a defect, just as Simpson's results are proven in ZFC. The meta-classical reasoning is quarantined: it establishes that the object-level equivalence holds, without contaminating the constructive content.

The programme was initiated by Ishihara [1992, 2006] and developed by Bridges and Vîță [2006], among others. Key results include the equivalence of LPO with bounded monotone convergence, of WLPO with the existence of infima of bounded sequences, and the Ishihara trichotomy relating WLPO to the sequential structure of Banach spaces.

### 2.3 Machine verification

A distinctive feature of this programme is its reliance on formal verification in Lean 4. The companion papers provide complete Lean formalizations: approximately 5,500 lines for the bidual gap equivalence (Paper 2, Zenodo deliverable), 759 lines across 8 modules for the physical bidual gap (Paper 7), 1,374 lines across 18 modules for the 1D Ising transfer-matrix formalization (Paper 8), 1,319 lines across 18 modules for the independent combinatorial formalization (Paper 9), over 700 lines for the quantum spectra calibration (Paper 4, AxCal), and approximately 420 lines across 4 modules for the Heisenberg uncertainty principle (Paper 6 v2, CRM over Mathlib). The `#print axioms` command provides a machine-checkable certificate that a given proof uses no classical axioms beyond those explicitly declared — a level of assurance unavailable to pen-and-paper proofs about constructive validity.

**Methodological distinction.** The companion papers employ two distinct formalization methodologies. Papers 2, 6, 7, 8, and 9 use *constructive reverse mathematics (CRM)* over Mathlib: theorems are proved from Mathlib's library of formalized mathematics, and `#print axioms` certificates verify that no classical axioms beyond those explicitly declared appear in the proof term. These are deep formalizations — the mathematical content is machine-checked end-to-end. Paper 6 was originally formalized in the AxCal framework (v1, ~960 lines) and subsequently upgraded to a full CRM formalization over Mathlib (v2, ~420 lines), with all mathematical prerequisites (Cauchy-Schwarz inequality, inner product space algebra, self-adjoint operator properties) derived from Mathlib rather than axiomatized. Paper 4 uses the *Axiom Calibration (AxCal)* framework in mathlib-free Lean 4: mathematical prerequisites are axiomatized as unproven bridge lemmas, and Lean verifies that the *assembly* of these prerequisites into the target theorem is logically valid and constructive. AxCal formalizations verify the logical architecture of a proof — which principles are needed at the assembly level — but delegate the verification of mathematical prerequisites to the axiom layer. The calibration claims from both methodologies populate the table below; the distinction in verification depth should be understood when interpreting the entries.

---

## 3. The Verified Results

We summarize the six companion papers that anchor the calibration table.

### 3.1 The Bidual Gap equivalence (Paper 2)

A *bidual-gap witness* for a Banach space X is a constructive datum certifying that the canonical image J(X) is proper in X**: an explicit element Ψ ∈ X** together with a positive separation from J(X) — that is, an explicit functional and threshold such that ‖Ψ − Jx‖ > δ for all x ∈ X.

**Theorem** [Lee 2026a]. Over BISH, the following are equivalent:

(i) WLPO.

(ii) There exists a Banach space X and a bidual-gap witness for X.

The proof proceeds via the Ishihara kernel technique. The forward direction (WLPO → gap) constructs a concrete non-reflexive space. The reverse direction (gap → WLPO) extracts an Ishihara kernel from the gap witness and derives WLPO using only intuitionistic logic — the classical content is quarantined in the kernel extraction. The Lean formalization verifies this separation: `WLPO_of_kernel` carries no classical axioms (the constructive consumer), while `WLPO_of_gap` — fenced in `section ClassicalMeta` — carries `Classical.choice` through the kernel construction (the classical producer) before delegating to `WLPO_of_kernel`.

This result establishes that non-reflexivity itself — the mere existence of a Banach space with a bidual gap — has the exact logical strength of WLPO.

### 3.2 The Physical Bidual Gap (Paper 7)

**Theorem** [Lee 2026b]. Let H be a separable infinite-dimensional Hilbert space.

(i) (Unconditional) S₁(H) is not reflexive: ¬(J is surjective), provable in BISH without any omniscience principle.

(ii) (Constructive witness bound) Any bidual-gap witness for S₁(H) — any constructive datum exhibiting a specific Ψ ∈ (S₁(H))** separated from J(S₁(H)) — implies WLPO.

This anchors the abstract result of Paper 2 in the canonical state space of quantum mechanics. Density matrices — the mathematical representatives of quantum states — are positive trace-class operators of unit trace. The bidual S₁(H)** contains functionals that are not represented by any density matrix. These are the *singular states*: mathematically well-defined objects in the bidual that correspond to no physical preparation procedure. In the language of operator algebras, every state ω on a von Neumann algebra admits a unique decomposition ω = ω_n + ω_s into normal and singular parts [Takesaki 1979] — the noncommutative analogue of the Lebesgue decomposition. The singular component ω_s vanishes on all compact operators, detecting only behavior at spatial infinity.

The crucial distinction is between the *¬-form* and the *witness form*. Statement (i) — that S₁(H) is not reflexive — is a negative result provable in BISH: singular states cannot be ruled out. Statement (ii) shows that *upgrading* this to a positive witness — actually exhibiting a singular state with constructive separation data — requires WLPO. This gap between "cannot be ruled out" and "can be explicitly produced" is characteristic of constructive mathematics, and it is precisely where the omniscience principle enters: not in the *existence* of singular states, but in *constructively exhibiting* one with separation data.

### 3.3 Dispensability of the thermodynamic limit (Paper 8, Part A)

**Theorem** [Lee 2026c, Part A]. For the one-dimensional Ising model with nearest-neighbour coupling J and inverse temperature β, the finite-size free energy density f_N(β) satisfies:

|f_N(β) − f_∞(β)| ≤ (1/N) · tanh(βJ)^N

This bound is provable in BISH without any omniscience principle. The proof proceeds via the transfer matrix method: the partition function Z_N = Tr(T^N) where T is the 2×2 transfer matrix, the eigenvalues λ₊ > λ₋ > 0 are constructively computable, and the error bound follows from the ratio λ₋/λ₊ = tanh(βJ) < 1. Every step — eigenvalue computation, logarithmic estimates, the geometric decay — is valid in BISH.

The significance is not that a direct computation is constructive — that would be trivially true. The significance is that the *approximation of the infinite-volume answer by finite-system data* is constructively valid, even though the infinite-volume answer itself is defined via a limit whose existence requires LPO. The empirical content of the thermodynamic limit is available without the idealization. Paper 9 [Lee 2026e] independently confirms this result via a purely combinatorial derivation using bond variables and the binomial parity sieve, with no linear algebra.

### 3.4 The LPO cost of the thermodynamic limit (Paper 8, Part B)

**Theorem** [Lee 2026c, Part B]. Over BISH, the following are equivalent:

(i) LPO.

(ii) Every bounded monotone sequence of real numbers converges (BMC).

The equivalence BMC ↔ LPO is due to Bridges and Vîță [2006]. Paper 8 instantiates this equivalence: the free energy densities f_N(β) form a bounded monotone sequence (by subadditivity of log Z), and asserting that f_∞(β) = lim f_N(β) *exists as a completed real number* imports LPO through BMC. The backward direction encodes a binary sequence α : ℕ → {0,1} into coupling constants whose free energy convergence decides α.

Together, Parts A and B establish that the thermodynamic limit costs exactly LPO, but its empirical content is free. The idealization is logically expensive; the physics it delivers is not. Paper 9 [Lee 2026e] re-derives both results from a combinatorial starting point (bond variables and the parity sieve identity), producing identical axiom profiles and confirming that the logical cost is formulation-invariant.

### 3.5 Quantum spectra calibration (Paper 4)

Paper 4 [Lee 2026f] applies the Axiom Calibration (AxCal) framework to quantum spectral theory, calibrating five spectral scenarios. Compact and finite-rank spectral approximations (S0) and the quantum harmonic oscillator spectrum (S4) are fully constructive — Height 0, no omniscience or choice principles required. The equivalence between approximate and exact spectra (S1) requires Markov's Principle (MP), encoding the unbounded search needed to decide spectral membership. Locale spatiality for separable operators (S2) requires Dependent Choice over ω (DCω). Non-separable separation routes to spectral claims (S3) trigger a "WLPO portal" — the proof constructs an element in the bidual of a function space, and by Paper 2's equivalence, this requires WLPO.

The spectral calibration introduces a significant structural observation: Markov's Principle is *orthogonal* to the omniscience hierarchy. MP is neither implied by nor implies WLPO; it lives on an independent axis. The logical geography of quantum theory is therefore not a linear chain but a partial order, with the omniscience spine (BISH < WLPO < LPO) supplemented by lateral dimensions (DCω, MP).

### 3.6 Heisenberg uncertainty principle calibration (Paper 6)

Paper 6 [Lee 2026g] calibrates the Heisenberg uncertainty principle, distinguishing preparation uncertainty from measurement uncertainty. The formalization (v2) is CRM over Mathlib: all mathematical prerequisites — the Cauchy-Schwarz inequality, inner product space algebra, self-adjoint operator properties, complex number arithmetic — are derived from Mathlib's `InnerProductSpace` and `ContinuousLinearMap.adjoint` APIs. The total formalization is approximately 420 lines across 4 modules, with zero custom axioms and zero sorry.

**Preparation uncertainty (HUP-RS).** The Robertson-Schrödinger inequality ‖⟨[A,B]⟩‖² ≤ 4·Var(A)·Var(B) is fully constructive — Height 0, provable in BISH with no choice or omniscience principles. The proof proceeds via centered vectors and the Cauchy-Schwarz inequality in Hilbert space: if z = ⟪ΔA(ψ), ΔB(ψ)⟫, then ⟨[A,B]⟩ = z − z̄, and ‖z − z̄‖² ≤ 4‖z‖² ≤ 4·Var(A)·Var(B) by Cauchy-Schwarz. The Schrödinger strengthening (the full two-term inequality with anti-commutator) uses the identity ‖z − z̄‖² + ‖z + z̄‖² = 4‖z‖² and is likewise constructive.

**Measurement uncertainty (HUP-M).** Extracting statistical information from infinite measurement sequences requires Dependent Choice (DCω). The logical cost arises not from the quantum structure itself — which is geometric and constructive — but from the classical information extraction process: constructing an infinite stream of measurement outcomes requires a choice principle to select each successive measurement result.

This separation sharpens the physical interpretation: the inherent quantum structure (Hilbert space geometry, uncertainty relations) is constructively accessible at BISH, while classical statistical analysis of measurement data incurs a modest choice cost (DCω).

---

## 4. The Correlation and Its Significance

### 4.1 The pattern

Assembling the results:

**BISH level.** Finite-volume quantum mechanics — state preparation on finite-dimensional Hilbert spaces, Born-rule probabilities, unitary time evolution for finite systems, finite-size approximations with constructive error bounds, finite spectral approximations, and preparation uncertainty (the Robertson-Schrödinger inequality) — is fully constructive. No omniscience or choice principle is needed. This is partly trivial (finite-dimensional linear algebra is constructive) and partly nontrivial (the error bounds of Paper 8 Part A and the spectral scenarios S0/S4 of Paper 4 require care to avoid implicit appeals to limits or unbounded search).

**DCω level.** Measurement uncertainty — extracting statistical conclusions from infinite sequences of quantum measurements — requires Dependent Choice over ω (Paper 6). Similarly, extracting classical point spectra from locale spectra in the separable case requires DCω (Paper 4, S2). These are the first costs incurred when moving from finite operational procedures to infinite data streams or infinite spectral decompositions.

**MP level (orthogonal axis).** Determining exact spectral membership — deciding whether a given value belongs to the spectrum rather than merely the approximate spectrum — requires Markov's Principle (Paper 4, S1). Crucially, MP is *independent* of the omniscience hierarchy: it neither implies nor is implied by WLPO. This reveals that the logical geography of physics is not a simple linear chain but a partial order. The MP axis captures a distinct aspect of idealization — the unbounded search needed to confirm spectral membership — that is logically orthogonal to the omniscience principles governing convergence and separation.

**WLPO level.** The ontological distinction between density matrices and singular states — the assertion that the quantum state space has a nontrivial bidual gap — requires WLPO (Papers 2, 7). Non-separable spectral separation routes also trigger WLPO through the "WLPO portal" of Paper 4 (S3). This is the level at which infinite-dimensional quantum theory parts ways with finite-dimensional approximation. Singular states are mathematical objects that no finite laboratory can prepare; asserting their existence as distinct from density matrices is an idealization whose logical cost is precisely WLPO. In the Haag-Kastler framework for algebraic quantum field theory [Haag 1996], singular states yield GNS representations disjoint from the identity representation, corresponding physically to inequivalent thermodynamic phases or superselection sectors [Bratteli and Robinson 1997]. The passage from the predual (normal states) to the bidual (all states, including singular) is the passage across the WLPO boundary.

**LPO level.** The thermodynamic limit — the assertion that intensive quantities converge to definite values as system size tends to infinity — requires LPO. This is the idealization that underwrites phase transitions, critical phenomena, and the emergence of thermodynamic behavior. It is strictly stronger than WLPO: you need more logical strength to assert convergence of sequences than to assert non-reflexivity of spaces.

**Undecidable level.** The spectral gap problem — whether a given Hamiltonian has a gap above its ground state energy in the thermodynamic limit — is undecidable [Cubitt, Perez-Garcia, Wolf 2015]. This is beyond LEM: no consistent formal system can decide all instances. The proof-theoretic structure underlying this level is formalized in Paper 3B [Lee 2025h]: Gödel's incompleteness theorems show that consistency strength continues to grow beyond full classical logic, with each extension of a consistent theory by its own consistency statement producing a genuinely stronger system. The Gödel sentence of a theory has height exactly 1 along the consistency ladder, and the ladder is proper at every finite stage. The spectral gap undecidability of Cubitt et al. is a physical manifestation of this phenomenon: the question lies beyond any fixed consistent extension of the base theory.

The principal progression along the omniscience spine is monotone: as the degree of physical idealization increases — from finite systems, through infinite-dimensional state spaces, through infinite-volume limits, to questions about the thermodynamic limit's spectral properties — the logical strength required increases in lockstep. The lateral dimensions (DCω, MP) enrich this picture without disrupting it: they calibrate costs associated with infinite data streams and unbounded search, respectively, that arise at intermediate levels of idealization. Beyond these, a further axis of non-constructivity — choice principles proper (Zorn's lemma, the ultrafilter lemma, the Boolean prime ideal theorem) — becomes relevant for non-separable functional analysis, where existence proofs for Banach limits on ℓ∞ or singular functionals on non-separable duals typically invoke choice beyond countable dependent choice. This choice/LEM axis is orthogonal to the omniscience axis catalogued here, and a clean separation of omniscience costs from choice costs in operator algebra theory remains an open problem.

### 4.2 Why this demands explanation

One might dismiss the correlation as tautological: of course stronger mathematics is needed for stronger claims. But the correlation is not between logical strength and *mathematical generality* — it is between logical strength and *physical idealization*. The claims at each level are about the same physical system (say, a quantum spin chain). The difference is how far the mathematical description extends beyond what a laboratory can instantiate.

Finite-volume physics is what we can actually *do*: prepare states, measure observables, record outcomes, all in finite time with finite precision. The WLPO level introduces infinite-dimensional spaces — Hilbert spaces with countably many degrees of freedom. The LPO level introduces infinite-volume limits — the fiction that the spin chain extends to infinity. The undecidable level asks questions about those infinite limits that no finite procedure can resolve.

The correlation, then, is between logical strength and *distance from operational reality*. This is a substantive observation, not a tautology. There is no a priori reason why the constructive hierarchy — which was developed for purely mathematical purposes by Ishihara, Bridges, and others — should track the layers of physical idealization in this way.

### 4.3 Comparison with van Wierst

Van Wierst [2019] was the first to examine phase transitions through a constructive lens, arguing that constructive mathematics forces "de-idealizations" of statistical-mechanical theories: no actual infinities, no discontinuous functions, and constructive real numbers that reflect the imperfect methods by which we determine physical quantities. (Regarding discontinuity: in BISH, WLPO is equivalent to the existence of a discontinuous function in a precise sense [Diener 2018]; absence of WLPO thus blocks one from *proving* such a function exists, though BISH does not positively assert Brouwerian continuity principles.) Van Wierst's argument is primarily philosophical. Our contribution is to supply the precise logical price tags: not merely "constructive mathematics forces de-idealization," but "the thermodynamic limit costs *exactly* LPO, and the singular-state distinction costs *exactly* WLPO."

### 4.4 Comparison with Batterman

Batterman [2005, 2011] has argued that infinite idealizations in physics are sometimes "explanatorily essential" — that finite-system descriptions, even when empirically adequate, fail to explain phenomena like universality and renormalization-group fixed points. Our results do not directly contradict Batterman, but they sharpen the debate. Paper 8 shows that for the 1D Ising model, finite-size bounds recover the empirical content of the thermodynamic limit constructively. The question Batterman raises — whether the *explanatory* content survives — is not resolved by our formalization, which addresses only the *predictive* content. But the separation between predictive and explanatory content is now formally precise: the predictions are BISH, the explanation (if it requires the completed infinite-volume limit) is LPO.

### 4.5 Comparison with Pour-El and Richards

Pour-El and Richards [1989] established that even computable initial data can evolve under the wave equation into non-computable solutions — physical dynamics producing non-computable outputs. Our results address a different layer: even before considering dynamics, the *spaces* in which physics lives have non-computable structure. The trace-class operators require WLPO merely to witness their non-reflexivity; no dynamics are involved. Together, Pour-El-Richards and our results suggest that computability constraints on physics are severe at multiple levels — both in the state spaces and in the evolution equations.

---

## 5. The Working Hypothesis

### 5.1 Statement

**Working Hypothesis (Logical Geography).** The correlation between constructive logical strength and degree of physical idealization is not an accident of the mathematical formalism. Empirical predictions — the outputs of quantum theory for finite experimental specifications — are BISH-derivable. Stronger logical principles (DCω, MP, WLPO, LPO, LEM) enter the mathematical description of physics only through idealizations that no finite laboratory can instantiate.

This is not operationalism. Operationalism rejects the meaningfulness of claims that transcend operational procedures. We do not reject the thermodynamic limit or singular states as meaningless. We observe that their mathematical formulation requires specific logical principles, and we hypothesize that these principles track the boundary between the physically realizable and the mathematically ideal. The hypothesis is about *logical structure*, not about ontological commitment.

### 5.2 Distinguishing features

The hypothesis makes three claims that go beyond the bare correlation:

First, *completeness*: every empirical prediction of quantum theory is BISH-derivable. This is not established by our results, which cover only the 1D Ising model and trace-class operators. It is a conjecture about quantum theory as a whole.

Second, *monotonicity*: along the omniscience spine, the logical cost increases with the degree of idealization. This is established for the layers we have calibrated, but the claim is that no counterexample exists — there is no physical prediction that requires LPO but whose underlying system is finite-dimensional, and no idealization that is weaker than singular states but whose logical cost exceeds WLPO. The monotonicity claim applies to the dominant spine (BISH < WLPO < LPO); the orthogonal axes (DCω, MP) enrich the landscape without violating it.

Third, *formulation-invariance*: the logical costs are properties of the physics, not of the mathematical formulation. This is the strongest and most testable claim. Paper 9 [Lee 2026e] provides the first positive evidence: the LPO cost of the thermodynamic limit is identical across transfer-matrix and combinatorial formulations. We discuss the scope and limitations of this evidence in §6.

### 5.3 Relation to the Church-Turing thesis

Our hypothesis stands in a natural relationship to the Church-Turing thesis as a physical principle. Deutsch [1985] proposed that the laws of physics should permit only computations consistent with the Church-Turing thesis (or its quantum generalization). This amounts to requiring that nature implement at most the computable functions.

Our hypothesis is both more and less demanding. It is more demanding in that BISH is stricter than Turing computability: there exist Turing-computable functions that are not constructively definable (because BISH requires *proofs* of totality, not mere algorithms). It is less demanding in that we do not require physical theories to be computable in the Church-Turing sense — we require only that their empirical content be expressible in BISH, which is a constraint on *logical structure* rather than *algorithmic complexity*.

The relationship to the extended Church-Turing thesis (that no physical process can compute a function not computable by a Turing machine) is also illuminating. If nature operates at BISH, then certainly the extended Church-Turing thesis holds — but the converse is false. Turing computability plus classical logic gives you more than BISH. Our hypothesis occupies a specific position between the Church-Turing thesis and full classical logic.

### 5.4 Subsumption of the digital physics critique

In a supplementary note [Lee 2026d], we derived a trilemma for digital physics programs: any program claiming the universe is fundamentally computational must either (i) accept finitism (no infinite-dimensional state spaces at all), (ii) accept hypercomputation (a computational universe that somehow transcends Turing limits), or (iii) reconstruct physics constructively to avoid bidual-gap arguments. That trilemma is a corollary of the present hypothesis.

If the hypothesis is correct, horn (iii) is the natural resolution: the physics *is* reconstructible at the constructive level, because the empirical content never needed the non-constructive superstructure. The bidual gap is real as mathematics (Papers 2 and 7 verify this), but its physical significance is precisely that it marks the boundary beyond which the formalism outruns the physics. A digital physics program that operates at the BISH level — computing finite-volume predictions with constructive error bounds — captures everything a laboratory can verify. The infinite-dimensional overhead is the mathematician's convenience, not nature's structure.

### 5.5 Relation to Gisin's intuitionistic physics

Gisin [2020, 2021] has argued philosophically for "intuitionistic physics" — a reformulation of physics avoiding infinite precision and non-constructive existence claims. Gisin's argument is primarily conceptual, motivated by the observation that real numbers with infinite decimal expansions encode more information than any physical measurement can access. He does not provide the technical price tag for his proposal.

Our results supply that price tag. If physics is to be intuitionistic (in the sense of avoiding WLPO), it must abandon or reconstruct: the density-matrix formalism for mixed states (since the normal/singular distinction requires WLPO), the thermodynamic limit for phase transitions (which requires the stronger LPO), and more broadly, any argument that distinguishes reflexive from non-reflexive spaces. Whether this reconstruction is possible while preserving empirical content is the open problem we have identified — and Paper 8, Part A provides the first affirmative instance, showing that at least in the exactly solvable 1D Ising case, the reconstruction succeeds.

---

## 6. The Formulation-Invariance Test

The hypothesis predicts that the logical costs are properties of the physics, not of the mathematical formulation. Paper 9 [Lee 2026e] provides the first test of this prediction.

### 6.1 The test and its outcome

**Test.** If the logical cost of the thermodynamic limit is intrinsic to the physics, then mathematically independent derivations of the same physical quantity should yield identical axiom profiles. If the cost is an artifact of the formalism, different formulations should yield different profiles.

**Outcome.** Paper 9 re-derives both results of Paper 8 — the BISH dispensability of finite-size bounds (Part A) and the LPO equivalence of the thermodynamic limit (Part B) — using purely combinatorial methods. The partition function identity Z_N(β) = (2cosh β)^N + (2sinh β)^N is established via bond variables and the binomial parity sieve, replacing the transfer-matrix spectral decomposition Z_N = Tr(T^N) = λ₊^N + λ₋^N entirely. No matrices, eigenvalues, linear algebra, or functional analysis appear at any point.

The formulation-invariance claim is verified at two levels. First, the *axiom audit*: the `#print axioms` output for both formulations is identical — `[propext, Classical.choice, Quot.sound]` for Part A, with the addition of `bmc_of_lpo` for the Part B equivalence. (The combinatorial formalization also axiomatizes a parity sieve identity — an elementary combinatorial fact requiring nontrivial Lean infrastructure to formalize; this axiom is architecturally isolated from the main theorem dependency chains and does not appear in the `#print axioms` output for either the dispensability or equivalence theorems.) Second, the *import audit*: the combinatorial formalization imports no Mathlib module from `LinearAlgebra.*` or `Analysis.NormedSpace.*`, ensuring strict separation from the transfer-matrix approach. The two formalizations share only the unavoidable common substrate — real arithmetic and the logical principles under test.

The result: two mathematically independent routes to the same physical quantity produce the same logical cost. The LPO-strength of the thermodynamic limit is not an artifact of the transfer-matrix formalism.

### 6.2 Scope and limitations

The formulation-invariance result is evidence, not proof. Two formulations are better than one, but a definitive result would be an *ineliminability* theorem: that *any* constructive proof of free energy convergence for the 1D Ising model must use BMC. This remains an open problem (Problem 1 below).

The test has been carried out only at the LPO level and only for the 1D Ising model. Whether the WLPO cost of the bidual gap (Papers 2, 7) is similarly formulation-invariant — whether the same logical cost arises in the C*-algebraic formulation as in the Banach-space formulation — is an open question (Problem 5 below).

### 6.3 The encoding objection

A natural objection to the calibration results is that they depend on encoding: the equivalence between LPO and free energy convergence (Paper 8, Part B) works by encoding a binary sequence into coupling constants, and the resulting Hamiltonian may be "artificial." If the logical cost is an artifact of the encoding rather than a property of the physics, the calibration is meaningless.

We address this directly. The encoding objection conflates two questions: (i) Is the Hamiltonian physically natural? (ii) Is the logical equivalence informative? For (i), the encoded Hamiltonian is a legitimate nearest-neighbour 1D Ising model with site-dependent couplings — unusual in the physics literature, but not artificial in any mathematical sense. For (ii), the equivalence is informative precisely because it shows that BMC (bounded monotone convergence) is the *exact* logical content of thermodynamic-limit existence for this class of models. The encoding is the proof technique; the calibration is the result.

Moreover, Paper 9 strengthens the response to this objection: the same encoding strategy works in the combinatorial formulation, producing identical axiom profiles. The encoding is not tied to the transfer-matrix framework.

### 6.4 The topos-theoretic alternative

A significant challenge to our hypothesis comes from the Döring-Isham topos program [Isham 1997, Döring and Isham 2008, Heunen, Landsman, and Spitters 2009]. This program reformulates quantum mechanics within a topos — a generalized universe of sets with an intuitionistic internal logic. In the topos associated with a von Neumann algebra, the Kochen-Specker theorem is reinterpreted as the non-existence of global sections of a certain presheaf, and quantum states become probability valuations on the spectral presheaf.

The internal logic of these topoi is intuitionistic, hence compatible with constructive mathematics. If the entire empirical content of quantum theory can be recovered within the Döring-Isham framework, this would support our hypothesis: the physics would be expressible in an intuitionistic (hence constructive-compatible) framework, with classical logic entering only through the traditional formulation.

Conversely, if the Döring-Isham framework provably *cannot* recover certain empirical predictions without additional classical axioms, this would challenge the hypothesis. The precise relationship between the Döring-Isham internal logic and the BISH/WLPO/LPO hierarchy has not been worked out. We flag this as a high-priority question for the programme.

### 6.5 What a counterexample would look like

A decisive refutation of the working hypothesis would take the following form: a *finite-system* measurement prediction — an expectation value, a correlation function, a transition probability for a system specified by a finite-dimensional Hilbert space, rational Hamiltonian coefficients, and rational error tolerance — whose derivation from first principles essentially requires WLPO (or a stronger principle), with no constructive alternative derivation yielding the same numerical value within the specified tolerance.

We know of no such counterexample. This is weak evidence in favor of the hypothesis, but it is the correct kind of evidence: the hypothesis survives not because it is unfalsifiable, but because no one has found the relevant counterexample. The search for such a counterexample — or for a proof that none exists — is the most immediate concrete research question our proposal generates.

---

## 7. Historical Precedents

The proposal that a mathematical structure might track physical reality rather than merely representing it has significant precedents.

### 7.1 Computation as physics

Before Landauer [1961] and Bennett [1973], computation was a purely mathematical notion. The insight that computation is a physical process — requiring energy, dissipating heat, occupying time — transformed information theory and eventually led to quantum computing. Deutsch [1985] sharpened this by proposing that the set of physically computable functions is determined by physics, not mathematics: quantum physics computes different functions than classical physics.

Our proposal extends this one level up. Deutsch asked: what if *computability* is physical? We ask: what if *logical strength* is physical? The constructive hierarchy (BISH, WLPO, LPO, LEM) is to our proposal what the computability hierarchy (finite automata, pushdown automata, Turing machines) was to Deutsch's.

### 7.2 Simultaneity and the operational content of mathematics

Einstein's 1905 analysis of simultaneity is perhaps the deepest precedent. Einstein asked: what physical content does the claim "two events are simultaneous" actually carry? The answer — that simultaneity requires a synchronization procedure, and different procedures yield different answers for different observers — was a foundational insight that revolutionized physics.

We ask an analogous question: what physical content does the claim "this state is singular" (or "this Banach space is non-reflexive" or "this spectral gap is zero") actually carry? Our formalized results provide a precise answer: these claims carry the logical content of specific omniscience principles. Whether this logical content has physical substance — whether the universe "decides" these questions or whether they are artifacts of the formalism — is the question our hypothesis addresses.

### 7.3 Constructive mathematics as physics

There is a long tradition of developing constructive mathematics as the natural language for analysis and computation. Bishop [1967] framed constructive analysis with an algorithmic interpretation. Bridges and Richman [1987] systematized the varieties of constructive mathematics. Beeson [1985] developed the metamathematical foundations. Ishihara [2006] initiated the specific program of constructive reverse mathematics. Diener [2018] compiled the most comprehensive survey. Brattka and Gherardi [2009] connected omniscience principles to the Weihrauch lattice, providing a computational counterpart to the logical classification. The mathematical infrastructure for our proposal has been built by these researchers over decades; our contribution is to connect this infrastructure to the physical hierarchy of idealizations. Paper 3B [Lee 2025h] extends this infrastructure into classical proof theory, formalizing the ladders of consistency and reflection strength and establishing precise calibrations of Gödel's incompleteness theorems within the AxCal framework.

---

## 8. Open Problems

We close by listing specific open problems that would advance the programme.

**Problem 1.** *Ineliminability.* Papers 8 and 9 establish the LPO cost of the thermodynamic limit via two independent formulations. Is this cost *ineliminable* — must *any* constructive proof of free energy convergence for the 1D Ising model use BMC? A positive answer would upgrade the formulation-invariance evidence of Paper 9 to a genuine theorem. For the 2D Ising model, where the Peierls argument establishes phase coexistence, the question is sharper: if finite-size bounds for the 2D magnetization can be established constructively, the dispensability extends; if not, there is a genuine LPO obstruction at the empirical level, and the hypothesis is under pressure.

**Problem 2.** *Phase transitions without limits.* Can phase transitions be characterized constructively — without asserting the existence of the thermodynamic limit — in a way that preserves the standard phenomenology (critical exponents, universality classes, scaling relations)? Van Wierst [2019] argues that constructive analysis forces "de-idealizations" but does not provide a positive reconstruction.

**Problem 3.** *Intermediate and orthogonal principles.* The calibration table now includes DCω (measurement uncertainty, locale spatiality) and MP (exact spectral membership) alongside the omniscience spine (WLPO, LPO). Several questions arise: (a) Does any physical idealization have LLPO (the Lesser Limited Principle of Omniscience, intermediate between WLPO and LPO) as its exact logical cost? (b) Can the DCω costs of Paper 4 (S2) and Paper 6 (HUP-M) be sharpened to exact equivalences rather than upper bounds? (c) Is the MP cost of exact spectral membership (Paper 4, S1) formulation-invariant — does the same cost arise in the C*-algebraic spectral theory as in the Hilbert-space formulation?

**Problem 4.** *Döring-Isham calibration.* What is the constructive strength of the Döring-Isham topos framework? Specifically, does the internal logic of the Bohrification topos associated with B(H) coincide with BISH, or does it validate additional principles (WLPO, LPO, or fragments thereof)?

**Problem 5.** *Formulation-invariance for the WLPO level.* The WLPO equivalence (Papers 2, 7) is stated in the Banach-space formulation of quantum mechanics. Does the same logical cost appear in the C*-algebraic formulation? Specifically, does the GNS construction applied to a state on B(H) — recovering the density matrix from the algebraic state — require WLPO?

**Problem 6.** *Beyond statistical mechanics.* Does the calibration pattern extend to quantum field theory? The renormalization group involves infinite-volume limits (LPO-strength), but also ultraviolet limits (requiring different mathematical infrastructure). What are the logical costs of renormalization?

---

## 9. Conclusion

The constructive hierarchy of omniscience and choice principles — a technical apparatus developed for the internal purposes of constructive analysis — turns out to map onto the layers of physical idealization in quantum theory with surprising fidelity. Finite physics and preparation uncertainty are BISH. Measurement uncertainty and spectral locale extraction cost DCω. Exact spectral membership costs MP (on an orthogonal axis). The singular sector costs WLPO. The thermodynamic limit costs LPO. The spectral gap is undecidable. Each step away from what a finite laboratory can instantiate requires a precisely calibrated increment of logical strength — and the landscape admits not just a linear chain but a partial order, with the omniscience spine supplemented by choice and decidability dimensions.

This could be a coincidence. But the correlation is not between logical strength and mathematical complexity — it is between logical strength and *physical accessibility*. The simplest explanation is that nature operates at the constructive level, and the non-constructive superstructure of classical mathematical physics, while enormously convenient, tracks the mathematician's idealizations rather than the world's structure.

We have formulated this as a working hypothesis, carried out a first formulation-invariance test (Paper 9), and identified the open problems that would confirm or refute the hypothesis at greater generality. The programme now encompasses six companion papers covering the bidual gap (Paper 2), quantum spectra (Paper 4), uncertainty relations (Paper 6), trace-class operators (Paper 7), and the thermodynamic limit via two independent formulations (Papers 8, 9). The precision of the calibration, verified in thousands of lines of Lean 4 — predominantly CRM over Mathlib, with Paper 4 using the AxCal methodology — is unprecedented in the philosophy of mathematical physics. Whether the pattern holds as the programme extends to higher dimensions, quantum field theory, and alternative formulations is the question we leave to future work.

---

## References

- Batterman, R. W. "Critical phenomena and breaking drops: Infinite idealizations in physics." *Studies in History and Philosophy of Modern Physics* 36 (2005): 225–244.
- Batterman, R. W. "Emergence, singularities, and symmetry breaking." *Foundations of Physics* 41 (2011): 1031–1050.
- Beeson, M. J. *Foundations of Constructive Mathematics*. Springer, Berlin, 1985.
- Bennett, C. H. "Logical reversibility of computation." *IBM Journal of Research and Development* 17(6) (1973): 525–532.
- Bishop, E. *Foundations of Constructive Analysis*. McGraw-Hill, New York, 1967.
- Bishop, E. and Bridges, D. *Constructive Analysis*. Springer, Berlin, 1985.
- Brattka, V. and Gherardi, G. "Weihrauch degrees, omniscience principles and weak computability." In *6th International Conference on Computability and Complexity in Analysis (CCA'09)*, OASIcs vol. 11, pp. 83–94. Schloss Dagstuhl, 2009.
- Bratteli, O. and Robinson, D. W. *Operator Algebras and Quantum Statistical Mechanics*, Vol. I. 2nd ed. Springer, Berlin, 1987.
- Bratteli, O. and Robinson, D. W. *Operator Algebras and Quantum Statistical Mechanics*, Vol. II. 2nd ed. Springer, Berlin, 1997.
- Bridges, D. and Richman, F. *Varieties of Constructive Mathematics*. Cambridge University Press, 1987.
- Bridges, D. and Vîță, L. S. *Techniques of Constructive Analysis*. Springer, New York, 2006.
- Cubitt, T. S., Perez-Garcia, D., and Wolf, M. M. "Undecidability of the spectral gap." *Nature* 528 (2015): 207–211.
- Deutsch, D. "Quantum theory, the Church-Turing principle and the universal quantum computer." *Proceedings of the Royal Society of London A* 400 (1985): 97–117.
- Diener, H. "Constructive reverse mathematics." Habilitation thesis, Universität Siegen, 2018.
- Döring, A. and Isham, C. J. "'What is a thing?': Topos theory in the foundations of physics." In *New Structures for Physics*, Lecture Notes in Physics 813, Springer, 2008.
- Gisin, N. "Mathematical languages shape our understanding of time in physics." *Nature Physics* 16 (2020): 114–116.
- Gisin, N. "Indeterminism in physics, classical chaos and Bohmian mechanics: Are real numbers really real?" *Erkenntnis* 86 (2021): 1469–1481.
- Haag, R. *Local Quantum Physics: Fields, Particles, Algebras*. 2nd ed. Springer, Berlin, 1996.
- Heunen, C., Landsman, N. P., and Spitters, B. "A topos for algebraic quantum theory." *Communications in Mathematical Physics* 291 (2009): 63–110.
- Isham, C. J. "Topos theory and consistent histories: The internal logic of the set of all consistent sets." *International Journal of Theoretical Physics* 36 (1997): 785–814.
- Ishihara, H. "Continuity properties in constructive mathematics." *Journal of Symbolic Logic* 57 (1992): 557–565.
- Ishihara, H. "Reverse mathematics in Bishop's constructive mathematics." *Philosophia Scientiae*, Cahier spécial 6 (2006): 43–59.
- Kadison, R. V. and Ringrose, J. R. *Fundamentals of the Theory of Operator Algebras*, Vol. I. Academic Press, New York, 1983.
- Landauer, R. "Irreversibility and heat generation in the computing process." *IBM Journal of Research and Development* 5(3) (1961): 183–191.
- Landsman, N. P. *Foundations of Quantum Theory: From Classical Concepts to Operator Algebras*. Springer, 2017.
- Lee, P. C.-K. "Constructive reverse mathematics of the bidual gap: WLPO equivalence for Banach space non-reflexivity." 2026a. Lean 4 formalization archived at Zenodo. DOI: 10.5281/zenodo.17107493.
- Lee, P. C.-K. "The physical bidual gap: WLPO and non-reflexivity of trace-class operators." 2026b. Lean 4 formalization archived at Zenodo. DOI: 10.5281/zenodo.18509795.
- Lee, P. C.-K. "The constructive cost of the thermodynamic limit: LPO equivalence and BISH dispensability in the 1D Ising model." 2026c. Lean 4 formalization archived at Zenodo. DOI: 10.5281/zenodo.18516813.
- Lee, P. C.-K. "Digital physics and the bidual gap: Why computational universes cannot verify Banach space non-reflexivity." Supplementary note, 2026d. Available at ResearchGate.
- Lee, P. C.-K. "Formulation-invariance of the logical cost of the thermodynamic limit: A combinatorial proof for the 1D Ising model." 2026e. Lean 4 formalization archived at Zenodo. DOI: 10.5281/zenodo.18517570.
- Lee, P. C.-K. "Axiom calibration for quantum spectra: Orthogonal heights, choice principles, and separation portals." 2026f. Lean 4 formalization archived at Zenodo. DOI: 10.5281/zenodo.17059483.
- Lee, P. C.-K. "Constructive reverse mathematics for the Heisenberg uncertainty principle: Robertson--Schr\"odinger and Schr\"odinger inequalities over Mathlib." 2026g. Lean 4 formalization archived at Zenodo. DOI: 10.5281/zenodo.18519836. (Paper 6, v2; supersedes v1 at DOI: 10.5281/zenodo.17068179.)
- Lee, P. C.-K. "Axiom calibration of meta-mathematical hierarchies: Formal collisions and the structure of consistency and reflection." 2025h. Lean 4 formalization archived at Zenodo. DOI: 10.5281/zenodo.17054155.
- Pour-El, M. B. and Richards, J. I. *Computability in Analysis and Physics*. Springer, Berlin, 1989.
- Simpson, S. G. *Subsystems of Second Order Arithmetic*. 2nd ed. Cambridge University Press, 2009.
- Takesaki, M. *Theory of Operator Algebras I*. Springer, New York, 1979.
- van Wierst, P. "The paradox of phase transitions in the light of constructive mathematics." *Synthese* 196 (2019): 1863–1893.

---

*Acknowledgments.* The Lean 4 formalizations and LaTeX manuscripts in this programme were developed with substantial assistance from Claude (Opus 4.6), an AI assistant by Anthropic. The author is not a domain expert in constructive mathematics or mathematical physics; the formalization methodology --- iterative proof construction guided by Lean's type-checker and Mathlib's API --- made this programme tractable for a non-specialist. The author gratefully acknowledges the AI assistance, which was indispensable at every stage: proof strategy, Mathlib API navigation, error diagnosis, and manuscript preparation.

*Data availability.* All Lean 4 source code is archived at Zenodo. Paper 2: DOI: 10.5281/zenodo.17107493. Paper 3B: DOI: 10.5281/zenodo.17054155. Paper 4: DOI: 10.5281/zenodo.17059483. Paper 6: DOI: 10.5281/zenodo.18519836. Paper 7: DOI: 10.5281/zenodo.18509795. Paper 8: DOI: 10.5281/zenodo.18516813. Paper 9: DOI: 10.5281/zenodo.18517570.
