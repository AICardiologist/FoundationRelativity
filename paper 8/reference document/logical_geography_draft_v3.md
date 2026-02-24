# The Logical Geography of Mathematical Physics: Constructive Calibration from Density Matrices to the Thermodynamic Limit

### A Companion to the Bidual Gap Series

**Paul Chun-Kit Lee**
New York University
dr.paul.c.lee@gmail.com

**Draft — February 2026**

---

## Abstract

We synthesize a series of Lean 4 formalizations connecting core results in functional analysis to constructive omniscience principles, and interpret their significance for quantum theory. The verified results show that exhibiting a bidual-gap witness (a constructive witness of non-reflexivity) is equivalent over Bishop-style constructive mathematics (BISH) to WLPO, and that any bidual-gap witness for the trace-class operators S₁(H) — the standard state space of quantum mechanics — entails WLPO. Interpreting S₁(H)** as the space of bounded linear functionals on B(H), this identifies a precise logical threshold between normal states (density matrices) and constructively witnessing singular states.

Building on these equivalences and on prior work by van Wierst [2019] on constructive phase transitions, the Döring-Isham topos program [2008], and Cubitt, Perez-Garcia, and Wolf [2015] on spectral-gap undecidability, we assemble a calibration landscape mapping layers of quantum statistical mechanics to positions in the constructive hierarchy (BISH, WLPO, LPO, LEM, undecidable). The verified entries are marked as *calibrated*; the remaining entries, which track the logical cost of standard proof routes, are marked as *route-costed*. We observe a monotone correlation between logical strength and degree of physical idealization, and propose a working hypothesis: empirical predictions are BISH-derivable, and stronger principles enter only through idealizations. We formulate a metatheoretic test (formulation-invariance of logical costs) that would distinguish this hypothesis from the null hypothesis that the costs are artifacts of the Banach-space formalism, and situate the proposal within the broader landscape of constructive approaches to physics.

---

## 1. Introduction and Scope

**Scope.** This paper contains no new proofs or formalizations. All formal results cited here are machine-verified in the companion papers [Lee 2026a, 2026b, 2026c] and are publicly available with persistent DOIs. A supplementary note [Lee 2026d] explored the implications for digital physics programs; the present paper subsumes that note as a special case (§5.4) of a more general thesis.

Mathematical physics is written in the language of classical mathematics. Physicists invoke the law of excluded middle, the axiom of choice, and the full strength of Zermelo-Fraenkel set theory without hesitation, and the resulting formalism produces spectacularly accurate predictions. The question of whether this logical strength is *necessary* — whether the same physical content could be extracted from weaker principles — has been raised periodically since Brouwer, but has remained largely a philosophical curiosity. The practical success of classical mathematics leaves little incentive to investigate constructive alternatives.

Several independent lines of research have made progress on aspects of this question. In constructive reverse mathematics, Ishihara [2006] initiated a systematic program of calibrating non-constructive theorems against omniscience principles, and Diener [2018] compiled a comprehensive survey of known equivalences across analysis and topology. In the philosophy of physics, van Wierst [2019] argued that adopting constructive mathematics dissolves the "paradox of phase transitions" — the tension between the mathematical requirement of infinite systems for sharp phase transitions and the physical reality of phase transitions in finite systems — by forcing de-idealizations that make the paradox disappear. In mathematical physics, Döring and Isham [2008] and Heunen, Landsman, and Spitters [2009] reformulated quantum mechanics within topoi whose internal logic is intuitionistic, showing that the full empirical content of quantum theory may be recoverable without classical logic. And Cubitt, Perez-Garcia, and Wolf [2015] demonstrated that the spectral gap problem is undecidable, establishing that certain questions in mathematical physics lie beyond the reach of any logical principle.

What has been missing is a connection between these programs: a unified landscape that maps specific physical constructions in quantum statistical mechanics to specific positions in the constructive hierarchy, grounded in machine-verified results for the physically canonical spaces. Recent developments in formal verification make this possible. In a series of papers [Lee 2026a, 2026b], we have established such equivalences:

- The existence of a non-reflexive Banach space is equivalent to WLPO (the Weak Limited Principle of Omniscience) over Bishop-style constructive mathematics (BISH) [Lee 2026a].
- The trace-class operators S₁(H) — the canonical quantum state space — are not reflexive, and any constructive witness of this non-reflexivity implies WLPO [Lee 2026b].

The first result extends the abstract calibration program of Ishihara and Diener to Banach space theory. The second anchors this calibration in the specific mathematical structure that quantum mechanics actually uses — a step that had not been taken in the existing literature, where constructive reverse mathematics and mathematical physics have developed largely in parallel. The formalizations are machine-checked in Lean 4 and publicly available.

The present paper steps back from the formalization machinery to synthesize these results — ours and those of the researchers cited above — into a single interpretive framework. We assemble a calibration landscape mapping the layers of quantum statistical mechanics (finite-volume physics, singular states, thermodynamic limits, non-separable duals, spectral gap) to the constructive hierarchy (BISH, WLPO, LPO, LEM, undecidable). The first two rows of this landscape are our formalized results; the remaining rows draw on the work of Bridges and Vîță [2006], van Wierst [2019], and Cubitt, Perez-Garcia, and Wolf [2015]. We observe that the resulting landscape is monotone: logical cost increases with degree of physical idealization.

We propose a hypothesis to explain this monotonicity: nature operates at the constructive level, and stronger logical principles enter only through idealizations that no finite laboratory can instantiate. This hypothesis is consonant with van Wierst's philosophical conclusions and with the Döring-Isham program's use of intuitionistic internal logic, but it goes beyond both by proposing a concrete test — formulation-invariance of logical costs — that would distinguish the hypothesis from the null hypothesis that the costs are artifacts of the Banach-space formalism. We articulate this test precisely, identify its consequences, and situate the proposal within the broader landscape of constructive approaches to physics.

## 2. The Constructive Hierarchy

We work within Bishop-style constructive mathematics (BISH) in the sense standard in constructive reverse mathematics: intuitionistic logic together with countable choice, dependent choice, and unique choice, but without LEM and without full choice principles (Zorn's lemma, the ultrafilter lemma, the axiom of choice for arbitrary families) that underwrite many classical existence proofs [Bishop 1967, Bridges and Vîță 2006, Ishihara 2006]. BISH is compatible with classical mathematics (every BISH theorem is classically valid) but is strictly weaker: many classical theorems are not provable in BISH and require supplementation by specific logical principles.

The omniscience principles form a well-studied hierarchy, systematically investigated by Ishihara [2006] and comprehensively surveyed by Diener [2018]. WLPO (the Weak Limited Principle of Omniscience) states that for every binary sequence α : ℕ → {0,1}, either all terms are zero or it is not the case that all terms are zero:

> WLPO: ∀α : ℕ → {0,1}, (∀n, α(n) = 0) ∨ ¬(∀n, α(n) = 0).

LPO (the Limited Principle of Omniscience) strengthens this to an existential witness:

> LPO: ∀α : ℕ → {0,1}, (∀n, α(n) = 0) ∨ (∃n, α(n) = 1).

The hierarchy is strict: LPO implies WLPO, WLPO implies LLPO (the Lesser Limited Principle of Omniscience), and none of the reverse implications hold over BISH. Markov's Principle (MP) is independent of WLPO. At the top, the Law of Excluded Middle (LEM) implies all of these, and is equivalent to full classical logic.

The crucial observation for physics is that these principles have concrete analytic content. In BISH, LPO calibrates one-sided order decidability and is equivalent to bounded monotone convergence for real sequences [Bridges and Vîță 2006, Ishihara 2006]. WLPO calibrates a weaker stability principle: it is equivalent to the decidability of the zero-test ∀x ∈ ℝ, (x = 0) ∨ ¬(x = 0), and to the existence of a discontinuous function in a precise constructive sense [Diener 2018]. Note that "x ≠ 0" here is the negation of equality (¬(x = 0)), not a positive apartness witness (∃q ∈ ℚ, |x| > q > 0); WLPO gives the weak disjunction in this negated sense, whereas obtaining a positive witness typically tracks stronger principles. These are not abstract logical curiosities — they are the precise operations that mathematicians and physicists perform routinely under the implicit assumption of classical logic, and whose constructive status directly governs what can and cannot be computed.

## 3. The Formalized Results

Before presenting the results, we introduce a distinction that will be maintained throughout the paper.

**Definition (calibrated vs. route-costed).** We say a logical cost is *calibrated* when we have a verified equivalence: the physical statement is provably equivalent to the omniscience principle over BISH. We say a logical cost is *route-costed* when we can identify the logical cost of a standard proof route (e.g., "the usual construction uses monotone convergence, hence imports at least LPO"), without having shown that no lower-cost route exists.

The WLPO results in §§3.1–3.2 are calibrated. The LPO and LEM entries in §§4.3–4.4 are route-costed. We are explicit about this distinction throughout.

**Definition (bidual-gap witness).** A *bidual-gap witness* for a Banach space X is a constructive datum certifying that the canonical image J(X) is proper in X**: an explicit element Ψ ∈ X** together with a positive separation from J(X) (e.g., an explicit functional and threshold such that |Ψ(f) − Jx(f)| > δ for all x ∈ X).

### 3.1 The Bidual Gap Equivalence

In [Lee 2026a], we proved the following equivalence in Lean 4:

**Theorem (Bidual Gap Equivalence).** Over BISH, the following are equivalent:
1. WLPO.
2. There exists a real Banach space X and a bidual-gap witness for X.

The backward direction (bidual-gap witness implies WLPO) proceeds via the Ishihara kernel construction: given Ψ outside the canonical image, one extracts a finite tuple of functionals and a positive threshold that, together, constructively produce a WLPO decision. The forward direction constructs an explicit witness G ∈ (c₀)** using WLPO. Both directions are machine-checked, and the formalization is publicly available [Lee 2026a, GitHub repository].

### 3.2 The Physical Bidual Gap

In [Lee 2026b], we extended this result to the physically canonical space:

**Theorem (Physical Bidual Gap).** Let H be a separable Hilbert space.
1. (Unconditional) S₁(H) is not reflexive: ¬(J is surjective), provable in BISH without any omniscience principle.
2. (Constructive witness bound) Any bidual-gap witness for S₁(H) — any constructive datum exhibiting a specific Ψ ∈ (S₁(H))** separated from J(S₁(H)) — implies WLPO.

The crucial distinction: statement (1) is a *negative* result (¬-form), provable constructively. Statement (2) shows that upgrading this to a *positive witness* — actually exhibiting a singular state with constructive separation data — requires WLPO. This gap between the negative and positive forms is characteristic of constructive mathematics and is precisely where the omniscience principle enters.

The proof of (1) proceeds by embedding ℓ¹ isometrically into S₁(H) via the diagonal embedding and showing that if S₁(H) were reflexive, ℓ¹ would be reflexive — a contradiction. The key lemma (every closed subspace of a reflexive Banach space is reflexive, proved via two applications of the Hahn-Banach theorem without James's theorem) was independently formalized in Lean 4 and is not currently present in the Mathlib4 library.

The physical content: S₁(H) is the predual of B(H), the algebra of bounded operators on H. In von Neumann's formulation of quantum mechanics, the normal states — the physically preparable density matrices — are the elements of S₁(H). The bidual (S₁(H))** contains additional elements: singular states, positive linear functionals on B(H) that are not σ-weakly continuous and cannot be represented by any density matrix. The ¬-form of non-reflexivity tells us these singular states cannot be ruled out; statement (2) says that constructively exhibiting any specific one (with separation data) requires WLPO.

## 4. The Calibration Landscape

We now catalogue the logical costs of quantum statistical mechanics. The entries range from fully constructive to undecidable, and the ordering correlates with the degree of physical idealization.

### 4.1 Finite-volume physics: BISH

The properties of a quantum system confined to a finite volume Λ ⊂ ℤ^d — the Gibbs state at inverse temperature β, the finite-volume partition function Z_Λ(β), explicit magnetization estimates, Peierls-type bounds — are fully constructive. The Hilbert space H_Λ is finite-dimensional, the trace is a finite sum, and the density matrix ρ_Λ = e^{-βH_Λ} / Z_Λ is constructively computable. No omniscience principle is required.

This is the physics of actual laboratories. Every experiment is performed on a finite system, in finite time, with finite precision. The mathematical description of these experiments lives entirely within BISH.

### 4.2 The singular sector: WLPO (calibrated)

The bidual gap in S₁(H) — the set of singular states on B(H) that are not representable by density matrices — is non-empty in the ¬-form (provable in BISH), but constructively exhibiting any specific singular state with separation data (a bidual-gap witness) requires WLPO. This is the content of our Physical Bidual Gap theorem. This cost is *calibrated*: the equivalence with WLPO is machine-verified.

Physically, singular states are the mathematical objects that populate the boundary between finite-volume quantum mechanics and the infinite-volume theory. Every state ω on a von Neumann algebra admits a unique decomposition ω = ω_n + ω_s into normal and singular parts [Takesaki 1979] — the noncommutative analogue of the Lebesgue decomposition. The singular component ω_s vanishes on all compact operators: it detects only the behavior of observables at spatial infinity. That ω_s ≠ 0 for some states is constructively guaranteed (the ¬-form of non-reflexivity tells us J is not surjective); but constructively *exhibiting* a state with ω_s ≠ 0 and providing explicit separation data is what requires WLPO. This distinction between "cannot be ruled out" (¬-form) and "can be explicitly produced" (witness form) is fundamental to the constructive picture.

### 4.3 The thermodynamic limit: LPO (route-costed)

The passage from finite-volume Gibbs states to infinite-volume equilibrium states — the thermodynamic limit — requires stronger logical resources. The existence of thermodynamic limits is often proved using compactness/subadditivity arguments (Fekete-type lemmas) or weak-* compactness (Banach-Alaoglu), whose constructive strength is nontrivial to locate. However, one ubiquitous route — bounded monotone convergence — has logical strength exactly LPO over BISH [Bridges and Vîță 2006]. The standard construction of free energy densities proceeds by this route: the sequence f_Λ(β) = -|Λ|⁻¹ log Z_Λ(β) converges monotonically, and the limit defines the infinite-volume free energy f(β).

We therefore assign this entry the label *route-costed*: the usual construction imports at least LPO, but we have not shown that LPO is genuinely *necessary* for the thermodynamic limit (as opposed to merely sufficient for a common proof strategy). Formalizing a representative thermodynamic-limit construction in Lean 4 and tracking whether LPO is essential — or whether an alternative route avoids it — is a concrete target for the program.

The physical content of this stronger requirement is significant. The thermodynamic limit is where phase transitions become mathematically sharp: the free energy f(β) becomes non-analytic at critical temperatures, the KMS (Kubo-Martin-Schwinger) states bifurcate into multiple coexisting phases, and spontaneous symmetry breaking occurs. Van Wierst [2019] was the first to examine these phenomena through a constructive lens, arguing that constructive mathematics forces "de-idealizations" of statistical-mechanical theories: no actual infinities, no discontinuous functions, and constructive real numbers that reflect the imperfect methods by which we determine physical quantities. (Regarding discontinuity: in BISH, WLPO is equivalent to the existence of a discontinuous function in a precise sense [Diener 2018]; absence of WLPO thus blocks one from *proving* such a function exists, though BISH does not positively assert Brouwerian continuity principles.) Our contribution here is to pin down the *specific* omniscience principle — LPO, via the Bridges-Vîță equivalence with monotone convergence — rather than leaving the constructive difficulty at the level of a general philosophical observation.

In the Haag-Kastler framework for algebraic quantum field theory [Haag 1996], infinite-volume states on the quasilocal algebra decompose into folia — equivalence classes under quasi-equivalence of GNS representations. Normal states belong to the folium of a given representation; singular states lie outside all folia. Via the GNS construction, singular states yield representations disjoint from the identity representation, physically corresponding to inequivalent thermodynamic phases or superselection sectors [Bratteli and Robinson 1997]. The passage from the predual (normal states, density matrices) to the bidual (all states, including singular) is the passage across the WLPO boundary; the further construction of the thermodynamic limit crosses the LPO boundary.

### 4.4 Non-separable functional analysis: classical choice/LEM package (route-costed)

The Hahn-Banach theorem in its full generality — separation and extension in non-separable spaces — is a different kind of non-constructive commitment from the omniscience principles above. In separable spaces, the constructive Hahn-Banach theorem (proven by Bishop) suffices. But non-separable existence proofs (Banach limits on ℓ^∞, ultrafilter constructions, singular functionals on non-separable duals) typically rely on choice principles — Zorn's lemma, the Boolean prime ideal theorem, the ultrafilter lemma — that are orthogonal to the omniscience axis.

This matters for our landscape. The main monotone story — BISH → WLPO → LPO → undecidable — tracks omniscience strength. Choice principles represent a different axis of non-constructivity, one that bundles LEM with strong existence postulates. We include this rung for completeness, but we flag it as operating on the choice/LEM axis rather than purely on the omniscience axis. A clean separation of omniscience costs from choice costs in operator algebra theory is an open problem that would significantly sharpen the landscape.

### 4.5 The spectral gap: undecidable

Cubitt, Perez-Garcia, and Wolf [2015] proved that the spectral gap problem for quantum many-body systems — determining whether the gap between the ground state energy and the first excited state remains open in the thermodynamic limit — is algorithmically undecidable (in the same sense as the Halting Problem). Moreover, they exhibited an "axiomatic independence" phenomenon: for particular families of Hamiltonians, the spectral gap question is independent of any fixed consistent recursive axiomatization. This places general spectral-gap determination beyond the omniscience hierarchy, beyond LEM, in the realm of Turing undecidability and axiomatic independence.

### 4.6 Summary

The landscape, assembled:

| Physical statement | Logical principle | Status |
|---|---|---|
| Finite-volume Gibbs state properties | BISH (constructive) | Calibrated |
| S₁(H) non-reflexivity (¬-form) | BISH (constructive) | Calibrated |
| Bidual-gap witness for S₁(H) | ≡ WLPO | Calibrated |
| Thermodynamic limit (monotone convergence route) | ≥ LPO | Route-costed |
| Non-separable existence proofs | Choice/LEM package | Route-costed |
| Spectral gap decidability (general) | Undecidable | Established (Cubitt et al.) |

The first three rows are our formalized results (the ¬-form is BISH; the witness form is WLPO). The remaining rows represent logical costs of standard constructions as identified in the literature, without verified minimality. The column "Status" distinguishes machine-verified equivalences (calibrated) from upper bounds on proof-route costs (route-costed).

The pattern is suggestive: the logical cost increases with the degree of physical idealization. Finite-volume physics, the physics of actual experiments, is constructive. Each step toward greater idealization — singular state witnesses, infinite-volume limits, non-separable duals, undecidable spectral properties — demands stronger logical resources. Whether this monotonicity reflects the structure of physics or the structure of the Banach-space formalism is the question the remainder of this paper addresses.

## 5. The Hypothesis

We now state the central hypothesis of this paper.

**Working Hypothesis (Logical Geography).** The correlation between constructive logical strength and degree of physical idealization is not an accident of the mathematical formalism. Empirical predictions — the outputs of quantum theory for finite experimental specifications — are BISH-derivable. Stronger logical principles (WLPO, LPO, LEM) enter the mathematical description of physics only through idealizations that no finite laboratory can instantiate.

This is a physical claim dressed in logical language. Its content is that the constructive hierarchy detects the boundary between what nature actually does and what mathematicians add for convenience. The WLPO threshold is where mathematical physics first outruns physical reality.

### 5.1 Distinction from operationalism and from van Wierst

The hypothesis resembles operationalism — the doctrine, associated with Bohr and the Copenhagen school, that physical theories should refer only to observable quantities and measurement procedures. But it differs in two critical respects.

First, it is formally precise. Operationalism makes a vague appeal to "observability"; our hypothesis identifies a specific logical boundary (BISH) and locates specific physical constructions (singular states, thermodynamic limits, spectral gaps) at specific positions relative to that boundary. The calibration is machine-verified, not argued by philosophical fiat.

Second, it is testable. Operationalism, as traditionally formulated, offers no mechanism for determining whether a given mathematical construction is "observable" or not — the boundary is drawn by philosophical judgment. Our hypothesis proposes a concrete criterion: a physical construction is real (in the sense of being physically instantiable) if and only if its mathematical description is BISH-derivable. This criterion can be applied to specific cases and could, in principle, be falsified.

The hypothesis also differs from van Wierst's [2019] proposal, which is the closest antecedent in the literature. Van Wierst argues that switching to constructive mathematics dissolves philosophical problems about phase transitions by forcing de-idealizations. Her argument is essentially negative: constructive mathematics *removes* problematic commitments. Our hypothesis is positive: the constructive hierarchy *reveals* the structure of physical reality, and the specific omniscience principle required by a physical construction tells you something about how far that construction departs from what nature implements. Van Wierst does not calibrate specific physical constructions to specific omniscience principles, nor does she propose a test for whether the logical costs are formalism-dependent. Her paper opens the door; ours walks through it with machine-verified coordinates.

### 5.2 Distinction from finitism

The hypothesis does not commit us to finitism. BISH is not finitist mathematics. Constructive mathematics permits infinite objects and processes: one quantifies over ℕ, forms infinite sequences, defines real numbers by effective approximation, and works with infinite-dimensional separable Hilbert spaces. What BISH lacks is specific decidability principles — the ability to decide, for an arbitrary real number, whether it is zero (WLPO) or positive (LPO). The hypothesis says nature cannot perform these decisions, not that nature is finite.

This is an important distinction. Quantum mechanics on an infinite-dimensional Hilbert space is perfectly compatible with constructive mathematics — indeed, Bishop and Bridges [1985] developed substantial portions of functional analysis constructively. What fails constructively is the *classification* of states (normal versus singular), the *convergence* of infinite-volume limits (monotone convergence), and the *existence* of specific objects beyond the reach of finite construction procedures.

### 5.3 Relation to the Church-Turing thesis

Our hypothesis stands in a natural relationship to the Church-Turing thesis as a physical principle. Deutsch [1985] proposed that the laws of physics should permit only computations consistent with the Church-Turing thesis (or its quantum generalization). This amounts to requiring that nature implement at most the computable functions.

Our hypothesis is both more and less demanding. It is more demanding in that BISH is stricter than Turing computability: there exist Turing-computable functions that are not constructively definable (because BISH requires *proofs* of totality, not mere algorithms). It is less demanding in that we do not require physical theories to be computable in the Church-Turing sense — we require only that their empirical content be expressible in BISH, which is a constraint on *logical structure* rather than *algorithmic complexity*.

The relationship to the extended Church-Turing thesis (that no physical process can compute a function not computable by a Turing machine) is also illuminating. If nature operates at BISH, then certainly the extended Church-Turing thesis holds — but the converse is false. Turing computability plus classical logic gives you more than BISH. Our hypothesis occupies a specific position between the Church-Turing thesis and full classical logic.

### 5.4 Subsumption of the digital physics critique

In a supplementary note [Lee 2026d], we derived a trilemma for digital physics programs: any program claiming the universe is fundamentally computational must either accept finitism, accept hypercomputation, or reconstruct physics constructively to avoid bidual-gap arguments. That trilemma is a corollary of the present hypothesis. If nature operates at BISH, then digital physics programs are correct in spirit — the universe is "computational" in the sense that its physical content is constructively expressible — but they typically underestimate what constructive mathematics can do (it is not finitist) and overestimate what they need (hypercomputation is unnecessary if the non-constructive content is purely idealizing). The trilemma dissolves: the third horn (constructive reconstruction) is the natural one, and the calibration landscape tells you precisely what needs to be reconstructed and at what logical cost.

## 6. The Formulation-Invariance Test

The hypothesis makes a prediction that distinguishes it from the null hypothesis (that the logical costs are artifacts of the Banach-space formalism). We propose a *metatheoretic test* — not an experimental protocol, but a formal invariance audit across mathematical presentations.

**Formulation-Invariance Test.** If the hypothesis is correct, then for any physical prediction derivable from quantum theory, the empirical content should be BISH-derivable, possibly from different mathematical premises than the classical formulation uses. If the hypothesis is wrong — if the logical costs are formalism-dependent — then there should exist an alternative mathematical formulation of the same physics at lower logical cost.

We define "empirical content" precisely: given a finite experimental specification (finite-dimensional Hilbert space, rational Hamiltonian coefficients, rational inverse temperature, rational observable, rational error tolerance ε > 0), the theory produces an interval of rational bounds for the expected value within ε. The claim is that this map from finite specifications to rational bounds is BISH-computable.

Concretely: take a physical quantity currently computed via the thermodynamic limit (an LPO-strength construction). For any finite system, the value of this quantity is computable (it is a finite-dimensional trace). The question is whether the *explanation* of why the finite-system value approximates the infinite-volume prediction can be given constructively, or whether it essentially requires LPO.

If finite-size scaling corrections — the systematic deviations of finite-system quantities from infinite-volume predictions — can be constructively bounded without invoking the infinite-volume limit, then the empirical content is BISH-available and the LPO-level construction is indeed a convenience, not a necessity. If, on the other hand, there exist finite-system predictions whose derivation from first principles essentially requires passage through an LPO-level infinite-volume limit with no constructive alternative, then the hypothesis would be under pressure.

We do not resolve this question here. We pose it as a research program.

### 6.1 The topos-theoretic alternative

The most developed alternative framework for non-classical logic in physics is the Döring-Isham topos program [Isham 1997, Döring and Isham 2008], subsequently refined by Heunen, Landsman, and Spitters [2009] into a rigorous "Bohrification" program. This body of work is substantial and directly relevant to our proposal.

The key insight of Döring-Isham is that the Kochen-Specker theorem — the impossibility of assigning definite values to all observables simultaneously — can be reinterpreted as a statement about the internal logic of a topos associated with a von Neumann algebra. In the topos of presheaves over the poset of commutative subalgebras, quantum states become probability valuations on a spectral presheaf, and the Kochen-Specker obstruction manifests as the non-existence of global sections. Crucially, the internal logic of these topoi is intuitionistic — that is, constructive.

Heunen, Landsman, and Spitters [2009] formalized this by showing that the Bohrification of a C*-algebra yields a commutative C*-algebra internal to the topos, whose Gelfand spectrum provides a non-classical phase space for the quantum system. The physical content of the theory is recovered without classical logic.

This program is both evidence for and a potential challenge to our hypothesis. It is evidence because it demonstrates independently that quantum mechanics fits naturally into an intuitionistic logical framework — precisely what our calibration landscape predicts. It is a potential challenge because the relationship between the Döring-Isham internal logic and the specific omniscience principles in our hierarchy (WLPO, LPO) has not been worked out. Do the WLPO and LPO thresholds manifest within the topos-theoretic reformulation? If the topos approach recovers all empirical predictions with only intuitionistic logic (no omniscience principles at all), this would support our hypothesis more strongly than our own Banach-space calibration does — it would suggest that the logical costs in our landscape are indeed artifacts of the classical formalism, and that the physical content is constructive. Conversely, if the topos approach encounters its own omniscience-level obstructions at the same physical thresholds (singular states, thermodynamic limits), this would provide strong evidence for formulation-invariance.

We regard the relationship between our calibration landscape and the Döring-Isham internal logic as the most important open question for the program proposed in this paper.

### 6.2 What a counterexample would look like

A decisive refutation of the hypothesis would take the following form: a *finite-system* measurement prediction — an expectation value, a correlation function, a transition probability — whose derivation from the Hamiltonian and initial state essentially requires WLPO (or a stronger principle), with no constructive alternative derivation yielding the same numerical value.

We know of no such counterexample. This is weak evidence in favor of the hypothesis, but it is the correct kind of evidence: the hypothesis survives not because it is unfalsifiable, but because no one has found the relevant counterexample. The search for such a counterexample — or for a proof that none exists — is the most immediate concrete research question our proposal generates.

## 7. Historical Precedents

The proposal that a mathematical structure might be physical rather than merely representational has significant precedents.

### 7.1 Computation as physics

Before Landauer [1961] and Bennett [1973], computation was a purely mathematical notion. The insight that computation is a physical process — requiring energy, dissipating heat, taking time — transformed information theory and eventually led to quantum computing. Deutsch [1985] sharpened this by proposing that the set of physically computable functions is determined by physics, not mathematics: quantum physics computes different functions than classical physics.

Our proposal extends this one level up. Deutsch asked: what if *computability* is physical? We ask: what if *logical strength* is physical? The constructive hierarchy (BISH, WLPO, LPO, LEM) is to our proposal what the computability hierarchy (finite automata, pushdown automata, Turing machines) was to Deutsch's.

### 7.2 Simultaneity and the operational content of mathematics

Einstein's 1905 analysis of simultaneity is the deepest precedent. Einstein asked: what physical content does the claim "two events are simultaneous" actually carry? The answer — that simultaneity requires a synchronization procedure, and different procedures yield different answers for different observers — was a foundational insight that revolutionized physics.

We ask an analogous question: what physical content does the claim "this state is singular" (or "this Banach space is non-reflexive" or "this spectral gap is zero") actually carry? Our formalized results provide a precise answer: these claims carry the logical content of specific omniscience principles. Whether this logical content has physical substance — whether the universe "decides" these questions or whether they are artifacts of the formalism — is the question our hypothesis addresses.

### 7.3 Constructive mathematics as physics

There is a long tradition of advocating constructive mathematics as the natural language for computation and analysis. Bishop [1967] framed constructive analysis as mathematics done with an algorithmic interpretation. Bridges and Richman [1987] systematized the varieties of constructive mathematics. Beeson [1985] developed the metamathematical foundations. Ishihara [2006] initiated the specific program of constructive reverse mathematics, calibrating classical theorems against omniscience principles. Diener [2018] compiled the most comprehensive survey to date. Brattka and Gherardi [2009] connected omniscience principles to the Weihrauch lattice, providing a topological and computational counterpart to the logical classification. The mathematical infrastructure for our proposal has been built by these researchers over decades.

Our proposal makes a claim that goes beyond the "constructive mathematics is better for computation" argument. We are not claiming that constructive proofs are more informative (though they are) or that they yield algorithms (though they do). We are claiming that the *boundary* of constructive provability — the exact point where WLPO, LPO, or LEM becomes necessary — tracks the *boundary* of physical reality. This is a much stronger claim, and it is the one that our calibration landscape, together with van Wierst's philosophical analysis and the Döring-Isham program's independent use of intuitionistic logic in physics, makes precise enough to investigate.

## 8. Open Questions

1. **The LPO calibration.** Our formalized results establish equivalences at the WLPO level. The claim that the thermodynamic limit requires LPO rests on the known equivalence between monotone convergence for bounded real sequences and LPO [Bridges and Vîță 2006], together with the observation that the standard construction of infinite-volume free energies uses monotone convergence. A formal verification of this logical cost — analogous to our WLPO results — would strengthen the calibration landscape significantly.

2. **Formulation-invariance.** Can the empirical predictions of quantum statistical mechanics be recovered from a mathematical framework that avoids the LPO-level thermodynamic limit entirely? Finite-size scaling theory provides approximations; the question is whether exact finite-system predictions can be derived without passing through the infinite-volume limit.

3. **The Döring-Isham connection.** What is the relationship between our calibration landscape and the internal logic of the Döring-Isham topoi? Specifically, where do the WLPO and LPO thresholds manifest within the topos-theoretic reformulation?

4. **Experimental signatures.** Are there observable consequences of the hypothesis — measurable differences between a BISH-universe and an LPO-universe? Finite-size scaling exponents are the most natural candidates, but the connection remains to be worked out.

5. **Other physical theories.** The calibration landscape presented here is specific to quantum statistical mechanics. Does a similar hierarchy arise for general relativity, for quantum field theory on curved spacetimes, or for string theory? The Schwarzschild formalization [Lee 2026c] suggests that analogous logical costs appear in general relativity, but the analysis has not been carried out systematically.

6. **The invariance question.** Is the logical cost of a physical theorem formulation-invariant? If the non-reflexivity of S₁(H) can be avoided by reformulating quantum state spaces categorically (e.g., via the C*-algebraic framework), does the WLPO cost disappear or merely migrate to a different theorem? This is perhaps the most fundamental open question for the program.

## 9. Conclusion

The machine-verified results of [Lee 2026a, 2026b] establish that the mathematical infrastructure of quantum mechanics — the Banach space structure of the quantum state space — carries precise logical commitments that can be calibrated against the constructive hierarchy of omniscience principles. The resulting landscape reveals a monotone correlation between logical strength and physical idealization: what can be measured in a finite laboratory is constructive; what requires infinite-volume limits, singular states, or spectral gap decisions demands progressively stronger logical principles.

We have proposed a hypothesis to explain this correlation: nature operates at the constructive level, and stronger logical principles are artifacts of idealization. We have distinguished this hypothesis from operationalism and finitism, articulated a concrete test (formulation-invariance of logical costs), and situated the proposal within the broader landscape of constructive approaches to physics.

The hypothesis may be wrong. The logical costs may be accidents of the Banach-space formalism — features of our mathematical language rather than of the world. But the correlation is there, it is precise, and it is machine-verified. We believe it merits investigation.

If the hypothesis is right, the constructive hierarchy is not a classification of proof techniques. It is a map of physical reality — a logical geography of what nature computes.

---

## References

- Beeson, M. J. *Foundations of Constructive Mathematics*. Springer, Berlin, 1985.
- Bennett, C. H. "Logical reversibility of computation." *IBM Journal of Research and Development* 17(6): 525–532, 1973.
- Bishop, E. *Foundations of Constructive Analysis*. McGraw-Hill, New York, 1967.
- Bishop, E. and Bridges, D. *Constructive Analysis*. Grundlehren der mathematischen Wissenschaften, vol. 279. Springer, Berlin, 1985.
- Brattka, V. and Gherardi, G. "Weihrauch degrees, omniscience principles and weak computability." In *6th International Conference on Computability and Complexity in Analysis (CCA'09)*, OASIcs vol. 11, pp. 83–94. Schloss Dagstuhl, 2009.
- Bratteli, O. and Robinson, D. W. *Operator Algebras and Quantum Statistical Mechanics*, vol. 1. Springer, New York, 2nd ed., 1987.
- Bratteli, O. and Robinson, D. W. *Operator Algebras and Quantum Statistical Mechanics*, vol. 2. Springer, Berlin, 2nd ed., 1997.
- Bridges, D. and Richman, F. *Varieties of Constructive Mathematics*. Cambridge University Press, Cambridge, 1987.
- Bridges, D. and Vîță, L. S. *Techniques of Constructive Analysis*. Universitext. Springer, New York, 2006.
- Cubitt, T. S., Perez-Garcia, D., and Wolf, M. M. "Undecidability of the spectral gap." *Nature* 528(7581): 207–211, 2015.
- Deutsch, D. "Quantum theory, the Church-Turing principle and the universal quantum computer." *Proceedings of the Royal Society A* 400(1818): 97–117, 1985.
- Diener, H. "Constructive reverse mathematics." arXiv:1804.05495, 2018.
- Döring, A. and Isham, C. J. "A topos foundation for theories of physics: I. Formal languages for physics." *Journal of Mathematical Physics* 49: 053515, 2008. (Parts II–IV: JMP 49: 053516–053518.)
- Haag, R. *Local Quantum Physics: Fields, Particles, Algebras*. Springer, Berlin, 2nd ed., 1996.
- Heunen, C., Landsman, N. P., and Spitters, B. "A topos for algebraic quantum theory." *Communications in Mathematical Physics* 291: 63–110, 2009.
- Isham, C. J. "Topos theory and consistent histories: The internal logic of the set of all consistent sets." *International Journal of Theoretical Physics* 36: 785–814, 1997.
- Ishihara, H. "Reverse mathematics in Bishop's constructive mathematics." *Philosophia Scientiæ* CS 6: 43–59, 2006.
- Landauer, R. "Irreversibility and heat generation in the computing process." *IBM Journal of Research and Development* 5(3): 183–191, 1961.
- Landsman, N. P. *Foundations of Quantum Theory: From Classical Concepts to Operator Algebras*. Springer, Cham, 2017.
- Lee, P. C.-K. "The bidual gap: A Lean 4 formalization of WLPO and non-reflexivity in Banach spaces." Preprint, 2026a. doi:10.5281/zenodo.18501689.
- Lee, P. C.-K. "The physical bidual gap and Banach space non-reflexivity: A Lean 4 formalization of WLPO via trace-class operators." Preprint, 2026b. doi:10.5281/zenodo.18509795.
- Lee, P. C.-K. "Formalizing Einstein's equations for Schwarzschild spacetime in Lean 4." Preprint, 2026c. [TODO: add Zenodo DOI]
- Lee, P. C.-K. "Digital physics and the bidual gap: Why computational universes cannot verify Banach space non-reflexivity." Supplementary note, 2026d. Available at ResearchGate.
- Takesaki, M. *Theory of Operator Algebras I*. Springer, New York, 1979.
- van Wierst, P. "The paradox of phase transitions in the light of constructive mathematics." *Synthese* 196(5): 1863–1884, 2019.
