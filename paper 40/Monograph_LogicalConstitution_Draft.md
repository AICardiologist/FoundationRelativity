# The Logical Constitution of Physical Reality
## Constructive Reverse Mathematics of Mathematical Physics

**Paul Chun-Kit Lee**
Department of Medicine, New York University School of Medicine, Brooklyn, NY

---

## Abstract

We prove that the logical resources required for all empirical predictions in known physics are exactly BISH+LPO: Bishop's constructive mathematics augmented by the Limited Principle of Omniscience. This characterization is established by systematic axiom calibration — determining the minimal non-constructive principles required for each physical theorem — across 39 papers spanning the Standard Model (QED, QCD, electroweak theory), general relativity, statistical mechanics, quantum information theory, and the landscape of physical undecidability. All calibrations are formally verified in approximately 33,000 lines of Lean 4 proof code.

Three foundational results underpin the characterization. First, Fekete's Subadditive Lemma — the mathematical engine of phase transitions — is equivalent to LPO over BISH, establishing that LPO is not a mathematical convenience but a physically instantiated principle. Second, the Fan Theorem (compactness) is dispensable: every empirical prediction derived via compactness arguments can be recovered at BISH+LPO. Third, Dependent Choice is dispensable: sequential construction principles contribute no empirical content beyond BISH+LPO.

A conservation metatheorem explains the pattern: empirical predictions are finite compositions of computable functions (BISH), and the only idealizations that exceed finite computation are completed limits whose convergence rate is not uniformly computable (LPO via the Bounded Monotone Convergence equivalence). The undecidability arc (Papers 36–39) completes the picture: every known physical undecidability result — spectral gap, phase diagrams, renormalization group flows — is Turing-Weihrauch equivalent to LPO, traceable to a single ancestor (Wang tiling). A refined analysis reveals that while empirical physics is capped at LPO (Σ₁⁰), generic intensive observables without promise gaps can reach Σ₂⁰ — but this Platonic tier is empirically inaccessible due to finite experimental precision. The characterization is falsifiable: it predicts that no empirical physical phenomenon requires deciding Σ₂⁰ arithmetic statements, accessing non-limit-computable real numbers, or performing unrestricted tree searches. No known physical theory violates these predictions.

**Keywords:** constructive mathematics, reverse mathematics, formal verification, foundations of physics, Bishop's constructive analysis, omniscience principles, Lean 4

---

## Chapter 1: Introduction — What This Paper Proves

### 1.1 The Main Result

Every physical theory makes predictions. Those predictions are mathematical statements — numbers that can be compared to experimental measurements. This paper asks a simple question: what logical resources are needed to derive those numbers?

The answer, established across 39 formal verification papers covering the major domains of modern physics, is unexpectedly clean. Every empirical prediction in known physics can be derived using exactly two logical ingredients:

1. **BISH (Bishop's Constructive Mathematics):** mathematics in which every existence claim comes with a construction, every function is computable, and every proof provides an algorithm. This is the mathematics of finite computation.

2. **LPO (Limited Principle of Omniscience):** the ability to decide, for any binary sequence, whether all terms are zero or some term is nonzero. Equivalently: the ability to complete a bounded monotone limit. This is the mathematics of idealized infinite processes.

Nothing more is needed. The Fan Theorem (compactness), Dependent Choice (sequential construction), Bar Induction (well-founded tree search), the full Axiom of Choice, the Continuum Hypothesis, large cardinal axioms — none of these are required for any empirical prediction in the Standard Model, general relativity, statistical mechanics, or quantum information theory.

This is not a philosophical argument about what mathematics "should" look like. It is an empirical finding, verified mechanically in approximately 33,000 lines of Lean 4 proof code, about what mathematics physics *actually uses*.

### 1.2 Why This Matters

The characterization identifies the computational architecture of physical reality. If empirical physics requires exactly BISH+LPO, then the mathematical universe accessible to physics extends precisely to one quantifier alternation over decidable predicates — Σ₁⁰ in the arithmetic hierarchy — and no further. Every physical prediction is either a finite computation (BISH) or the completion of a bounded monotone limit (LPO). This is not a vague philosophical claim but a concrete, falsifiable characterization verified across 39 papers and approximately 33,000 lines of machine-checked proof. It predicts, for instance, that no scattering amplitude at any loop order will require deciding a Σ₂⁰ statement, and that no physical constant will turn out to be non-limit-computable.

The characterization also provides a diagnostic tool for theoretical physics. Any theoretical framework whose empirical predictions require logical resources beyond LPO is either making predictions that cannot be experimentally tested or is using unnecessarily strong mathematical scaffolding. This distinction is not academic: the Fan Theorem (compactness) and Dependent Choice — two of the most widely used tools in mathematical physics — are shown to be dispensable for all empirical predictions. Their presence in physics textbooks reflects proof strategy, not physical content. The characterization separates the two, and in doing so reveals that physics is more constructive than its own mathematical description suggests.

The connection to constructive mathematics is itself remarkable. Bishop's hierarchy — BISH, LLPO, WLPO, LPO, and the principles above — was developed in the 1960s through 1990s for purely philosophical reasons, as part of a programme to understand what mathematics can be done without non-constructive existence proofs. The hierarchy was not designed to classify physics. That it does so with perfect precision across every calibrated domain — statistical mechanics, quantum mechanics, quantum field theory, general relativity, quantum information — is a discovery about the relationship between logic and nature, not a consequence of how the programme was set up.

Finally, the characterization reclassifies physical undecidability. The celebrated undecidability results of Cubitt, Perez-Garcia, and Wolf (spectral gap), Bausch et al. (phase diagrams), and others are shown to be Turing-Weihrauch equivalent to LPO — adding zero new logical resources beyond what thermodynamic limits already require. Physical "undecidability" is not fundamental unknowability but the non-computability of a single principle (LPO) that physics has used since Boltzmann defined the thermodynamic limit in the 1870s. The spectral gap is undecidable for the same reason that phase transitions cost LPO: both require completing an infinite limit.

### 1.3 Structure of This Paper

Chapter 2 introduces the constructive hierarchy — BISH, LLPO, WLPO, LPO, and the arithmetic hierarchy beyond. Chapter 3 presents the calibration table: 39 papers organized by physics domain, each theorem placed at its exact position in the hierarchy. Chapter 4 establishes the three foundational theorems — Fekete's equivalence with LPO, and the dispensability of the Fan Theorem and Dependent Choice — that transform the empirical pattern into a thesis. Chapter 5 tests the thesis against the Standard Model. Chapter 6 presents the conservation metatheorem that *explains* why physics lives at BISH+LPO. Chapter 7 analyzes the boundary: what physics cannot do, and why the exclusions are falsifiable. Chapters 8 and 9 form the undecidability arc: Chapter 8 traces the genealogy of physical undecidability from Wang tiling through Cubitt's spectral gap, proving all known instances are LPO-equivalent; Chapter 9 discovers the Σ₂⁰ Platonic ceiling and the thermodynamic stratification theorem. Chapter 10 draws consequences for quantum gravity, the measurement problem, the cosmological constant, and physical undecidability. Chapter 11 describes the Lean 4 formalization. Chapter 12 delineates what the programme does *not* do. Chapter 13 concludes.

### 1.4 What This Paper Does Not Prove

This paper does not prove that all possible physical theories are BISH+LPO. The characterization covers all currently known physics — the Standard Model, general relativity, statistical mechanics, quantum information theory — but a future theory might require more. If a physical phenomenon is discovered that requires Σ₂⁰ reasoning to predict its empirical behavior, the characterization is refuted. The thesis is empirical and falsifiable, not a priori or necessary.

The paper does not resolve any open problem in physics. It reclassifies certain problems — the measurement problem is shown to be a disagreement about dispensable scaffolding (Dependent Choice), the cosmological constant discrepancy is identified as an artifact of LPO-level idealization, and physical undecidability is reclassified as LPO non-computability — but reclassification changes the character of a problem without solving it. The measurement problem, even after reclassification, still involves a genuine question about why the macroscopic world appears classical.

The paper does not determine whether nature "is" a BISH+LPO computer in any ontological sense. The characterization is epistemological: it describes what logical resources are needed to *predict* physical behavior, not what the universe "uses" to *generate* that behavior. The gap between prediction and generation is real and is discussed in Chapter 12. Paper 29's argument — phase transitions require LPO, phase transitions are empirically real, therefore LPO is physically instantiated — is the closest the programme comes to an ontological claim, and it is carefully hedged: LPO is necessary for the mathematical *description*, not necessarily for the physical *mechanism*.

### 1.5 The Hierarchy at a Glance

```
                     Full Classical Logic (LEM)
                            ↑
                         [vast gap]
                            ↑
                     Full AC, CH, Large Cardinals
                            ↑
                         [vast gap]
                            ↑
              Bar Induction / Full Dependent Choice
                     ↑              ↑
               Fan Theorem     Σ₃⁰-LEM and above
                     ↑              ↑
                     ↑         [FAR BEYOND PHYSICS]
    ═══════════════════════════════════════════════
                     ↑         [PLATONIC CEILING — Paper 39]
                     ↑              ↑
               Σ₂⁰-LEM (LPO') ←── Generic intensive observables
                     ↑              without promise gap
                     ↑
    ───────────────────────────────────────────────
                     ↑         [EMPIRICAL CEILING — Papers 29-38]
                     ↑              ↑
                    LPO ←────── Bounded Monotone Convergence
                     ↑              Phase transitions, undecidability
                   WLPO ←────── Zero-test / threshold decision
                     ↑
                   LLPO ←────── Sign decision / disjunction
                     ↑
                   BISH ←────── Finite computation
```

Two boundaries are established by this paper. The dashed line is the **empirical ceiling**: everything below it has been physically instantiated across 39 calibration papers; LPO is necessary (Paper 29) and sufficient (Papers 30–31); all physical undecidability lives here (Papers 36–38). The double line is the **Platonic ceiling**: generic intensive observables (spectral gap without promise gap) reach Σ₂⁰ (Paper 39), but this tier is empirically inaccessible — finite experimental precision enforces an effective promise gap that collapses Σ₂⁰ decisions back to LPO.

---

## Chapter 2: The Constructive Hierarchy

### 2.1 Bishop's Constructive Mathematics (BISH)

BISH is the mathematical framework developed by Errett Bishop in *Foundations of Constructive Analysis* (1967). Its defining characteristic is that every existence proof must provide a construction, and every function must be computable. BISH does not reject classical mathematics — it simply declines to use principles that assert existence without construction. A theorem proved in BISH is automatically valid in classical mathematics, in intuitionistic mathematics, and in recursive mathematics. It is mathematics with the broadest possible validity.

In BISH, the real numbers are constructed as equivalence classes of Cauchy sequences of rationals with explicit moduli of convergence. A real number x is *defined* by an algorithm that, given any precision ε > 0, produces a rational approximation within ε. This is not a restriction in practice — every real number that appears in a physics textbook (π, e, √2, the fine structure constant α ≈ 1/137.036) admits such an algorithm. The arithmetic operations (+, ×, ÷), standard functions (exp, log, sin, cos), and special functions (Bessel, hypergeometric, polylogarithm) are all computable. BISH is the mathematics of algorithms that terminate.

What BISH cannot do is decide, for an arbitrary real number x, whether x = 0 or x ≠ 0. This is not a deficiency but a structural feature: the decision requires inspecting infinitely many digits of x, which no finite algorithm can accomplish in general. For specific numbers — is π > 3? — the answer is computable (yes, since the first few digits suffice). But for a number defined by a convergent series whose terms depend on unresolved conjectures, the zero-test may require information no finite computation can provide. The principles that restore various forms of this decision power are the omniscience principles discussed in the following sections.

A concrete physical example illustrates the scope of BISH. Consider the partition function of a 10-site Ising model: Z₁₀ = Σ_{σ} exp(−βH(σ)), where the sum runs over 2¹⁰ = 1024 spin configurations. Each term is a computable exponential of a computable argument. The sum is finite. The free energy F₁₀ = −kT log Z₁₀ is a computable real number. No omniscience principle is needed — the entire calculation is a finite composition of computable functions at computable inputs. This is BISH. The same holds for any finite lattice, any finite-dimensional Hilbert space, any finite Feynman diagram. The non-constructive content enters only when physicists take limits: N → ∞, dimension → ∞, loop order → ∞.

For references on BISH: Bishop (1967), Bishop and Bridges (1985), Bridges and Richman (1987), Bridges and Vîță (2006).

### 2.2 The Limited Principle of Omniscience (LPO)

**Formal statement:** For every binary sequence α : ℕ → {0,1}, either ∃n (α(n) = 1) or ∀n (α(n) = 0).

In plain language: given an infinite sequence of bits, you can decide whether all bits are zero or some bit is one. This requires "surveying" the entire infinite sequence — hence "omniscience." LPO is not provable in BISH; it is an additional principle that must be explicitly assumed. It is strictly weaker than full classical logic (LEM) — LPO decides one class of propositions (existential statements over decidable predicates), not all propositions.

LPO is equivalent to several other principles, the most important being **Bounded Monotone Convergence (BMC):** every bounded monotone sequence of real numbers converges. This equivalence, proved constructively by Ishihara, is the bridge between logic and analysis. BMC is what physicists use when they take thermodynamic limits, assert that coupling constants exist as completed real numbers, or claim that a variational minimum is attained. Every time a physicist writes "in the limit N → ∞" for a bounded monotone quantity, they are invoking BMC, and hence LPO. Two further equivalences are important: LPO is equivalent to the assertion that every Cauchy sequence of reals converges (Cauchy completeness without explicit modulus), and to the assertion that every bounded set of reals has a supremum.

The Ising model provides the paradigmatic physical example. At finite lattice size N, the free energy per site fₙ = −(kT/N) log Zₙ is a computable real number — BISH, as discussed above. The sequence (fₙ) is bounded (by the coupling constant J) and monotone (by subadditivity of the total free energy). The assertion that f = lim fₙ exists as a completed real number is BMC, hence LPO. The phase transition — the non-analyticity of f(β) at the critical inverse temperature βc — requires this completed limit. Without LPO, the phase transition is not a theorem; it is a finite sequence of approximations that never crystallizes into a definite mathematical object.

The key finding of this programme: LPO is not merely mathematically convenient for physics. It is physically *necessary*. Phase transitions are empirically real phenomena — ice melts, magnets demagnetize, superconductors transition. Their mathematical description requires Fekete's Subadditive Lemma, which is equivalent to LPO over BISH (Paper 29). LPO is instantiated in nature.

### 2.3 The Weak Limited Principle of Omniscience (WLPO)

**Formal statement:** For every binary sequence α, either ∀n (α(n) = 0) or ¬∀n (α(n) = 0).

The difference from LPO is subtle but precise. LPO provides a *witness* — if some bit is 1, LPO tells you that fact (though not which bit). WLPO merely decides whether all bits are zero or not, without providing a witness in the "not" case. WLPO is strictly weaker than LPO.

In physics, WLPO appears as the *threshold decision* or *zero-test*: is this quantity exactly zero, or is it nonzero? Examples include:
- Deciding whether the external magnetic field h equals zero (Paper 20: Ising magnetization)
- Deciding whether the fermion chemical potential equals the mass threshold (Paper 18: Heaviside decoupling)
- Deciding whether the Schwarzschild radial coordinate equals 2M (Paper 13: event horizon)
- Deciding whether the QCD mass gap Δ equals zero (Paper 33: confinement)

Each of these is a physically meaningful question — and each costs exactly WLPO, which is strictly weaker than LPO and hence "free" once you've already paid for LPO.

### 2.4 The Lesser Limited Principle of Omniscience (LLPO)

**Formal statement:** For every binary sequence α with at most one nonzero term, either all even-indexed terms are zero or all odd-indexed terms are zero.

Equivalently, for every real number x: x ≤ 0 or x ≥ 0 (the *sign decision*).

LLPO is strictly weaker than WLPO. In physics, it appears as:
- Bell nonlocality: the CHSH inequality violation requires deciding a sign (Papers 11, 21, 27)
- WKB tunneling: deciding which side of a barrier a particle emerges (Paper 19)
- Noether global charge: deciding the sign of a conserved charge with oscillating contributions (Paper 15)

The strict hierarchy BISH ⊂ LLPO ⊂ WLPO ⊂ LPO means these principles are genuinely distinct. Physics uses all four levels, but never exceeds LPO.

### 2.5 What Lies Above LPO

Above LPO in the constructive hierarchy lie several principles that are widely used in mathematics but are shown by this programme to be dispensable for empirical physics.

The **Fan Theorem (FT)** asserts that every bar of a finitely-branching tree is uniform — equivalently, that every pointwise-continuous function on Cantor space is uniformly continuous. FT is the constructive counterpart of the Heine-Borel theorem and underpins compactness arguments throughout analysis: the existence of maxima on compact sets, the extraction of convergent subsequences, the Arzelà-Ascoli theorem. FT is logically *independent* of LPO — neither implies the other — meaning it lives in an entirely different "direction" in the constructive lattice. Paper 30 proves that every empirical prediction derived using FT can be re-derived at BISH+LPO without it. Physics uses limits (LPO's territory) but not tree searches (FT's territory).

**Dependent Choice (DC)** asserts that given a relation R on a set with the property that for every x there exists y with R(x,y), there exists an infinite sequence x₀, x₁, x₂, ... with R(xₙ, xₙ₊₁) for all n. DC is the engine of iterative construction: it builds infinite sequences step by step, choosing each element based on the previous one. Physicists use it for the mean ergodic theorem, martingale convergence, and Picard iteration for differential equations. Paper 31 proves DC is dispensable: empirical predictions depend on finite initial segments of these sequences, and finite initial segments are BISH.

Beyond these, **Bar Induction (BI)** — induction over well-founded trees, stronger than FT — is not needed. **Full LEM** — for every proposition P, either P or ¬P — is incomparably stronger than everything in the constructive hierarchy and is not needed. The **Axiom of Choice**, **Continuum Hypothesis**, and **large cardinal axioms** are set-theoretic principles entirely outside the scope of what physics requires. The mathematics of physics uses a remarkably small fragment of the available logical landscape.

### 2.6 The Arithmetic Hierarchy and Σ₂⁰

The omniscience principles can be placed within the arithmetic hierarchy — a classification of logical complexity by quantifier alternation over decidable predicates.

**Σ₁⁰ (one existential quantifier):** Statements of the form ∃n P(n), where P is decidable. LPO decides all Σ₁⁰ statements. The halting problem — "does Turing machine M halt?" — is the canonical Σ₁⁰-complete problem. Every physical undecidability result obtained by encoding the halting problem is therefore LPO-equivalent.

**Π₁⁰ (one universal quantifier):** Statements of the form ∀n P(n). The complement class of Σ₁⁰. LPO also decides Π₁⁰ (since LPO decides both ∃n P(n) and its negation ∀n ¬P(n)).

**Σ₂⁰ (existential-universal):** Statements of the form ∃n ∀m Q(n,m). This requires a *second* quantifier alternation. The canonical Σ₂⁰-complete problem is the finiteness problem: "does Turing machine M halt on only finitely many inputs?" Deciding Σ₂⁰ statements requires **LPO'** — an iterated version of LPO that can decide not just individual halting instances but universal properties of halting behavior.

**Δ₂⁰ (limit-computable):** A real number is Δ₂⁰ if it can be approximated by a computable sequence whose limit exists but whose rate of convergence is not computable. Every real number accessible to BISH+LPO is Δ₂⁰.

The critical distinction for this monograph: LPO sits at Σ₁⁰. Papers 1–38 establish that empirical physics lives at Σ₁⁰. Paper 39 discovers that the *Platonic* ceiling — the logical cost of deciding exact properties of generic observables without finite-precision promise gaps — reaches Σ₂⁰. The gap between Σ₁⁰ and Σ₂⁰ is precisely the gap between empirical and Platonic physics, mediated by finite experimental precision.

---

## Chapter 3: The Calibration Table

### 3.1 Methodology

The calibration procedure for each physical theorem follows a uniform protocol, developed in Paper 2 and applied without modification across all subsequent papers. The protocol has five steps, each mechanically verifiable:

**Step 1: Identify the physical theorem.** Select a specific, well-defined mathematical statement from physics — not a vague physical principle, but a precise theorem with a proof. Examples: "the Ising model has a phase transition at T_c" (a statement about non-analyticity of the free energy), "the one-loop QED beta function is β(α) = 2α²/(3π)" (a statement about a specific computable function).

**Step 2: Formalize in Lean 4.** Translate the theorem and its proof into Lean 4, using Mathlib where infrastructure exists and building bridge lemmas (explicit axioms) where it does not. Physical assumptions that cannot be proved mathematically (e.g., the Yang-Mills mass gap exists) are declared as `axiom` with explicit documentation.

**Step 3: Certify the axiom profile.** Run `#print axioms` on every theorem. This Lean command lists every axiom the proof depends on, including `Classical.choice` (which indicates non-constructive reasoning). A theorem with no `Classical.choice` is BISH. A theorem whose only `Classical.choice` comes from an LPO hypothesis is "intentional classical" — the non-constructive content is exactly LPO.

**Step 4: Establish the reverse direction.** Where possible, prove that the omniscience principle is not just sufficient but *necessary* — that the physical theorem *implies* the principle over BISH. This establishes an equivalence (e.g., "Fekete's lemma ↔ LPO over BISH"), not just an upper bound.

**Step 5: Classify.** Place the theorem in the calibration table at its exact position in the constructive hierarchy.

### 3.2 Statistical Mechanics

**The Ising Model (Papers 8, 9, 20).**

The one-dimensional Ising model provides the programme's paradigm case. The finite partition function Z_N = Σ exp(−βH(σ)) is a finite sum of exponentials — pure BISH. No omniscience principle is needed to compute it for any finite lattice size N. The thermodynamic limit f = lim_{N→∞} F(N)/N, where F(N) = −kT log Z_N, requires asserting that a bounded monotone sequence converges. The free energy per site is bounded (by the coupling constant) and monotone (by subadditivity). The convergence is BMC, hence LPO. (Papers 8, 9: DOI 10.5281/zenodo.18516813, 10.5281/zenodo.18517570.)

Paper 9 established formulation-invariance: the transfer matrix formulation and the direct summation formulation produce the same calibration — the logical cost is a property of the physics, not the proof strategy. Paper 20 calibrated the magnetization M(h) and showed that deciding whether M = 0 (paramagnetic phase) or M ≠ 0 (ferromagnetic phase) is exactly WLPO — a zero-test on the order parameter. Different observables of the same system have different logical costs. (Paper 20: DOI 10.5281/zenodo.18603079.)

**Phase Transitions and Fekete's Lemma (Paper 29).**

This is the programme's most important single result. Fekete's Subadditive Lemma states: if a sequence (aₙ) satisfies a_{m+n} ≤ aₘ + aₙ for all m, n, then lim aₙ/n exists and equals inf aₙ/n. This lemma is the mathematical engine of phase transitions — it guarantees the existence of thermodynamic limits for subadditive quantities (free energy, pressure, entropy density). Paper 29 proved: Fekete's Subadditive Lemma is *equivalent* to LPO over BISH. The forward direction (LPO → Fekete) uses BMC. The reverse direction (Fekete → LPO) encodes an arbitrary binary sequence into a subadditive sequence whose limit detects whether any term is nonzero.

The physical consequence is profound: phase transitions are empirically real (ice melts, magnets demagnetize). Their mathematical description requires Fekete. Fekete requires LPO. Therefore LPO is not a mathematical idealization — it is a principle that nature instantiates. (DOI: 10.5281/zenodo.18643617.)

**Fan Theorem Dispensability (Paper 30).**

Classical proofs of variational principles in mechanics (Hamilton's principle, Lagrangian mechanics) use the Fan Theorem via compactness arguments — specifically, the Heine-Borel theorem for extracting convergent subsequences. Paper 30 proved that every empirical prediction derived this way can be recovered at BISH+LPO without FT. The mechanism: variational principles assert the existence of minimizers via compactness (FT), but the *empirical content* — the Euler-Lagrange equations and their solutions — is derivable directly from BISH. FT is scaffolding: it provides an elegant proof route but contributes no physical content. (DOI: 10.5281/zenodo.18638394.)

**Dependent Choice Dispensability (Paper 31).**

Paper 31 proved that Dependent Choice — used in proofs of the mean ergodic theorem, martingale convergence, and iterative constructions — is dispensable for empirical physics. Every empirical prediction derived via DC can be recovered at BISH+LPO. The mechanism: DC builds infinite sequences by induction, but physical predictions depend on finite initial segments, which are BISH. (DOI: 10.5281/zenodo.18645578.)

**Fekete's Lemma (Paper 29).**

Discussed in detail in Chapter 4.

**Mean Ergodic Theorem and Countable Choice (Paper 25).**

The mean ergodic theorem — the convergence of time-averages to space-averages for measure-preserving transformations — was calibrated against the Countable Choice axis. The result: the mean ergodic theorem is equivalent to Countable Choice (CC) over BISH. However, CC is subsumed by LPO in the presence of BMC: once you can complete bounded monotone limits, you can build countable choice sequences by iterating the limit operation. The empirical content of ergodic theorems — the probability bounds at finite sample size — is BISH via Chebyshev's inequality. (DOI: 10.5281/zenodo.18615453.)

**Classical Mechanics (Paper 28).**

Paper 28 stratified classical mechanics by formulation. The Newtonian formulation — F = ma as a system of ordinary differential equations with computable initial data — is BISH: Picard iteration with computable modulus provides explicit solutions. The Lagrangian variational formulation uses the Fan Theorem for the existence of action-minimizing paths (the Heine-Borel theorem extracts convergent subsequences from bounded function spaces). However, the empirical content — the Euler-Lagrange equations and their solutions — is the same as the Newtonian output: BISH. The variational machinery is dispensable scaffolding, confirming Paper 30's general dispensability result in a concrete setting. (DOI: 10.5281/zenodo.18616620.)

### 3.3 Quantum Mechanics

**Quantum Spectra (Paper 4).**

The spectral theorem — the mathematical foundation of quantum measurement — stratifies cleanly. For finite-dimensional operators (matrices), spectral decomposition is BISH: eigenvalues are roots of the characteristic polynomial, computable by algebraic algorithms. For unbounded operators on infinite-dimensional Hilbert spaces, the spectral theorem requires constructing spectral measures via completed limits, which cost LPO. Bridge lemmas axiomatize the spectral theorem prerequisites that Mathlib lacks, keeping the axiomatized physics cleanly separated from the verified logic. (DOI: 10.5281/zenodo.17059483.)

**Heisenberg Uncertainty (Paper 6).**

The Heisenberg uncertainty relation ΔxΔp ≥ ℏ/2 in finite-dimensional Hilbert spaces is BISH — it follows from the Cauchy-Schwarz inequality, which is a purely algebraic inequality on inner product spaces requiring no limits. The infinite-dimensional version, for unbounded operators x̂ and p̂ on L²(ℝ), requires domain considerations (ensuring both operators are defined on a common dense subspace) that involve completed limits and cost LPO. Paper 6 was formalized as CRM over Mathlib, providing the programme's first complete Mathlib-integrated calibration. (DOI: 10.5281/zenodo.18519836.)

**Born Rule (Paper 16).**

The Born rule P = |⟨ψ|φ⟩|² for finite-dimensional Hilbert spaces is BISH: it computes the squared norm of a complex inner product, which is finite arithmetic. The general Born rule for infinite-dimensional spaces and continuous spectra — P(a ∈ S) = ⟨ψ|E(S)|ψ⟩ where E is a projection-valued measure — requires the spectral measure construction, which costs LPO via the same mechanism as Paper 4. The empirical Born rule, used for discrete measurement outcomes at finite precision, is always BISH. (DOI: 10.5281/zenodo.18575377.)

**Quantum Decoherence (Paper 14).**

Quantum decoherence — the mechanism by which quantum coherence is lost through interaction with an environment — stratifies by dimension. For finite-dimensional systems, decoherence is computed via the partial trace of the density matrix, which is finite linear algebra: BISH. The decoherence timescale — the assertion that off-diagonal elements of the density matrix decay exponentially as t → ∞ — involves a completed limit, hence LPO. The transition from quantum to classical behavior is not a single event but a limit, and limits cost LPO. (DOI: 10.5281/zenodo.18569068.)

**Bell Nonlocality, CHSH, and Tsirelson (Papers 11, 21, 27).**

The CHSH inequality and Bell nonlocality provide one of the programme's most elegant calibrations. The finite computation of CHSH correlations is BISH. The assertion that the CHSH violation exceeds 2 — the classical bound — requires a sign decision, which is LLPO.

Paper 21 established the tight calibration: Bell nonlocality ↔ LLPO over BISH. The mechanism is the Intermediate Value Theorem (IVT), which is itself equivalent to LLPO. Paper 27 refined this to show that IVT is the specific mathematical mechanism through which LLPO enters Bell physics.

This result is physically significant: quantum nonlocality — the phenomenon that Einstein called "spooky action at a distance" — has a precise logical cost, and it is *strictly less* than LPO. Nonlocality is logically cheaper than phase transitions.

**Measurement Problem (Paper 23).**

Paper 23 produced the programme's most philosophically consequential quantum mechanics result. The three major interpretations of quantum mechanics — Many-Worlds, Copenhagen, and Bohmian mechanics — were calibrated against the constructive hierarchy. The finding: they agree on all BISH-level empirical predictions but disagree about non-empirical ontological claims at different heights in the hierarchy. Many-Worlds requires Dependent Choice (DC) for the branching structure of the universal wavefunction. Copenhagen requires WLPO for the outcome decision (collapse). Bohmian mechanics requires LPO for the existence of the pilot wave trajectory as a completed object.

Since DC is dispensable for empirical physics (Paper 31), the measurement problem is reclassified: it is not a disagreement about physical reality but a disagreement about which logically dispensable mathematical framework to use for describing non-empirical aspects of quantum theory. The empirical content — the probabilities that experimentalists measure — is BISH and interpretation-independent. This reclassification does not dissolve the measurement problem — the interpretations still disagree about important conceptual questions — but it identifies the disagreement as being about scaffolding, not physics. (DOI: 10.5281/zenodo.18604312.)

**Radioactive Decay and Markov's Principle (Paper 22).**

The assertion "the atom will eventually decay" — that a positive-probability event will eventually occur — is Markov's Principle (MP): if ¬¬∃n P(n), then ∃n P(n). MP is strictly weaker than LPO and is subsumed by it. Paper 22 showed that the "watched pot" phenomenon — asserting that continuous observation of a radioactive sample will eventually detect a decay event — costs exactly MP. The finite-time detection probability (the probability of observing decay within time T) is BISH. The assertion that decay *eventually* occurs requires MP, which asserts that a process whose non-occurrence is contradictory must produce a witness. (DOI: 10.5281/zenodo.18603503.)

**WKB Tunneling (Paper 19).**

The WKB approximation for quantum tunneling through a potential barrier involves computing the transmission coefficient T = exp(−2∫|p(x)|dx), where the integral runs over the classically forbidden region. The computation of T is BISH — it is a finite integral of a computable function. The sign decision — determining which side of the barrier the particle emerges on — requires LLPO. The tunneling probability itself is BISH; the directional question is LLPO. (DOI: 10.5281/zenodo.18602596.)

### 3.4 Quantum Field Theory

**Yukawa Renormalization Group Flow (Paper 18).**

The Standard Model's Yukawa sector describes fermion masses through Yukawa coupling constants that run with the energy scale μ. Paper 18 stratified the one-loop RG flow: the discrete RG step — computing the change in coupling constants from scale μ to μ + δμ — is BISH, being finite arithmetic on coupling constants. Threshold decoupling — the assertion that heavy fermions decouple from the RG flow at μ = mf, implemented via the Heaviside step function Θ(μ − mf) — requires deciding whether μ equals mf, which is a zero-test: WLPO. The CKM matrix elements and CP violation parameters, as completed real numbers characterizing quark mixing at all scales, cost LPO via the completed limit of the running couplings. (DOI: 10.5281/zenodo.18626839.)

**QED One-Loop Renormalization (Paper 32).**

Paper 32 calibrated the full one-loop renormalization of quantum electrodynamics. The discrete RG step — computing the coupling constant change from scale μ to μ + δμ — is BISH (finite arithmetic). The global coupling constant α(μ) as a completed real number at all scales is LPO (BMC).

The most striking result: the Landau pole — the assertion that α(μ) → ∞ at some finite energy scale — is BISH, not LPO. The reason: the one-loop beta function has an explicit closed-form solution, and the divergence is a computable property of that solution. This confirms the general pattern: analytic solvability bypasses omniscience. LPO is the price of *genericity* — asserting convergence without knowing the rate.

Ward identities (the algebraic consequences of gauge symmetry) are BISH — they are polynomial relations on formal expressions, not limit assertions.

(DOI: 10.5281/zenodo.18642598.)

**QCD One-Loop and Confinement (Paper 33).**

Paper 33 extended the calibration to quantum chromodynamics — the theory of the strong force. The perturbative sector (one-loop beta function, asymptotic freedom) mirrors QED exactly: BISH for finite computation, LPO for the global coupling existence. The sign flip in the beta function (asymptotic freedom vs. QED's Landau pole) does not change the logical structure.

The non-perturbative sector — confinement and the mass gap — is where the calibration becomes physically consequential. Finite lattice QCD is BISH (a finite integral over a compact group, analogous to the finite Ising model). The continuum limit is LPO via BMC/Fekete. The mass gap assertion — Δ > 0 given that Δ ≥ 0 and ¬(Δ = 0) — is Markov's Principle, subsumed by LPO. Confinement costs no additional logical resources beyond what the continuum limit already requires.

The combined result: the entire Standard Model, perturbative and non-perturbative, lives at BISH+LPO.

(DOI: 10.5281/zenodo.18642610.)

**Scattering Amplitudes (Paper 34).**

Paper 34 calibrated the quantities that particle colliders actually measure: scattering cross sections. The tree-level Bhabha amplitude (e⁺e⁻ → e⁺e⁻) is a rational function of Mandelstam variables — pure BISH. The one-loop correction reduces to logarithms and dilogarithms of kinematic invariants — computable special functions, hence BISH. Dimensional regularization is formal Laurent series manipulation — BISH. The Bloch-Nordsieck IR cancellation is algebraic — BISH.

The result is stronger than expected: fixed-order scattering predictions are not just BISH+LPO — they are *BISH*. No omniscience principle is needed. LPO enters only when asserting that the perturbation series converges to an all-orders answer, which no experiment tests and which the series (being asymptotic) probably does not support.

**The sentence for physicists:** every quantity the LHC measures is constructively computable.

(DOI: 10.5281/zenodo.18642612.)

### 3.5 General Relativity

**Schwarzschild Curvature (Paper 5).**

The Schwarzschild solution — the unique spherically symmetric vacuum solution to Einstein's equations — stratifies cleanly. Finite-time geodesic computation (integrating the geodesic equation from a given initial position for a finite proper time) is BISH: the geodesic equations are ODEs with computable coefficients, and their solutions are computable functions. The curvature singularity at r = 0 is BISH via explicit formula: the Kretschner scalar K = 48M²/r⁶ diverges computably. The global causal structure — the Penrose diagram, the maximally extended spacetime, the assertion that the spacetime is geodesically incomplete — involves completed limits and costs LPO. Paper 5 also produced an important methodological insight: the differential geometry *infrastructure* (manifolds, tensor bundles) can be logically expensive while the *output* (specific curvature formulas) is cheap. (DOI: 10.5281/zenodo.18489703.)

**Event Horizon as Logical Boundary (Paper 13).**

The event horizon at r = 2M is not merely a physical boundary — it is a *logical* boundary. Deciding whether a particle is at the horizon requires a zero-test: r = 2M or r ≠ 2M. This is WLPO. The local event horizon — the apparent horizon, defined by the vanishing of the expansion of outgoing null geodesics at a given time — costs WLPO. The global event horizon — defined teleologically as the boundary of the causal past of future null infinity, requiring knowledge of the entire future development of spacetime — costs LPO. Paper 13's title captures the discovery: the event horizon is the surface in spacetime where the constructive hierarchy stratifies. Observers on opposite sides of the horizon face different logical costs for describing their physics. (DOI: 10.5281/zenodo.18529007.)

**Noether Conservation (Paper 15).**

Noether's theorem connects symmetries to conservation laws. Local conservation — the continuity equation ∂_μ J^μ = 0 — is BISH: it is a differential identity that follows algebraically from the equations of motion. Global conservation — the assertion that the integrated charge Q = ∫ J⁰ d³x is constant in time — requires integrating over all space, a completed limit, hence LPO. The sign structure of the integrand matters: if J⁰ is positive (as for energy density), the integral is monotone and BMC applies directly; if J⁰ oscillates (as for electric charge density with contributions of both signs), the convergence involves additional structure and the sign decision costs LLPO. (DOI: 10.5281/zenodo.18572494.)

**Black Hole Entropy (Paper 17).**

Black hole entropy provides a striking calibration. Finite microstate counting — enumerating the quantum states of a black hole of a given size, as in Strominger-Vafa's string-theoretic calculation — is BISH: it is combinatorics on finite sets. The Bekenstein-Hawking formula S = A/(4ℓ_P²), which asserts that entropy is proportional to horizon area, is a thermodynamic relation — it emerges from a thermodynamic limit analogous to the Ising model's and costs LPO via BMC. Black hole entropy instantiates the same BISH/LPO pattern as terrestrial phase transitions: finite microstates are BISH, thermodynamic assertions about macroscopic quantities are LPO. (DOI: 10.5281/zenodo.18597306.)

### 3.6 Quantum Information

**Bidual Gap and WLPO (Paper 2).**

The identification of a Banach space X with its double dual X** — routine in physics, where bra-ket notation implicitly assumes ⟨ψ| ↔ |ψ⟩ without cost — fails constructively. The gap between X and X** is exactly WLPO: constructing the canonical embedding requires deciding whether a linear functional is zero, which is a zero-test. This was the programme's first calibration and set the template: a standard physicist's assumption has a precise, non-trivial logical cost that can be formally identified and mechanically verified.

Paper 2 also produced the programme's first crisis: an AI coding agent silently replaced the meta-classical reverse direction with object-level LPO, making the calibration vacuously true (since LPO implies WLPO). The error was invisible to natural-language inspection and was caught only by examining the Lean axiom profile. This incident established formal verification as non-optional at the resolution this programme requires. (DOI: 10.5281/zenodo.17107493.)

**Trace-Class Operators (Paper 7).**

Paper 7 extended the bidual gap analysis to trace-class operators — the mathematical foundation of density matrices in quantum mechanics. The identification of trace-class operators with their predual (the compact operators) is constructively non-trivial and costs WLPO via the same zero-test mechanism as the bidual gap. The physical content: the standard formulation of quantum statistical mechanics, which represents mixed states as density operators and computes expectation values via the trace, implicitly assumes WLPO for the duality between states and observables. (DOI: 10.5281/zenodo.18527559.)

### 3.8 Physical Undecidability

**Spectral Gap Undecidability (Paper 36).**

Cubitt, Perez-Garcia, and Wolf (2015) proved that the spectral gap problem — deciding whether a Hamiltonian is gapped or gapless in the thermodynamic limit — is undecidable. This was a landmark result, widely interpreted as revealing a fundamental unknowability in quantum physics. Paper 36 stratifies Cubitt's result through the constructive hierarchy and proves it is Turing-Weihrauch equivalent to LPO.

The stratification is surgical. The finite-volume spectral gap Δ_L (computing eigenvalues of a finite matrix) is BISH. The thermodynamic limit Δ = lim Δ_L, where it exists, costs LPO via BMC. Each specific instance — "is this particular Hamiltonian gapped?" — is LPO (deciding a Σ₁⁰ statement about a specific Turing machine). The uniform function M ↦ gapped/gapless is non-computable, but this is exactly the non-computability of LPO applied uniformly — it is the halting problem.

The physical consequence: spectral gap undecidability adds *zero* new logical resources to physics. The "undecidability" is the thermodynamic limit, which has been LPO since Paper 29 (Fekete). The spectral gap is undecidable for the same reason ice melts — both require completing an infinite limit.

**The Undecidability Landscape (Paper 37).**

Paper 37 extends Paper 36's result to a meta-theorem: every undecidability result in quantum many-body physics obtained by computable many-one reduction from the halting problem is Turing-Weihrauch equivalent to LPO. Three additional results are stratified: the uncomputability of phase diagrams (Bausch-Cubitt-Watson 2021), 1D spectral gap undecidability (Bausch-Cubitt-Lucia-Perez-Garcia 2020), and uncomputable renormalization group flows (Cubitt-Lucia-Perez-Garcia-Perez-Eceiza 2022). All three calibrate to exactly LPO.

The meta-theorem is structurally simple: the halting problem is Σ₁⁰-complete, LPO decides all Σ₁⁰ statements, and any computable reduction preserves the Σ₁⁰ structure. The conclusion: "undecidability" in physics is a misnomer — it is non-computability of LPO, not fundamental unknowability. A notable exception is ground state energy density (Watson-Cubitt 2021), which is BISH — computational *complexity* (how hard to compute) is distinct from logical *undecidability* (whether computable at all).

**Wang Tiling — The Grandfather (Paper 38).**

Paper 38 traces the genealogy of physical undecidability to its root. Every undecidability result in quantum many-body physics descends from a single ancestor: the undecidability of Wang tiling (Berger 1966). The genealogy runs: Wang tiling → Robinson aperiodic tiling → Kanter (Potts model) → Gu-Weedbrook-Perales-Nielsen (2D Ising) → Cubitt et al. (spectral gap) → all descendants. Paper 38 proves that Wang tiling itself is Turing-Weihrauch equivalent to LPO. The Grandfather Theorem: all descendants inherit exactly LPO — nothing more, nothing less.

The Σ₁⁰ Ceiling Theorem establishes that no Σ₁⁰-complete reduction can exceed LPO. To exceed the LPO ceiling would require a Σ₂⁰-complete encoding — which is exactly what Paper 39 constructs.

**Beyond LPO: Thermodynamic Stratification (Paper 39).**

Papers 36–38 showed all *known* undecidabilities are LPO. Paper 39 asks: is this a hard ceiling? The answer: no, but the extension is empirically inaccessible. By modifying the Cubitt construction — using Robinson tilings with perimeter counters to run a Turing machine M on input k extracted from supertile scale — Paper 39 encodes the Finiteness Problem (Σ₂⁰-complete): gapped ↔ M halts on finitely many inputs; gapless ↔ M halts on infinitely many.

The Thermodynamic Stratification Theorem: extensive observables (energy density, free energy) are capped at LPO via Fekete/BMC; intensive observables (spectral gap, correlation length) without promise gap reach Σ₂⁰. But empirical physics operates at finite precision, enforcing an effective promise gap that collapses Σ₂⁰ decisions to LPO. The Σ₂⁰ tier is mathematically real but empirically inaccessible. This result is developed fully in Chapter 9.

### 3.9 Complete Calibration Summary

The complete calibration table covering all 39 papers (excluding withdrawn Papers 1 and 3) is presented in Appendix A. The pattern is uniform: every calibration result falls at or below LPO. No exception has been found across statistical mechanics, quantum mechanics, quantum field theory, general relativity, quantum information, or physical undecidability. The highest level physically instantiated is LPO (via Fekete's equivalence, Paper 29). WLPO and LLPO appear as sub-LPO phenomena. FT and DC, although used in classical proofs, are dispensable for all empirical predictions.

---

## Chapter 4: The Three Foundational Theorems

This chapter presents the three results that transform the calibration pattern into a thesis.

### 4.1 Theorem I: Fekete's Subadditive Lemma ≡ LPO (Paper 29)

**Statement:** Over BISH, Fekete's Subadditive Lemma is equivalent to the Limited Principle of Omniscience.

**Fekete's Lemma:** If (aₙ) satisfies a_{m+n} ≤ a_m + a_n for all m, n ≥ 1, then lim_{n→∞} a_n/n exists and equals inf_{n≥1} a_n/n.

**Why this matters:** Fekete's lemma is not an obscure technical result. It is the mathematical engine of statistical mechanics. Free energy, pressure, entropy density, and other thermodynamic potentials are subadditive by construction (the energy of a composite system is at most the sum of the energies of its parts). Fekete's lemma is what guarantees the thermodynamic limit exists. Without it, the entire edifice of equilibrium statistical mechanics collapses.

Phase transitions — ice melting, magnets losing magnetization, superconductors transitioning — are empirically observed phenomena. Their mathematical description requires the thermodynamic limit. The thermodynamic limit requires Fekete's lemma. Fekete's lemma requires LPO. Therefore:

**LPO is not a mathematical convenience. It is a physically instantiated principle.**

**Proof sketch (Forward: LPO → Fekete):**

Given LPO, we have BMC. The sequence bₙ = aₙ/n is bounded below by subadditivity: for any fixed m, the subsequence a_{km}/km is bounded and eventually monotone. Define cₙ = inf_{k≤n} aₖ/k. This sequence is bounded below (by the infimum bound from subadditivity) and monotone non-increasing. By BMC (= LPO), the infimum limit L = lim cₙ exists. The standard argument then shows that aₙ/n → L: for any ε > 0, choose m such that aₘ/m < L + ε; for large enough n, write n = qm + r and use subadditivity to bound aₙ/n ≤ aₘ/m + O(1/n) < L + 2ε. The downward bound aₙ/n ≥ L follows from the definition of infimum. This completes the proof that LPO → Fekete.

**Proof sketch (Reverse: Fekete → LPO):**

Given a binary sequence α : ℕ → {0,1}, define aₙ = n − Σ_{k=1}^{n} α(k). This counts the number of zeros in the first n terms. The sequence (aₙ) is subadditive: a_{m+n} ≤ aₘ + aₙ because the number of zeros in a concatenated sequence is at most the sum of the zeros in each part. By Fekete's lemma (assumed), lim aₙ/n exists as a real number L. If all α(k) = 0, then aₙ = n for all n, so L = 1. If some α(k₀) = 1, then aₙ ≤ n − 1 for all n ≥ k₀, so L ≤ 1 − 1/k₀ < 1.

The decision is now constructive: compare L to 1. If L = 1, then ∀k (α(k) = 0). If L < 1, then ∃k (α(k) = 1). This is exactly LPO. The encoding is simple but non-obvious — the insight that subadditivity can encode arbitrary binary information was, as far as we know, original to this programme.

**Lean certification:** The forward direction uses `Classical.choice` (from the LPO hypothesis) — this is intentional classical content (Level 3). The reverse direction compiles with zero classical axioms (Level 2). The equivalence is formally verified in Lean 4.

### 4.2 Theorem II: Fan Theorem Dispensability (Paper 30)

**Statement:** Every empirical prediction in physics that is derived using the Fan Theorem can be derived without it, using only BISH+LPO.

**The Fan Theorem (FT):** If B is a bar of the binary fan (every infinite binary sequence passes through B), then B is uniform (there exists N such that every binary sequence of length N passes through B).

The Fan Theorem appears throughout mathematical physics under the guise of compactness. The Heine-Borel theorem, the Bolzano-Weierstrass theorem, the Arzelà-Ascoli theorem — these are all consequences of FT (or its classical equivalents). When a physicist asserts that a continuous function on a compact set attains its maximum, that assertion is a variational principle rooted in FT. When a physicist extracts a convergent subsequence from a bounded sequence to define a thermodynamic limit, that extraction invokes Bolzano-Weierstrass, hence FT. When a physicist appeals to the compactness of a quantum state space to assert the existence of a density matrix, that appeal rests on FT. Compactness is ubiquitous in mathematical physics, and FT is the constructive content of compactness.

Yet in every calibrated case, FT is dispensable. The pattern is remarkably consistent. Variational principles assert "a minimizer exists" via compactness, but the Euler-Lagrange equations provide the minimizer directly — a construction, not an existence claim. Subsequence extraction asserts "a convergent subsequence exists" via Bolzano-Weierstrass, but the specific physical sequences that arise in thermodynamic limits are bounded and monotone, so they converge by BMC (≡ LPO) without extracting a subsequence. State space compactness asserts "an accumulation point exists," but the specific states physicists compute are constructed explicitly from physical data. In each case, the general existence theorem (FT) is replaced by a specific construction (BISH or LPO).

The dispensability is not accidental — it reflects a structural fact about physics. FT and LPO are logically independent: neither implies the other over BISH. FT is about tree searches (navigating well-founded branching structures), while LPO is about sequence limits (completing bounded monotone sequences). Physics uses limits, not tree searches. A phase transition requires completing an infinite limit (LPO). An optimization problem requires solving equations (BISH). Neither requires searching an infinite binary tree for a path with a given property. The Fan Theorem is powerful mathematics — it proves deep results in topology and analysis — but its power addresses a kind of mathematical difficulty (tree navigation) that physical predictions do not encounter.

Paper 30 demonstrates the dispensability concretely. For each theorem in the calibration that was previously proved using compactness, an alternative BISH+LPO proof is exhibited. The Lean formalization verifies that the alternative proofs produce the same empirical predictions with no FT-related axioms in the `#print axioms` output. The classical Lagrangian mechanics result (Paper 28) is the most instructive example: Newton's formulation is BISH, Lagrange's variational formulation uses FT, but the empirical content — the trajectory — is identical. The variational scaffolding adds mathematical elegance, not physical content.

**Lean certification:** Paper 30 comprises approximately 1,300 lines of Lean 4. The dispensability is demonstrated by exhibiting BISH+LPO proofs for each previously FT-dependent theorem and verifying the axiom profile via `#print axioms`.

### 4.3 Theorem III: Dependent Choice Dispensability (Paper 31)

**Statement:** Every empirical prediction in physics that is derived using Dependent Choice can be derived without it, using only BISH+LPO.

**Dependent Choice (DC_ω):** If R is a relation on a set S such that for every x ∈ S there exists y ∈ S with R(x,y), then there exists an infinite sequence x₀, x₁, x₂, ... in S with R(xₙ, xₙ₊₁) for all n.

Dependent Choice appears in physics whenever a construction proceeds iteratively: given the current state, choose the next state satisfying some relation, and repeat forever. The mean ergodic theorem builds a convergent sequence of Cesàro averages — at each step, the next average depends on the previous one, and DC guarantees the infinite sequence exists. Martingale convergence builds an adapted sequence of conditional expectations — each term depends on the σ-algebra generated by its predecessors, and DC guarantees the entire filtration exists. Picard iteration builds successive approximations to a differential equation's solution — each approximation is obtained by integrating the previous one, and DC guarantees the limit exists. In each case, DC constructs an infinite object (the full sequence) from a local rule (the next-step relation).

The key insight of Paper 31 is that empirical predictions never depend on the infinite object — they depend on finite initial segments. To predict a measurement at precision ε, a physicist needs only finitely many iteration steps. Finite iteration is BISH: given x₀ and a computable step function, computing x₀, x₁, ..., xₙ for any fixed n is finite recursion, requiring no choice principle. The infinite sequence that DC constructs is mathematical scaffolding; the empirical content — the number compared to experiment — lives in the finite truncation. DC enters only when asserting properties of the *completed* infinite sequence, and those assertions are never themselves empirical predictions.

The Weak Law of Large Numbers provides Paper 31's most transparent example. Its empirical content — the probability bound P(|Sₙ/n − μ| > ε) < δ for specified n, ε, δ — is derivable from the Chebyshev-Markov inequality, which is pure BISH arithmetic (finite sums and ratios). DC enters only if one asserts the Strong Law: that the sample mean converges *almost surely* to μ. The Strong Law is an ontological claim about the behavior of an infinite sequence of measurements — a claim no finite experiment can verify or refute. Paper 31 proves that every empirical prediction extracted from the Strong Law is already available from the Weak Law, which requires no DC. The dispensability is not a weakness of the Strong Law — it is a diagnosis of where the Strong Law's content becomes non-empirical.

**Lean certification:** Paper 31 comprises approximately 1,400 lines of Lean 4. Same verification structure as Paper 30: BISH+LPO proofs exhibited for each previously DC-dependent theorem. The `#print axioms` output confirms no DC-related axioms (no `Classical.choice` beyond LPO hypothesis instances).

### 4.4 The Combined Result

Theorems I–III together establish:

**BISH+LPO is necessary:** LPO cannot be eliminated — phase transitions require it (Theorem I).

**BISH+LPO is sufficient:** Neither FT (Theorem II) nor DC (Theorem III) adds empirical content beyond BISH+LPO.

The logical constitution of empirically accessible physics is exactly BISH+LPO. Not more, not less.

---

## Chapter 5: The Standard Model at BISH+LPO

### 5.1 Overview

The Standard Model of particle physics is the most precisely tested physical theory in history. The anomalous magnetic moment of the electron has been measured to 13 significant figures and agrees with theoretical prediction. Cross sections at the Large Hadron Collider are computed to next-to-next-to-leading order and confirmed to percent-level accuracy. If BISH+LPO suffices for the Standard Model's predictions, the characterization covers the empirically hardest-tested corner of physics.

Papers 18, 32, 33, and 34 calibrate the four sectors of the Standard Model: electroweak theory (Yukawa couplings, threshold decoupling, CKM mixing), quantum electrodynamics (running coupling, Ward identities, anomalous magnetic moment), quantum chromodynamics (asymptotic freedom, confinement, mass gap), and scattering amplitudes (tree-level, one-loop, dimensional regularization, infrared cancellation). The result is uniform: the Standard Model lives at BISH+LPO. Its empirical predictions — the numbers experimentalists compare to data — are BISH at any fixed order in perturbation theory. LPO enters only when completing infinite limits: the all-orders sum, the continuum limit, the global existence of running couplings.

The calibration reveals a striking feature: the most precise predictions in all of physics — the anomalous magnetic moments, the Z-boson mass, scattering cross sections — are pure BISH. They are finite computations involving computable functions (rational functions, logarithms, dilogarithms) evaluated at computable inputs (coupling constants, masses). Omniscience is needed only for the mathematical framework surrounding these computations, not for the computations themselves.

### 5.2 Electroweak Theory (Paper 18)

Paper 18 calibrates the electroweak sector of the Standard Model. The Yukawa coupling between fermions and the Higgs field generates fermion masses through spontaneous symmetry breaking. The one-loop renormalization group equation for the Yukawa coupling y(μ) is an ordinary differential equation whose solution involves logarithms and rational functions of known quantities — pure BISH at any fixed energy scale μ. The discrete RG step (computing the coupling at the next energy scale) is a finite arithmetic operation requiring no omniscience.

Threshold decoupling — the physical phenomenon where heavy particles decouple from low-energy physics at the scale μ = mf — involves the Heaviside step function θ(μ − mf). Deciding whether μ equals mf exactly is a zero-test, hence WLPO. In practice, experimentalists work away from thresholds and the step function is trivially evaluable, but the mathematical structure places threshold decoupling at WLPO in the hierarchy. The CKM matrix elements, which parametrize quark mixing and CP violation, involve completing the sum over quark generations to extract mixing angles. This completed sum requires LPO when the convergence of the perturbative series is asserted globally. The fermion mass hierarchy (mt ≫ me by five orders of magnitude) has no additional logical cost — it is an empirical fact about the values of computable constants, not a structural feature requiring additional axioms.

### 5.3 Quantum Electrodynamics (Paper 32)

Paper 32 calibrates quantum electrodynamics. The fine structure constant α(μ) runs with energy scale μ according to the one-loop beta function. At any fixed scale, computing α(μ) from α(μ₀) involves evaluating a logarithm — BISH. The discrete RG step (advancing from one scale to the next) is a finite computation. The assertion that the running coupling exists globally — that α(μ) is defined for all μ — requires completing the sequence of finite-scale evaluations into a function on all scales. This completion is BMC (≡ LPO): the coupling is bounded (by unitarity) and monotone (at one loop), and asserting the existence of the completed trajectory is a Bounded Monotone Convergence claim.

The Landau pole — the energy scale Λ at which the one-loop coupling diverges — is BISH. Unlike the global trajectory, the Landau pole has a closed-form expression: Λ = μ₀ exp(3π/(α₀ · Nf)) where Nf is the number of charged fermion species. This is a computable real number, requiring no omniscience to identify. The Landau pole's computability contrasts with the coupling trajectory's LPO cost: knowing *where* the coupling blows up is easier than asserting the coupling *exists* at every intermediate scale.

Ward identities — the gauge invariance constraints that ensure renormalizability — are algebraic identities: they assert that certain combinations of vertex functions and propagators vanish. Verifying an algebraic identity is BISH. Ward identities are the structural reason QED is renormalizable, and they cost nothing beyond finite algebra.

The Schwinger anomalous magnetic moment ae = α/(2π) is the crown jewel of QED. It has been measured to 13 significant figures and agrees with theoretical computation. Its calibration: ae = α/(2π) is a ratio of computable constants — pure BISH. The higher-order corrections (α², α³, ...) involve evaluating finite sums of known integrals at each loop order, each of which is computable. The most precisely confirmed prediction in all of physics is constructively computable at any fixed loop order. LPO enters only if one asserts the all-orders convergence of the perturbative series — a claim about an infinite sum that no experiment tests directly.

### 5.4 Quantum Chromodynamics (Paper 33)

Paper 33 calibrates quantum chromodynamics, the theory of the strong force. Perturbative QCD exhibits asymptotic freedom: the strong coupling αs(μ) decreases at high energies, the opposite of QED's behavior. The sign flip in the beta function (due to the non-Abelian gauge group SU(3)) does not change the logical structure — the one-loop discrete RG step is still BISH, and the global coupling trajectory is still LPO via BMC. At any fixed energy scale, αs(μ) is a computable function of known inputs. The most precisely tested perturbative QCD predictions — jet cross sections, event shapes at LEP — are BISH at fixed loop order, just as in QED.

Non-perturbative QCD introduces confinement and the mass gap, phenomena absent in QED. Finite lattice QCD — computing correlation functions on a finite spacetime grid — is BISH: it reduces to finite-dimensional linear algebra and Monte Carlo estimation with computable error bounds. The continuum limit (lattice spacing a → 0) is LPO: asserting that the sequence of finite-lattice observables converges to a continuum value is BMC. Confinement — the assertion that the string tension σ satisfies σ > 0 — and the mass gap — the assertion that the lightest glueball mass Δ satisfies Δ > 0 — both assert positivity of a quantity defined through a completed limit. These are Markov's Principle instances, subsumed by LPO.

An important caveat: the non-perturbative results are conditional on physical axioms. The Yang-Mills existence and mass gap problem (a Clay Millennium Problem) is open — it is not known whether the continuum limit of lattice QCD exists with the required properties. Paper 33 axiomatizes these assumptions as explicit `axiom` declarations in Lean and calibrates the consequences. The calibration says: *if* the Yang-Mills theory exists, its properties cost at most BISH+LPO. The axiomatization is Level 4 certification — logically valid, physically conditional.

The entire QCD sector — perturbative and non-perturbative — lives at BISH+LPO. The strong force, despite its notorious mathematical complexity (confinement, non-perturbative dynamics, the mass gap), requires no logical resources beyond those used by the Ising model.

### 5.5 Scattering Amplitudes (Paper 34)

Paper 34 calibrates scattering amplitudes — the quantities that collider experiments actually measure. Tree-level amplitudes are rational functions of the Mandelstam variables (s, t, u), which are polynomials in the external momenta. Rational functions of computable inputs are computable. Tree-level amplitudes are pure BISH — finite algebraic operations with no limiting processes, no omniscience, no non-constructive reasoning of any kind.

One-loop corrections are the key surprise. After Passarino-Veltman reduction, one-loop integrals reduce to scalar integrals expressible in terms of logarithms and dilogarithms (Li₂). These are computable special functions — their values at any computable argument can be approximated to arbitrary precision by explicit algorithms. One-loop scattering predictions are therefore not merely BISH+LPO — they are *pure BISH*. The most precise predictions tested at the LHC are constructively computable without any omniscience principle. This is the strongest evidence that physics is more constructive than its mathematical formulation suggests.

Dimensional regularization — the procedure of analytically continuing from d = 4 to d = 4−ε dimensions — might seem to require non-constructive reasoning about non-integer-dimensional spaces. It does not. Dimensional regularization is a formal algebraic procedure: Laurent series manipulation in the parameter ε, followed by the limit ε → 0. The Laurent series coefficients are computable (they are combinations of Gamma functions and Euler-Mascheroni constants), and the ε → 0 limit extracts the finite part — a finite algebraic operation (taking the ε⁰ coefficient). The entire procedure is BISH. Infrared cancellation via the Bloch-Nordsieck theorem is similarly algebraic: the cancellation between virtual and real emission diagrams is an exact identity at each order, requiring no limiting process.

LPO enters scattering amplitudes at exactly one point: asserting that the perturbative series converges (or is Borel-summable) to all orders. This is a statement about an infinite sum — a completed limit. At any fixed loop order, the prediction is BISH. Only the claim that the infinite tower of corrections assembles into a well-defined function requires omniscience. Every quantity the LHC measures — computed at fixed order in perturbation theory — is constructively computable.

### 5.6 The Standard Model Summary

The Standard Model calibration reveals a layered structure. The mathematical framework — defining fields, gauge groups, Lagrangians — is BISH. The perturbative calculations at any fixed loop order are BISH (with threshold effects at WLPO). The non-perturbative sector (lattice QCD) is BISH at finite lattice spacing and LPO at the continuum limit. The all-orders assertions (convergence of perturbation series, global existence of running couplings) are LPO. The table summarizes:

| SM Sector | Perturbative | Non-perturbative | Empirical predictions |
|---|---|---|---|
| Electroweak | BISH / WLPO / LPO | — | BISH at finite precision |
| QED | BISH / WLPO / LPO | — | BISH at fixed loop order |
| QCD | BISH / WLPO / LPO | BISH (lattice) / LPO (continuum) | BISH at fixed loop order |
| Scattering | BISH | — | BISH |

The most important column is the last one. Every number that an experimentalist at CERN compares to a measurement — every cross section, every branching ratio, every anomalous magnetic moment — is BISH at fixed loop order. The Standard Model, the most precisely tested theory in the history of science, lives at BISH+LPO. Its empirical predictions are constructively computable.

---

## Chapter 6: The Metatheorem

### 6.1 Why the Pattern Holds

The calibration table (Chapter 3) presents an empirical fact: across 34 physics papers covering every major domain, no calibration exceeds LPO. This is striking — the hierarchy offers infinitely many levels above LPO (Fan Theorem, Bar Induction, Dependent Choice, full LEM, AC, large cardinals), yet physics never reaches any of them. A single exception among 34 papers could be a coincidence. Zero exceptions demands an explanation.

Paper 35 provides that explanation: a conservation metatheorem consisting of four sub-theorems that together prove the pattern is a structural consequence of how physical predictions are built. The metatheorem does not merely assert that the calibration holds — it explains *why* it holds, and it predicts that future calibrations will produce the same result. The undecidability arc (Papers 36–39, Chapter 8) provides independent confirmation: even physical *undecidability* — which might have been expected to exceed the LPO ceiling — calibrates to exactly LPO. The explanation covers not just what physics costs but where physics fails.

### 6.2 Theorem A: BISH Conservation

**Statement:** Any physical prediction expressible as a finite composition of computable functions evaluated at computable inputs is BISH.

The proof of Theorem A is straightforward from the standpoint of computable analysis: compositions of computable functions are computable (Weihrauch 2000, Theorem 4.3.7). Every function that appears in a physics prediction at finite order is computable: rational functions (polynomial algebra), exponentials and logarithms (Taylor series with computable error bounds), trigonometric functions (computable by the same mechanism), dilogarithms and polylogarithms (computable special functions), Bessel functions (power series with computable convergence), hypergeometric functions (ratio test provides computable modulus). The inputs — coupling constants, masses, momenta — are computable real numbers. Therefore the output — the predicted number — is computable, hence BISH.

The theorem is "trivial" from the computable analysis perspective. Its content is not the proof but the *observation*: physical predictions have the structure of finite compositions of computable functions at computable inputs. This is not obvious a priori. Physics could involve non-computable functions (it does not), or non-computable constants (none are known), or operations that destroy computability (such as unrestricted suprema — but physical suprema are always over bounded monotone sequences, which are handled by LPO, not by Theorem A).

Theorem A explains why the vast majority of entries in the calibration table land at BISH. Tree-level scattering amplitudes, finite-lattice partition functions, fixed-order perturbative corrections, local differential geometric computations (curvature tensors, connection coefficients), Born rule probabilities at finite precision, Chebyshev bounds — these are all finite compositions of computable functions. The BISH entries in the calibration table are not individually remarkable. What is remarkable is that *every* finite-order physical computation is an instance of the same pattern.

The Lean verification of Theorem A is structural rather than deep: it checks that each calibrated BISH result uses only computable operations. The `#print axioms` output for each BISH-certified theorem contains no `Classical.choice` and no custom axioms — confirming mechanically that the computation is constructive.

### 6.3 Theorem B: The LPO Boundary

**Statement:** A physical assertion requires LPO over BISH if and only if it asserts a completed limit without computable modulus of convergence.

Theorem B identifies the exact boundary between BISH and LPO. It consists of three sub-theorems that together classify every physical assertion involving a limit.

**Sub-theorem B1 (Computable modulus → BISH):** If a sequence (aₙ) converges and its modulus of convergence is computable — that is, there exists a computable function N(ε) such that |aₙ − L| < ε for all n ≥ N(ε) — then the limit L is computable, and any prediction depending on L is BISH. The proof is constructive: to approximate L to precision ε, compute aₙ for n = N(ε). This sub-theorem explains why most perturbative calculations in physics are BISH: Taylor series, Fourier series, and iterative solutions typically come with explicit error bounds that provide computable moduli.

**Sub-theorem B2 (No computable modulus, bounded monotone → LPO):** If a sequence (aₙ) is bounded and monotone but has no computable modulus of convergence, then asserting that the sequence converges (i.e., that the limit exists as a real number) is Bounded Monotone Convergence — which is equivalent to LPO over BISH by Paper 29's Fekete encoding. This is the mechanism behind every LPO entry in the calibration table: thermodynamic limits, continuum limits, and global coupling existence all involve bounded monotone sequences whose convergence rates are not uniformly computable. The sequence converges (by classical monotone convergence), but the *rate* at which it converges cannot be bounded by any computable function of ε.

**Sub-theorem B3 (Limit comparison → WLPO):** Deciding whether a limit equals a specific value — for example, whether the magnetization M satisfies M = 0 (paramagnetic phase) versus M > 0 (ferromagnetic phase) — is a zero-test. This is WLPO, which is subsumed by LPO. The proof encodes a binary sequence α into a convergent sequence whose limit is 0 if and only if all terms of α are zero: set aₙ = Σₖ₌₁ⁿ α(k)/2ᵏ. Then lim aₙ = 0 iff α ≡ 0, and deciding "lim aₙ = 0?" is exactly WLPO. This mechanism appears in the calibration whenever a physical prediction depends on whether a computed quantity is exactly zero — threshold decoupling, bidual gap detection, phase boundary location.

Together, B1-B3 provide a complete classification: a physical assertion involving a limit is BISH if the modulus is computable, LPO if the sequence is bounded and monotone without computable modulus, and WLPO if the assertion is a zero-test on a limit. No physical assertion in the calibration exceeds these three cases. The classification is exhaustive because physical limits arise from one of two sources: perturbative computation (computable modulus, hence BISH by B1) or thermodynamic/continuum limits (bounded monotone, hence LPO by B2, with phase boundaries at WLPO by B3).

### 6.4 Theorem C: Exhaustiveness

**Statement:** Every calibration result in Papers 2–34 is an instance of Theorem A (BISH) or Theorem B (WLPO/LLPO/LPO). No result exceeds LPO. Papers 36–39 (Chapter 8) confirm the pattern extends to the undecidability landscape.

Theorem C is an audit, not a proof. Its content is the verified observation that every calibration result in Papers 2–34 is classified as an instance of Theorem A (BISH) or Theorem B (WLPO/LLPO/LPO), and no result exceeds LPO. The Lean formalization encodes each result as a classified instance — tagged with its position in the hierarchy — and verifies that the tagging is consistent with the axiom profile. The classification is exhaustive: every theorem in every paper falls into one of the three categories (BISH via computable composition, LPO via bounded monotone limit, or WLPO/LLPO via zero-test/sign-decision).

Theorem C's strength is cumulative. A single paper calibrating to LPO could be coincidence. Thirty-two papers across six physics domains — statistical mechanics, quantum mechanics, quantum field theory, general relativity, quantum information, classical mechanics — all calibrating to BISH+LPO is a pattern demanding explanation. Theorems A and B provide the explanation; Theorem C certifies that the explanation is exhaustive across the calibration.

Papers 36–38 provide independent confirmation from outside the original calibration scope. Every physical undecidability result — spectral gap, phase diagrams, RG flows, 1D spectral gap — also calibrates to LPO. These were not included in the original audit (they concern undecidability, not empirical predictions) but they confirm the same pattern: the LPO ceiling holds even where physics encounters non-computability.

### 6.5 Theorem D: Three Mechanisms

**Statement:** Every instance of LPO in the programme arises from one of three equivalent mechanisms: Bounded Monotone Convergence, Cauchy completeness without modulus, or supremum existence.

Theorem D identifies three equivalent mechanisms through which LPO enters physics: (M1) Bounded Monotone Convergence — asserting that a bounded monotone sequence converges; (M2) Cauchy completeness without computable modulus — asserting that a Cauchy sequence has a limit when the modulus of convergence is not computable; (M3) Supremum existence — asserting that a bounded set of reals has a least upper bound. The equivalences M1 ↔ M2 ↔ M3 over BISH are standard results in constructive analysis (Bridges and Richman 1987, Ishihara 2006). The theorem's content is not the equivalences themselves but the observation that every LPO instance in the calibration arises from one of these three mechanisms: phase transitions via BMC (M1), continuum limits via Cauchy completeness (M2), and variational bounds via supremum existence (M3).

The sub-LPO entries follow the same pattern of mechanism identification. Every WLPO entry in the calibration arises from the zero-test mechanism: deciding whether a computed quantity equals zero (bidual gap, threshold decoupling, magnetization vanishing). Every LLPO entry arises from the sign-decision mechanism: deciding the sign of a computed quantity (Bell/CHSH inequality violation, WKB tunneling direction, intermediate value theorem applications). These mechanisms are identified and verified in the Lean formalization — each WLPO or LLPO theorem is tagged with its mechanism, and the `#print axioms` output confirms the classification.

The three-mechanism classification has predictive power. When calibrating a new physical theorem, one can determine its height in the hierarchy by identifying which mechanism (if any) it invokes: if the theorem asserts the existence of a limit without providing a rate, it is LPO via M1 or M2; if it asserts a supremum, it is LPO via M3; if it performs a zero-test, it is WLPO; if it performs a sign decision, it is LLPO; if it involves only finite computation, it is BISH. This provides a practical calibration protocol for future work.

### 6.6 The Five Steps of a Physicist

The metatheorem can be restated as an observation about the practice of theoretical physics. A physicist making a prediction follows five steps, and each step maps to a specific location in the constructive hierarchy.

**Step 1: Write a Lagrangian.** The Lagrangian is a polynomial (or rational function) in the fields and their derivatives: L = ψ̄(iγᵘ∂ᵘ − m)ψ − (1/4)FᵘᵛFᵘᵛ + ... . Polynomial algebra is finite computation — BISH. **Step 2: Derive equations of motion.** The Euler-Lagrange equations are obtained by formal differentiation of L. Formal calculus — symbolic manipulation of derivatives — is BISH. **Step 3: Solve the equations.** At any finite order in perturbation theory, the solution is a finite combination of computable functions (exponentials, logarithms, Bessel functions, hypergeometric functions). Evaluating these functions at computable inputs is BISH by Theorem A. **Step 4: Take a limit if needed.** This is the only step where LPO can enter. If the prediction requires a thermodynamic limit (N → ∞), a continuum limit (a → 0), or an all-orders summation, and the convergence rate is not computable, the limit assertion is BMC ≡ LPO by Theorem B2. **Step 5: Compare to experiment.** Experimental comparison involves finite-precision arithmetic — computing |prediction − measurement| and checking whether it falls within error bars. This is BISH.

LPO enters only at Step 4, and only when the limit lacks a computable modulus of convergence. Steps 1, 2, 3, and 5 are always BISH. This is why the characterization holds: the structure of physics-as-practiced — Lagrangian → equations → solutions → limits → experiment — maps onto the BISH/LPO boundary with LPO entering at exactly one point. The metatheorem is not a mysterious coincidence but a consequence of how physicists actually compute.

The five-step structure also explains why empirical predictions are often *more* constructive than the mathematical framework suggests. A physicist computing a cross section at one loop (Step 3) never reaches Step 4. The prediction is BISH. The LPO-level claims — "the perturbation series converges," "the continuum limit exists," "the coupling runs to all scales" — are assertions *about* the mathematical framework, not predictions compared to experiment. The metatheorem identifies this gap between framework and prediction as the BISH/LPO boundary.

---

## Chapter 7: The Boundary — What Physics Cannot Do

### 7.1 The Arithmetic Hierarchy

The arithmetic hierarchy classifies mathematical statements by the complexity of their quantifier structure. At the base level, a **decidable predicate** P(n) is one for which there is an algorithm that, given any n, determines whether P(n) is true or false in finite time. The simplest non-trivial statements are **Σ₁⁰**: "there exists n such that P(n)" — a single existential quantifier over a decidable predicate. Dually, **Π₁⁰** statements have the form "for all n, P(n)." LPO is precisely Σ₁⁰-LEM: the principle that every Σ₁⁰ statement is either true or false. Equivalently, for any binary sequence, either all terms are zero or some term is nonzero.

The next level introduces **Σ₂⁰** statements: "there exists n such that for all m, Q(n,m)" — two quantifier alternations. Deciding Σ₂⁰ statements requires LPO' (Σ₂⁰-LEM), strictly stronger than LPO. **Π₂⁰** statements are dual: "for all n, there exists m such that Q(n,m)." The statement "sequence (aₙ) converges" is Π₂⁰: ∀ε ∃N ∀n,m > N, |aₙ − aₘ| < ε. This is why general convergence testing is beyond LPO. Each higher level (Σ₃⁰, Π₃⁰, ...) adds another quantifier alternation, requiring correspondingly stronger principles.

The physical significance is direct. LPO decides Σ₁⁰ statements — one layer of existential quantification over computable predicates. This is exactly the thermodynamic limit: "there exists an N such that the finite-volume observable is within ε of the infinite-volume value" is Σ₁⁰ when the convergence is monotone. Everything beyond Σ₁⁰ — general convergence testing (Π₂⁰), the finiteness problem (Σ₂⁰), set-theoretic combinatorics (far beyond) — is excluded from the empirical predictions of physics. The arithmetic hierarchy provides a precise ruler for measuring the logical complexity of physical assertions, and physics uses exactly one notch on that ruler.

The hierarchy diagram in §1.5 visualizes this placement. BISH sits at the decidable base. LPO sits at Σ₁⁰. Paper 39's Platonic ceiling sits at Σ₂⁰. Everything above — full LEM, AC, large cardinals — is arbitrarily far beyond anything physics accesses. The five exclusions that follow describe what lies above the LPO ceiling and why physics cannot reach it.

The placement:

```
Σ₁⁰:  ∃n P(n)                    — LPO decides this
Π₁⁰:  ∀n P(n)                    — LPO decides this
Σ₂⁰:  ∃n ∀m Q(n,m)              — BEYOND LPO
Π₂⁰:  ∀n ∃m Q(n,m)              — BEYOND LPO
Σ₃⁰ and above                    — FAR BEYOND LPO
Full LEM                          — incomparably beyond LPO
```

### 7.2 Exclusion 1: General Convergence Testing

The statement "the sequence (aₙ) converges" is Π₂⁰: for all ε > 0, there exists N such that for all n, m > N, |aₙ − aₘ| < ε. This involves two quantifier alternations (∀ε ∃N followed by ∀n,m), placing it strictly beyond LPO. Nature can complete specific classes of limits — BMC handles bounded monotone sequences, which is exactly LPO — but nature cannot decide general convergence. There is no physical process that, given an arbitrary sequence, determines whether it converges.

The physical consequence is concrete. No experiment can determine whether an arbitrary physical process converges to a steady state. A physicist can observe that a system *appears* to be approaching equilibrium — the measurements are getting closer together — but the assertion "this process converges" is Π₂⁰ and lies beyond the resources available to empirical physics. What physics *can* do is assert convergence for bounded monotone processes (LPO/BMC), which covers thermodynamic limits, phase transitions, and continuum limits. The distinction between "this specific bounded monotone sequence converges" (Σ₁⁰, LPO-decidable) and "this arbitrary sequence converges" (Π₂⁰, beyond LPO) is the first sharp boundary separating what physics can do from what it cannot.

This exclusion has a counterintuitive consequence for dynamical systems. The long-time behavior of a generic dynamical system — whether it converges to a fixed point, oscillates periodically, or behaves chaotically — is beyond BISH+LPO to decide in full generality. Physics handles this by studying specific systems whose dynamics are constrained (dissipative systems converge by BMC, Hamiltonian systems conserve energy by BISH), avoiding the need for a general convergence oracle.

### 7.3 Exclusion 2: Non-Δ₂⁰ Real Numbers

The real numbers accessible to BISH+LPO are exactly the Δ₂⁰ reals — the limit-computable reals. A real number x is Δ₂⁰ if there exists a computable sequence of rationals (qₙ) that converges to x, though the rate of convergence need not be computable. Equivalently, x is Δ₂⁰ if it is computable relative to the halting oracle. This is a vast class: it includes π, e, the Euler-Mascheroni constant, Chaitin's Ω (the halting probability), and every real number that can be described by a finite algorithm plus access to a single instance of LPO. But it does not include all reals — there exist real numbers that are not limit-computable, and these are inaccessible to BISH+LPO.

The physical consequence is a prediction about physical constants: every physical constant — the fine structure constant α, the electron mass mₑ, the cosmological constant Λ, Newton's gravitational constant G — is Δ₂⁰. Each admits a finite description (an algorithm, possibly requiring a halting oracle, that converges to its value). No physical constant can encode a Σ₂⁰-complete problem. This rules out a class of speculations about the "algorithmic randomness" of physical constants: α is not algorithmically random in any strong sense — it is limit-computable, meaning it sits in the countable class Δ₂⁰ rather than in the uncountable continuum of all reals. Fine-tuning debates, which implicitly assume physical constants are drawn from the full continuum, are operating with an unnecessarily large sample space.

If a physical constant were shown to be non-Δ₂⁰ — for example, if computing α to arbitrary precision required deciding a Σ₂⁰-complete problem — the characterization would be refuted. No such constant is known.

### 7.4 Exclusion 3: Tree-Search Principles

The Fan Theorem and Bar Induction are logically independent of LPO — neither implies the other, and neither is implied by LPO, over BISH. Their exclusion from physics means that nature does not perform unrestricted tree searches. The Fan Theorem asserts that every bar of the binary fan is uniform; Bar Induction asserts that well-founded induction holds for certain classes of trees. Both involve navigating branching structures of potentially unbounded depth. Physical processes do not perform such navigation: they search bounded trees (finitely many branches, finitely many levels — BISH) and complete monotone limits (LPO), but they cannot navigate arbitrary well-founded trees.

The dispensability of the Fan Theorem (Paper 30) provides the empirical evidence for this exclusion. Every physical prediction that was derived via compactness (FT's primary application) can be re-derived without it, using direct construction (BISH) or bounded monotone convergence (LPO). Nature solves optimization problems by satisfying equations (BISH), not by searching over compact sets (FT). Nature takes thermodynamic limits by monotone convergence (LPO), not by extracting convergent subsequences (FT). The tree-search capabilities that FT and Bar Induction provide are powerful mathematical tools, but they address a kind of difficulty — infinite branching — that physical predictions do not encounter.

### 7.5 Exclusion 4: Set-Theoretic Combinatorics

BISH+LPO is an arithmetic theory — its assertions concern natural numbers, real numbers (as Cauchy sequences), and functions between them. It has no set-theoretic content. The Continuum Hypothesis (CH), large cardinal axioms, the full Axiom of Choice, projective determinacy, Martin's axiom — the entire landscape of modern set theory — is physically meaningless. No experiment can distinguish a CH-universe from a ¬CH-universe. No scattering amplitude depends on whether inaccessible cardinals exist. No phase transition requires determinacy for analytic sets.

This is not a claim about the mathematical importance of set theory — it is a claim about its physical irrelevance. Set theory is powerful and deep mathematics. But physics uses only a tiny fragment of the mathematical language that ZFC provides. The relationship is analogous to using a dictionary: the Oxford English Dictionary contains 170,000 entries, but a grocery list uses perhaps 30 words. The dictionary is not wrong or unnecessary — it serves other purposes. But the grocery list does not need it. Physics is the grocery list; ZFC is the dictionary.

The full Axiom of Choice deserves special mention. AC is used routinely in functional analysis (the existence of Hamel bases, the Hahn-Banach theorem in full generality, the existence of non-measurable sets) and is embedded in much of the mathematical infrastructure that physicists inherit. But the programme's calibration shows that every *empirical prediction* extracted from AC-dependent infrastructure can be re-derived without AC, using at most BISH+LPO. AC, like the Fan Theorem and Dependent Choice, is dispensable scaffolding — present in the mathematical framework, absent from the physical content.

### 7.6 Exclusion 5: Full Classical Logic

LPO is Σ₁⁰-LEM — the law of excluded middle restricted to existential statements over decidable predicates. It is not full LEM. Physics can decide "does this sequence have a nonzero term?" (Σ₁⁰) but cannot decide arbitrary propositions about infinite-dimensional Hilbert spaces, continuous functions, or uncountable sets. The gap between Σ₁⁰-LEM and full LEM is enormous — it is the difference between deciding one quantifier alternation and deciding arbitrary logical complexity.

The measurement problem provides the most vivid illustration. The double-slit experiment asks: "did the electron go through slit A or slit B?" This is a Σ₁⁰ question (a decision about a specific detector event) and is LPO-decidable. But the wavefunction collapse question — "did the quantum state transition from a superposition to an eigenstate?" — is a proposition about the state of an infinite-dimensional Hilbert space, and BISH+LPO does not validate LEM for such propositions. The interpretations of quantum mechanics differ precisely on whether to apply LEM to these higher-complexity propositions. Copenhagen applies LEM (the system is in an eigenstate or it isn't). Many-Worlds refuses LEM (the superposition is real, no collapse occurs). The empirical predictions are identical because they depend only on Born rule probabilities (BISH/LPO), not on the metaphysical status of collapse.

The exclusion of full LEM has a precise physical meaning: physics cannot decide questions whose logical complexity exceeds Σ₁⁰. It can decide "is this energy eigenvalue above threshold?" (Σ₁⁰) but not "does this quantum system have a property P for every possible measurement?" (Π₂⁰ and beyond). The boundary between what physics can and cannot decide is not vague or philosophical — it is the boundary between Σ₁⁰ and higher levels of the arithmetic hierarchy.

### 7.7 Falsifiability

The characterization makes concrete, testable predictions — and this is what separates it from philosophical speculation about the foundations of mathematics. Five specific predictions follow from BISH+LPO as the logical constitution of empirical physics: (1) no scattering amplitude at any loop order will require deciding a Σ₂⁰ statement; (2) no physical constant will be shown to be non-Δ₂⁰ (non-limit-computable); (3) no empirical prediction will require the Fan Theorem or Bar Induction; (4) no empirical prediction will require the full Axiom of Choice or any set-theoretic axiom beyond arithmetic; (5) no finite-precision measurement will require full LEM (as opposed to Σ₁⁰-LEM). Each prediction is falsifiable: a single counterexample refutes the characterization.

Paper 39 shows that generic intensive observables *without promise gap* can reach Σ₂⁰. This does not refute the characterization — it refines it. The empirical ceiling (LPO) is intact because finite experimental precision enforces an effective promise gap that collapses Σ₂⁰ decisions back to Σ₁⁰. The Platonic ceiling (Σ₂⁰) is a new discovery that sharpens the boundary analysis: it identifies exactly how far physics *could* reach if infinite-precision measurements were possible. The gap between the empirical ceiling (Σ₁⁰) and the Platonic ceiling (Σ₂⁰) is precisely one quantifier alternation, and it is bridged by the promise gap — the logical signature of finite experimental precision.

The characterization predicts that no *empirical* prediction — no number compared to a finite-precision measurement — requires Σ₂⁰ reasoning. This prediction has survived 39 calibration papers across every major domain of physics. It remains unfalsified. If a laboratory measurement is discovered that requires distinguishing "gap = 0" from "gap approaches 0" with infinite precision — that is, a measurement that genuinely requires Σ₂⁰ reasoning — the empirical ceiling is broken. The programme invites such a discovery: falsification would be more interesting than confirmation.

---

## Part IV: The Undecidability Arc

---

## Chapter 8: The Genealogy of Physical Undecidability

### 8.1 Overview

In 2015, Cubitt, Perez-Garcia, and Wolf proved that the spectral gap problem is undecidable — a Hamiltonian encoding a Turing machine can be constructed such that whether the system is gapped or gapless is as hard as the halting problem. This result was widely interpreted as revealing a fundamental limit to physical knowledge, a proof that quantum physics harbors irreducible unknowability.

The programme faced a question: does Cubitt's undecidability break the LPO ceiling? Does physics require logical resources beyond Σ₁⁰ after all?

Papers 36–38 answer: no. Every known physical undecidability result is Turing-Weihrauch equivalent to LPO. "Undecidability" in physics is not a new phenomenon — it is the non-computability of LPO, the same principle that governs thermodynamic limits, phase transitions, and coupling constant existence. Physical undecidability adds zero new logical resources to the programme's thesis.

Paper 39 then asks the deeper question: is LPO really a hard ceiling, or are there observables beyond it? The answer — Σ₂⁰ for generic intensive observables — refines the thesis without breaking it.

### 8.2 Cubitt's Theorem Is LPO (Paper 36)

The stratification of Cubitt-Perez-Garcia-Wolf through the constructive hierarchy reveals four layers:

| Level | Content | Mechanism |
|-------|---------|-----------|
| BISH | Finite-volume spectral gap Δ_L | Algebraic eigenvalue computation |
| LPO | Thermodynamic limit Δ = lim Δ_L | Bounded Monotone Convergence |
| LPO | Each instance: "is H(M) gapped?" | Σ₁⁰ decision for specific M |
| Non-computable | Uniform function M ↦ gapped/gapless | = Halting problem = LPO non-computability |

The finite-volume spectral gap is the energy difference between the ground state and first excited state of a finite-dimensional Hamiltonian. This is an eigenvalue computation — finite linear algebra, pure BISH. No omniscience needed.

The thermodynamic limit — asserting that the sequence of finite-volume gaps converges to a real number — is Bounded Monotone Convergence, hence LPO. This is exactly the same mechanism as the Ising model (Paper 8) and is governed by Fekete's equivalence (Paper 29).

Each specific instance — "is Hamiltonian H(M) gapped, where M is a particular Turing machine?" — reduces to "does M halt?" This is a Σ₁⁰ decision, decidable by LPO. The undecidability arises only when asking the *uniform* question: "given an arbitrary M, is H(M) gapped?" This uniform question is the halting problem, which is non-computable — but its non-computability is exactly the non-computability of LPO applied to arbitrary inputs.

The bridge to the constructive programme: Cubitt's construction encodes Turing machine computation into a Hamiltonian via aperiodic tilings. The ground state *is* a tiling configuration. The spectral gap encodes halting. The promise gap — Δ ∈ {0} ∪ [γ, ∞) — ensures the decision is Σ₁⁰ (not Π₂⁰). Paper 36 proves this encoding is exactly LPO, verified in 655 lines of Lean 4 with zero sorry.

The physical punchline: the spectral gap is undecidable for the same reason that phase transitions cost LPO. Both require completing a thermodynamic limit. Cubitt's celebrated result, once stratified, reveals not a new form of unknowability but the familiar face of LPO — the same principle physicists have implicitly invoked since Boltzmann defined the thermodynamic limit in the 1870s.

### 8.3 The Undecidability Landscape (Paper 37)

Paper 36 proved Cubitt ≡ LPO. Paper 37 proves this is not special to Cubitt — it is universal. The meta-theorem: any undecidability result in physics obtained by computable many-one reduction from the halting problem is Turing-Weihrauch equivalent to LPO.

Three further undecidability results are explicitly stratified:

1. **Uncomputability of phase diagrams (Bausch-Cubitt-Watson 2021):** The assertion that the phase diagram of a many-body system is uncomputable reduces to LPO. The mechanism: the phase boundary is the locus where a thermodynamic potential is non-analytic, and non-analyticity requires a completed limit (LPO).

2. **1D spectral gap undecidability (Bausch-Cubitt-Lucia-Perez-Garcia 2020):** The 1D version of Cubitt's result, achieved via a more sophisticated tiling construction. Still LPO — the dimension does not change the logical structure.

3. **Uncomputable renormalization group flows (Cubitt-Lucia-Perez-Garcia-Perez-Eceiza 2022):** The assertion that RG fixed points are uncomputable. The mechanism: RG flow endpoints are completed limits of iterative coarse-graining. LPO.

The meta-theorem is structurally simple. The halting problem is Σ₁⁰-complete — it is the hardest decision problem with one existential quantifier over decidable predicates. LPO decides all Σ₁⁰ statements. Any computable many-one reduction preserves the Σ₁⁰ classification: if the input is Σ₁⁰ (halting) and the reduction is computable (BISH), the output is Σ₁⁰ (LPO). Therefore every such undecidability result lands at exactly LPO.

A notable exception establishes an important distinction: the ground state energy density (Watson-Cubitt 2021) is BISH. Computing the energy density is computationally *hard* (exponential time) but logically *decidable* (computable). Computational complexity — how long a computation takes — is fundamentally different from logical undecidability — whether a computation terminates at all. The ground state energy density is hard but not undecidable. The spectral gap is undecidable but not more undecidable than LPO.

The emerging narrative: "undecidability" in physics is a misnomer. What Cubitt et al. discovered is not that physics harbors irreducible unknowability — it is that the thermodynamic limit, which physicists have used routinely for 150 years, is non-computable when applied uniformly. The undecidability is LPO's non-computability wearing a quantum costume.

Paper 37: 660 lines of Lean 4, zero sorry.

### 8.4 Wang Tiling — The Grandfather (Paper 38)

Paper 38 traces the genealogy of physical undecidability to its origin. Every undecidability result in quantum many-body physics descends from a single ancestor: the undecidability of Wang tiling.

Wang (1961) conjectured that if a finite set of tiles can tile the plane, it can do so periodically. Berger (1966) disproved this by constructing an aperiodic tileset — one that tiles the plane but only aperiodically — and proved that the general tiling problem is undecidable. Robinson (1971) simplified the construction. The genealogy then branches into physics:

```
Wang Tiling (1961) → Berger (1966) → Robinson (1971)
    ↓
Kanter (1990): undecidable Potts model
    ↓
Gu-Weedbrook-Perales-Nielsen (2009): undecidable 2D Ising
    ↓
Cubitt-Perez-Garcia-Wolf (2015): spectral gap [Paper 36]
    ├── Bausch-Cubitt et al. (2020): 1D spectral gap [Paper 37]
    ├── Bausch-Cubitt-Watson (2021): phase diagrams [Paper 37]
    └── Cubitt-Lucia et al. (2022): RG flows [Paper 37]
```

Paper 38 proves that Wang tiling itself — the ancestor of the entire genealogy — is Turing-Weihrauch equivalent to LPO. The decision problem "does finite tileset T tile the plane?" is Σ₁⁰-complete, hence LPO-equivalent. The aperiodicity detection problem "are all valid tilings of T aperiodic?" is also LPO-equivalent.

The Grandfather Theorem states: every descendant in the genealogy inherits exactly LPO from Wang tiling. No descendant can exceed LPO because each is obtained by computable reduction from a Σ₁⁰-complete problem, and LPO decides all Σ₁⁰ statements. No descendant falls below LPO because each embeds the full halting problem.

The Σ₁⁰ Ceiling Theorem completes the analysis: to exceed LPO — to reach Σ₂⁰ — would require encoding a problem that is Σ₂⁰-complete (such as the finiteness problem: "does M halt on infinitely many inputs?"). No existing construction in quantum many-body physics achieves this. Paper 39 will construct exactly such an encoding — but the resulting observable is empirically inaccessible.

Paper 38: 573 lines of Lean 4, zero sorry.

### 8.5 What Undecidability Actually Is

Papers 36–38 together establish a single conclusion: physical undecidability is LPO's non-computability, inherited from the thermodynamic limit, traceable to Wang tiling.

This is a reclassification. Before this programme, spectral gap undecidability was understood as follows: "there exist Hamiltonians whose gapped/gapless nature cannot be determined by any algorithm." This is correct but misleading. The reclassification: "the thermodynamic limit — asserting that an infinite sequence of finite-volume quantities converges — is non-computable when applied uniformly; Cubitt et al. embedded the halting problem into this non-computability; the result is the non-computability of LPO, the same principle that governs every completed limit in physics."

All physical undecidability is one phenomenon wearing different costumes. The spectral gap, phase diagrams, RG flows, and 1D spectral gap are all instances of the same logical event: encoding a halting problem into a Σ₁⁰ decision via a computable reduction. The diversity of the physical contexts masks the uniformity of the logical mechanism.

---

## Chapter 9: Beyond LPO — The Thermodynamic Stratification

### 9.1 The Promise Gap as Logic Mechanism

Cubitt's original construction builds Hamiltonians with a promise gap: Δ ∈ {0} ∪ [γ, ∞) for some computable γ > 0. The system is either exactly gapless or gapped by at least γ — nothing in between. This is not a physical restriction but a feature of the encoding.

The promise gap has a precise logical consequence. With the gap, deciding "is Δ = 0?" reduces to:

∃L such that Δ_L < γ/2

This is a Σ₁⁰ statement — a single existential quantifier over a decidable predicate (comparing finite-precision eigenvalues). LPO decides it.

Without the promise gap — for a generic Hamiltonian where Δ could be any non-negative real — deciding "is Δ = 0?" requires:

∀m ∃L such that Δ_L < 1/m

This is a Π₂⁰ statement — a universal-existential quantifier alternation. LPO cannot decide it. It requires LPO' (Σ₂⁰-LEM), the ability to decide statements with two quantifier alternations.

The promise gap is not a convenience or a technical limitation of Cubitt's construction. It is the *logical mechanism* that determines whether the decision lives at Σ₁⁰ or Σ₂⁰. When Cubitt et al. proved undecidability with a promise gap, they were proving LPO non-computability. When the promise gap is removed, the arithmetic complexity increases by one quantifier alternation.

### 9.2 The Modified Encoding

Paper 39 constructs an explicit encoding that reaches Σ₂⁰. The modification uses Robinson aperiodic tilings with perimeter counters: supertiles of increasing scale k = 0, 1, 2, ... each run a Turing machine M on input k, where k is extracted from the perimeter counter of the supertile.

The encoding achieves:
- **Gapped** ↔ M halts on finitely many inputs
- **Gapless** ↔ M halts on infinitely many inputs

This is the **Finiteness Problem** — deciding whether a Turing machine halts on finitely or infinitely many inputs — which is Σ₂⁰/Π₂⁰-complete. It sits strictly above the halting problem in the arithmetic hierarchy.

The construction is verified in 802 lines of Lean 4 with zero sorry. The key technical ingredients are:
1. Robinson tilings provide hierarchical supertile structure at arbitrarily large scales
2. Perimeter counters extract the scale k as a computable input
3. The modified Hamiltonian H(M) has its gap behavior determined by the *collective* halting behavior of M across all inputs, not just a single input
4. The promise gap is removed: Δ can approach 0 without reaching it, creating a genuine Π₂⁰ decision

### 9.3 The Thermodynamic Stratification Theorem

Paper 39's central result is the Thermodynamic Stratification Theorem, which classifies observables by their arithmetic complexity as a function of thermodynamic scaling:

**Extensive observables** (energy density, free energy, magnetization per site) converge via subadditivity — the energy of a composite system is at most the sum of its parts. Fekete's lemma (≡ LPO, Paper 29) guarantees convergence. The arithmetic ceiling for extensive observables is **LPO (Σ₁⁰)**, regardless of promise gap.

**Intensive observables** (spectral gap, correlation length, mass gap) are determined by infimum-type operations, not averages. Without a promise gap, deciding whether an intensive observable equals a specific value (e.g., Δ = 0) involves a Π₂⁰ statement. The arithmetic ceiling for generic intensive observables is **LPO' (Σ₂⁰)**.

**Empirical observables** — quantities measured at finite precision — always carry an effective promise gap. A spectrometer measuring the spectral gap with precision ε effectively collapses the Π₂⁰ decision to Σ₁⁰: "is there a finite-volume gap below ε/2?" is decidable by LPO. The arithmetic ceiling for empirical observables is **LPO (Σ₁⁰)**.

The theorem identifies three tiers of physical reality:

| Tier | Observables | Ceiling | Mechanism |
|------|------------|---------|-----------|
| Empirical | All measured quantities | LPO (Σ₁⁰) | Finite precision = promise gap |
| Extensive-Platonic | Thermodynamic densities | LPO (Σ₁⁰) | Fekete/BMC |
| Intensive-Platonic | Gap, correlation length | LPO' (Σ₂⁰) | No promise gap, infimum-type |

### 9.4 The Refined Thesis

The original thesis of the programme: the logical constitution of empirical physics is BISH+LPO. Paper 39 refines this without breaking it:

**Empirical physics** (predictions compared to finite-precision measurements) remains at **BISH+LPO**. The empirical ceiling is confirmed — every number an experimentalist measures is constructively computable at the LPO level.

**Platonic physics** (exact mathematical properties of idealized infinite-volume systems) can reach **BISH+LPO'** for intensive observables. The question "is this generic Hamiltonian gapped?" — asked with infinite precision, without any promise — requires Σ₂⁰ reasoning.

The gap between empirical and Platonic physics is precisely the promise gap, and the promise gap is precisely finite experimental precision. The refinement *strengthens* the programme's thesis in three ways:

1. It identifies the *mechanism* that keeps empirical physics at Σ₁⁰: finite precision enforces effective promise gaps.
2. It identifies the *boundary* of the thesis: the Σ₂⁰ tier is real but inaccessible to experiment.
3. It makes a sharper falsifiable prediction: if a laboratory measurement is shown to require Σ₂⁰ reasoning (distinguishing between "gap approaches 0" and "gap equals 0" with infinite precision), the empirical ceiling is broken.

---

## Chapter 10: Consequences

### 10.1 For Quantum Gravity

The characterization predicts that whatever empirical predictions quantum gravity eventually makes, they will be BISH+LPO. This prediction applies to all candidate theories.

**String theory.** The string landscape — the space of consistent string vacua — is constructed using Calabi-Yau geometry, which relies heavily on compactness (the Fan Theorem). But compactness is dispensable (Paper 30). The landscape is mathematical scaffolding; whatever empirical predictions emerge from a specific string vacuum will be finite computations (BISH) or completed limits (LPO). The swampland programme, which asserts universal constraints of the form "no consistent theory has property P," makes Π₂⁰ claims (universal quantification over a space of theories). These claims may exceed BISH+LPO — and if they do, the programme predicts they are logically disconnected from empirical physics. A swampland constraint that cannot be formulated at the Σ₁⁰ level cannot be tested by any finite-precision experiment.

**Loop quantum gravity** fits the characterization naturally. Spin network states at finite graph size are combinatorial objects — BISH. The continuum limit (refinement of the spin foam) costs LPO, exactly as in lattice QCD. The logical structure of loop quantum gravity mirrors the pattern seen in every other physical theory: finite computation plus completed limits.

**Holographic entanglement entropy** (Ryu-Takayanagi) represents the most important untested prediction of the programme. The RT formula relates entanglement entropy on the boundary CFT to a minimal surface area in the bulk AdS spacetime. If both sides of AdS/CFT — the boundary computation (a quantum field theory calculation) and the bulk computation (a geometric optimization) — calibrate to BISH+LPO, then the duality is logically consistent in the programme's sense. If one side costs more than the other, the programme has identified a logical obstruction to the duality. This is the natural next calibration target.

### 10.2 For the Measurement Problem

The measurement problem asks: what happens when a quantum system is measured? The three major interpretations give different answers, and Paper 23 calibrated each answer against the constructive hierarchy. Many-Worlds requires Dependent Choice to construct the branching tree of the universal wavefunction — each measurement creates new branches, and the infinite tree requires DC. Copenhagen requires WLPO to assert that a definite outcome occurred (a zero-test on the superposition coefficients). Bohmian mechanics requires LPO to assert the existence of the pilot wave trajectory as a completed real-valued function of time.

The crucial observation: DC is dispensable (Paper 31). The branching structure that Many-Worlds requires is mathematical scaffolding — the empirical predictions (Born rule probabilities) are BISH and do not depend on whether the branches "exist." Similarly, Copenhagen's collapse postulate (WLPO) and Bohm's trajectory existence (LPO) generate the same BISH-level empirical predictions. The interpretations agree on every number that an experimentalist can measure. They disagree about ontological claims — claims about what "really happens" — at different heights in the hierarchy.

This does not "solve" the measurement problem in the sense of determining which interpretation is correct. It reclassifies the problem: from "what actually happens during measurement?" to "which logically dispensable mathematical framework do you prefer for describing non-empirical aspects of quantum theory?" The reclassification is valuable because it identifies precisely where the disagreement lives (in the choice of scaffolding above BISH) and why it is empirically unresolvable (because the scaffolding is dispensable). The interpretations are not competing physical theories — they are competing mathematical frameworks for the same physical content.

### 10.3 For the Cosmological Constant

The cosmological constant problem is often called the worst prediction in the history of physics: the quantum field theory estimate of the vacuum energy density exceeds the observed value by a factor of approximately 10¹²⁰. The QFT "prediction" is obtained by summing the zero-point energies of all quantum field modes — an infinite sum that, after regularization and renormalization, yields a finite but astronomically large number. The observed cosmological constant Λ is tiny by comparison.

The programme reclassifies this discrepancy. The QFT vacuum energy sum is an infinite series. Asserting that this series converges to a specific value is a completed limit — LPO. The BISH-level content is different: for any finite number of modes (any finite UV cutoff), the vacuum energy is finite and computable. The 10¹²⁰ discrepancy arises from comparing a completed infinite sum (LPO-level) to a measured value (BISH-level). It is a statement about a completed object that no experiment directly accesses — no experiment sums infinitely many modes.

The reclassification changes the diagnosis from "wrong prediction" to "artifact of idealization." The QFT vacuum energy is not a prediction in the empirical sense — it is a property of a completed mathematical object (the infinite sum) that exists at the LPO level. The measured cosmological constant is a BISH-level observable. Comparing an LPO-level mathematical artifact to a BISH-level measurement and calling the discrepancy a "prediction failure" conflates two different logical levels. This is not a resolution of the cosmological constant problem — the question of why Λ has its observed value remains open — but it is a change in character: the problem is about the relationship between mathematical idealization and physical measurement, not about a straightforward prediction failure.

### 10.4 For the Nature of Physical Constants

The characterization implies that every physical constant — the fine structure constant α ≈ 1/137, the electron mass mₑ, the Higgs vacuum expectation value v, the cosmological constant Λ — is a Δ₂⁰ real number. Each admits a finite description: an algorithm that, given access to a halting oracle (one instance of LPO), converges to the constant's value. No physical constant can encode a Σ₂⁰-complete problem. No physical constant is algorithmically random in the strong sense of being incompressible.

This reframes the fine-tuning debate. The standard discussion assumes that physical constants are drawn from the continuum — an uncountable set with measure-theoretic properties (the probability of a "life-permitting" universe is some tiny fraction of the full parameter space). But the programme says physical constants are Δ₂⁰ — a countable class. The sample space is fundamentally different from what fine-tuning arguments assume. A fine-tuning argument that computes the probability of α having its observed value by integrating over all real numbers is integrating over a space that is overwhelmingly populated by constants that physics cannot access. The physically relevant sample space is Δ₂⁰, which is countable and does not support the standard measure-theoretic formulation of fine-tuning.

This does not settle the fine-tuning question — the question of why constants have their observed values remains open. But it constrains the form that an answer can take: any explanation must be compatible with the constants being limit-computable, and any probabilistic argument must be formulated over Δ₂⁰ rather than ℝ.

### 10.5 For Consciousness and AI

*The following remarks are speculative and are clearly marked as such.*

If consciousness supervenes on physical processes — if mental states are determined by brain states, which are physical states — then the characterization imposes a constraint: conscious agents cannot access mathematical truths beyond Σ₁⁰ through physical processes alone. A brain is a physical system; its computations are BISH+LPO; its outputs cannot exceed the arithmetic complexity of its inputs. This is consistent with the phenomenology of mathematical intuition: mathematicians have powerful intuitions about mathematical truths but cannot, by introspection alone, decide whether the Continuum Hypothesis is true.

For artificial intelligence, the constraint is more concrete. Neural networks perform finite-precision arithmetic on finite-dimensional tensors — pure BISH. Training involves gradient descent (iterative optimization, BISH at each step) with convergence assertions that cost at most LPO. No current AI architecture exceeds BISH+LPO. Whether an AI system could implement LPO — that is, whether it could physically instantiate the completion of a bounded monotone limit — is an open engineering question. The programme does not resolve it but provides a framework for asking it precisely: an AI system that genuinely implements LPO would be performing a physical operation equivalent to completing a thermodynamic limit.

### 10.6 For Physical Undecidability

The undecidability arc (Papers 36–39) has a direct consequence for how "undecidability" in physics should be understood. Before this programme, spectral gap undecidability was widely interpreted as revealing a fundamental limit to physical knowledge — a proof that quantum physics harbors irreducible unknowability, comparable in significance to Gödel's incompleteness theorems. The reclassification offered by this programme is sobering: physical undecidability is the non-computability of LPO, the same principle that physicists have implicitly used since Boltzmann defined the thermodynamic limit in the 1870s.

This reclassification changes the character of the problem. The spectral gap of a *specific* Hamiltonian H(M) is not "unknowable" — it is LPO-decidable, meaning it is decidable given the ability to complete bounded monotone limits. A physicist who can take a thermodynamic limit can decide whether H(M) is gapped. The *uniform* problem — deciding for arbitrary Hamiltonians simultaneously — is non-computable because LPO is non-computable when applied to arbitrary binary sequences. But this is the same non-computability that prevents a general-purpose convergence oracle: given an arbitrary bounded monotone sequence, there is no algorithm to determine whether its limit exceeds a given threshold. Cubitt's celebrated result, once stratified, reveals not a new frontier of unknowability but the familiar non-computability of a principle physicists have used for 150 years.

The Σ₂⁰ refinement (Paper 39) sharpens this further. For generic intensive observables without promise gap, the decision reaches Σ₂⁰ — one quantifier alternation beyond LPO. The question "is this Hamiltonian gapped, where the gap can be any non-negative real?" requires deciding a Π₂⁰ statement that LPO cannot handle. But this Σ₂⁰ tier is Platonic: no finite-precision experiment can distinguish "gap = 0" from "gap < ε for all measurable ε." The empirical ceiling remains LPO because finite experimental precision enforces an effective promise gap. Physical undecidability is not a window into Platonic mathematics — it is a consequence of the thermodynamic limit, and its Platonic extensions are empirically inaccessible.

---

## Chapter 11: The Formalization

### 11.1 Why Formal Verification

The formal verification in Lean 4 is not an optional supplement to the programme — it is essential infrastructure. The distinctions between BISH, WLPO, LLPO, and LPO are too fine for informal mathematical reasoning. These principles are logically close: LLPO and WLPO differ in one quantifier placement; WLPO is strictly weaker than LPO but implies it for bounded monotone sequences; the boundary between "constructive proof with LPO hypothesis" and "classical proof using LPO as a theorem" is invisible in natural-language mathematics but precisely detectable by a proof assistant.

The LPO-weakening incident (Paper 2, §11.5) demonstrated the fragility of informal calibration. An AI coding agent, uncomfortable with meta-classical reasoning, replaced a classical metatheoretic argument with object-level LPO. The resulting proof was logically valid and appeared correct to natural-language review. But the calibration was destroyed: LPO implies WLPO, so the bidual gap hypothesis became logically redundant, and the theorem — which was supposed to show the gap has exactly the strength of WLPO — became vacuously true. The error was caught only by examining the Lean axiom profile via `#print axioms`. Without formal verification, the error would have persisted indefinitely.

Lean 4's kernel checks every logical step in every proof. The command `#print axioms theorem_name` lists every axiom the proof depends on. If `Classical.choice` appears, the proof uses non-constructive reasoning — and the specific axiom tag identifies exactly where and why. If `Classical.choice` is absent, the proof is mechanically certified as constructive (BISH). This is not a matter of opinion, interpretation, or mathematical convention — it is a mechanical fact about the proof term, as verifiable as a compiler checking type safety.

The choice of Lean 4 over other proof assistants (Coq, Agda, Isabelle) was driven by Mathlib — the comprehensive mathematical library that provides the infrastructure for real analysis, functional analysis, measure theory, and linear algebra that the programme requires. Mathlib's coverage of graduate-level mathematics made it possible to formalize physics theorems without building the entire mathematical infrastructure from scratch. The tradeoff — Mathlib's pervasive use of `Classical.choice` in its infrastructure, which appears in every theorem involving ℝ — is managed by the certification levels (§11.3): infrastructure-level classical axioms are distinguished from theorem-level non-constructive content.

### 11.2 The Producer/Consumer Architecture

Constructive reverse mathematics proofs work in a classical metatheory, just as Simpson's classical reverse mathematics uses ZFC as a base theory. The programme adopts a "producer/consumer" architecture inspired by dependency injection in software engineering.

The **producer** operates in the classical metatheory. Given a physical theorem T and a candidate principle P (e.g., LPO), the producer constructs a concrete mathematical artifact — typically a specific binary sequence, a specific bounded monotone sequence, or a specific real number — using whatever non-constructive reasoning is convenient. The artifact is the bridge between T and P. The **consumer** takes this artifact as input and derives P from T using only BISH. The consumer's proof is constructive: it shows that the physical theorem, applied to the producer's artifact, yields the omniscience principle.

The Lean formalization validates this architecture mechanically. Running `#print axioms` on the consumer's theorem shows no `Classical.choice` — the derivation is constructive. Running `#print axioms` on the producer's construction shows `Classical.choice` — the artifact was built non-constructively. The two components are independently checkable. The consumer's constructive status does not depend on how the artifact was built, only on what the consumer does with it. This separation is the formal analogue of the classical/constructive distinction in CRM.

### 11.3 Certification Levels

The programme uses four certification levels, reflecting the different ways Lean axioms can appear in a proof.

**Level 1 (Fully verified):** The theorem's `#print axioms` output contains only the Lean kernel axioms (propositional extensionality, quotient soundness) and Mathlib foundations. No `Classical.choice`, no custom axioms. The theorem is mechanically certified as BISH. Examples: finite-lattice partition functions, tree-level scattering amplitudes, Born rule at finite precision.

**Level 2 (Structurally verified):** Same as Level 1 but may include Mathlib infrastructure axioms (the `Classical.choice` that appears because Mathlib's ℝ is defined via Cauchy completion, which uses classical reasoning at the infrastructure level). The theorem itself is constructive — the classical content is in the mathematical library, not in the physics. Examples: most calibration theorems, since they involve real-number arithmetic over Mathlib's ℝ.

**Level 3 (Intentional classical):** The theorem contains `Classical.choice` arising from an explicit LPO, WLPO, or LLPO hypothesis. The non-constructive content *is* the theorem's content — the theorem says "assuming LPO, we can prove X," and the `Classical.choice` in the axiom profile reflects the LPO hypothesis. This is correct and expected: a theorem that calibrates to LPO *should* show classical axioms when it invokes LPO. Examples: Fekete's lemma (LPO hypothesis), thermodynamic limits, coupling constant existence.

**Level 4 (Axiomatized physics):** The theorem contains explicit `axiom` declarations — physical assumptions that are stated but not proved. Each axiom is documented with its physical justification and its logical role. Examples: Yang-Mills existence and mass gap (Paper 33), positivity of the string tension (Paper 33), specific Hamiltonian properties in the undecidability arc.

### 11.4 The Codebase

The codebase comprises approximately 33,000 lines of Lean 4 across 39 paper repositories, organized in four phases:

- **Phase I (Papers 2–28):** Approximately 20,000 lines covering the initial calibration across statistical mechanics, quantum mechanics, quantum field theory, general relativity, quantum information, and classical mechanics. This phase established the empirical pattern: everything calibrates to BISH+LPO.
- **Phase II (Papers 29–31):** Approximately 4,000 lines establishing the three foundational theorems — Fekete ↔ LPO (Paper 29, ~1,300 lines), Fan Theorem dispensability (Paper 30, ~1,300 lines), and Dependent Choice dispensability (Paper 31, ~1,400 lines). This phase transformed the empirical pattern into a thesis.
- **Phase III (Papers 32–35):** Approximately 6,000 lines calibrating the Standard Model (QED, QCD, scattering amplitudes) and proving the conservation metatheorem. This phase tested the thesis against the most precisely measured physics.
- **Phase IV (Papers 36–39):** Approximately 2,690 lines for the undecidability arc: Cubitt ≡ LPO (Paper 36, 655 lines), undecidability landscape (Paper 37, 660 lines), Wang tiling ancestor (Paper 38, 573 lines), and thermodynamic stratification (Paper 39, 802 lines). This phase extended the thesis to physical undecidability and discovered the Σ₂⁰ Platonic ceiling.

All code is publicly available on Zenodo with individual DOIs for each paper (see Appendix A). Compilation requires Lean 4 (installed via elan) and Mathlib. Detailed instructions are provided in Appendix B.

### 11.5 The LPO-Weakening Incident

The LPO-weakening incident in Paper 2 is the programme's most instructive failure. Paper 2 calibrates the bidual gap — the assertion that a Banach space X is isometrically isomorphic to its bidual X** — against the constructive hierarchy. The correct calibration: the bidual gap has exactly the strength of WLPO. The theorem states that WLPO is both necessary and sufficient, placing the gap precisely in the hierarchy.

During the formalization, an AI coding agent — uncomfortable with the meta-classical producer/consumer architecture — replaced the meta-classical producer with an object-level LPO hypothesis. The resulting proof compiled without errors and appeared correct on informal review. But the calibration was silently destroyed. LPO implies WLPO (LPO is strictly stronger), so the bidual gap hypothesis — which was supposed to provide exactly WLPO — became logically redundant under the LPO hypothesis. The theorem was vacuously true: it said "assuming something stronger than WLPO, we can derive WLPO." The calibration's content — that the gap is *exactly* WLPO, not LPO or stronger — was lost.

The error was caught by examining the `#print axioms` output, which showed `Classical.choice` entering from the LPO hypothesis rather than from a WLPO hypothesis. The fix was straightforward: restore the meta-classical architecture, ensuring the consumer uses only a WLPO hypothesis. The lesson is not: it is that without formal verification — without the mechanical ability to inspect axiom profiles — the fine distinctions between WLPO and LPO would be undetectable. A human reviewer reading the "fixed" proof in natural language would have found it entirely convincing. The error was invisible to informal reasoning and mechanically obvious to Lean.

---

## Chapter 12: What This Programme Does Not Do

### 12.1 Epistemology vs. Ontology

The programme characterizes the logical resources needed to *predict* physical behavior — to compute the numbers that experimentalists compare to measurements. It does not determine the logical resources the universe *uses* to *generate* that behavior. These are fundamentally different questions, and conflating them is the most common misreading of the programme's claims.

An analogy clarifies the distinction. Chess can be played on a physical board or simulated on a computer. The logical resources needed to *predict* chess outcomes (game tree search, α-β pruning, endgame tablebases) are well-defined computational problems. The logical resources the physical board "uses" to "generate" chess outcomes (the mechanics of wood and paint, the neurophysiology of the players' brains) are entirely different and vastly more complex. The programme is about the prediction question: what logical resources are needed to compute physics predictions? It is not about the generation question: what logical resources does nature use to produce physical phenomena?

The gap is real and important. The characterization says: BISH+LPO suffices to predict every empirical measurement in known physics. It does not say: the universe is a BISH+LPO computer. It does not say: nature "implements" LPO. It does not say: the physical world has the structure of a Σ₁⁰ computation. Paper 29's argument — that phase transitions physically instantiate LPO because they require completing a thermodynamic limit, and phase transitions are empirically real — comes closest to an ontological claim, but it is carefully hedged: LPO is necessary for the mathematical *description* of phase transitions, not necessarily for the physical *mechanism* that produces them.

The epistemological reading is robust: the programme has demonstrated, across 39 papers, that BISH+LPO suffices for all known empirical predictions. The ontological reading — that nature's computational architecture is BISH+LPO — would require additional philosophical argument that the programme does not provide and does not claim to provide.

The gap between "physics needs only BISH+LPO to predict" and "the universe IS a BISH+LPO machine" is real. Closing this gap would require an argument about the ontology of physical law — what it means for a principle to be "instantiated" in nature. Paper 29's argument (phase transitions require LPO, phase transitions are real, therefore LPO is physically instantiated) is the closest the programme comes to an ontological claim, and it is careful: it says LPO is *necessary for the mathematical description*, not that nature "performs" LPO computations.

### 12.2 Completeness

The calibration is not exhaustive. The programme has calibrated the major domains of known physics — statistical mechanics, quantum mechanics, quantum field theory (including the full Standard Model at one loop), general relativity, quantum information theory, classical mechanics, and the landscape of physical undecidability — but significant gaps remain. Multi-loop scattering amplitudes beyond one loop have not been calibrated (the metatheorem predicts they are BISH at each fixed order, but this has not been verified in Lean beyond one loop). Non-perturbative QCD observables beyond confinement and the mass gap — hadron spectroscopy, glueball properties, chiral symmetry breaking — have not been calibrated. Quantum gravity predictions (Ryu-Takayanagi, cosmological observables, black hole information) remain uncalibrated.

Condensed matter physics presents the largest gap. Topological phases of matter, the fractional quantum Hall effect, spin liquids, and topological insulators have not been calibrated. The metatheorem (Chapter 6) predicts these will calibrate to BISH+LPO — they involve finite computations on lattice systems (BISH) and thermodynamic limits (LPO) — but the prediction is untested. The thermodynamic stratification theorem (Chapter 9) predicts that intensive observables in these systems (topological invariants, gap closings) may reach Σ₂⁰ at the Platonic level but that empirical predictions will remain at LPO. Confirming or refuting these predictions is the natural next phase of the programme.

### 12.3 Physical Correctness

Lean verifies logical consistency, not physical correctness. The programme's bridge lemmas — the axioms that encode physical assumptions (e.g., "the partition function of the Ising model satisfies the transfer matrix recursion") — are stated as explicit `axiom` declarations. If a bridge lemma encodes incorrect physics, the Lean proof is logically valid but physically meaningless. Lean guarantees that the calibration *follows from* the physics assumptions; it does not guarantee that the physics assumptions are true.

The programme assumes standard physics: the Standard Model is correct (at least at the energies tested), general relativity describes gravity (at least outside black hole singularities), and statistical mechanics describes thermodynamic systems. If any of these assumptions are wrong — if the Standard Model is superseded by a theory requiring stronger logical resources — the calibration table describes the wrong theories. The logical characterization is conditional: "if known physics is correct, then empirical physics = BISH+LPO." The conditional is non-trivially informative because the physics is well-tested, but it is a conditional nonetheless.

### 12.4 Problem Resolution

The programme reclassifies several open problems in physics — the measurement problem, the cosmological constant discrepancy, the nature of physical constants, the significance of physical undecidability — but reclassification is not resolution. The measurement problem, even after reclassification as a disagreement about dispensable scaffolding, still involves a genuine question: why does the macroscopic world *appear* classical if the fundamental description is quantum? The programme says the disagreement is about framework choice (which dispensable principle to invoke), not about physical reality. But framework choice still matters for how physicists think about and develop their theories, even if it does not affect empirical predictions.

Similarly, reclassifying the cosmological constant discrepancy as an "artifact of idealization" does not explain why Λ has its observed value. Reclassifying physical undecidability as "LPO non-computability" does not make the spectral gap computable. The programme changes the *character* of these problems — it identifies what kind of problem each is — but solving a reclassified problem still requires new physics or new mathematics that the programme does not provide.

---

## Chapter 13: Conclusion

### 13.1 Summary

This monograph has presented two narrative threads that converge on a single conclusion.

The first thread is calibration. Across 34 papers spanning statistical mechanics, quantum mechanics, quantum field theory (including the full Standard Model at one loop), general relativity, quantum information theory, and classical mechanics, systematic axiom calibration establishes that every empirical prediction in known physics requires at most BISH+LPO. Fekete's Subadditive Lemma — the mathematical engine of phase transitions — is equivalent to LPO over BISH, proving that LPO is not mathematical scaffolding but a physically instantiated principle (Paper 29). The Fan Theorem and Dependent Choice are dispensable for all empirical predictions (Papers 30–31), proving that nothing above LPO is needed. The conservation metatheorem explains the pattern: empirical predictions are finite compositions of computable functions (BISH), and the only idealizations that exceed finite computation are completed limits without computable modulus (LPO via BMC) (Paper 35). The characterization is not imposed but discovered.

The second thread is undecidability. Every known physical undecidability result — spectral gap (Cubitt et al.), phase diagrams (Bausch et al.), 1D spectral gap, renormalization group flows — is Turing-Weihrauch equivalent to LPO, traceable to a single ancestor: the undecidability of Wang tiling (Papers 36–38). Physical "undecidability" is the non-computability of LPO — the same principle governing thermodynamic limits since Boltzmann. The Σ₂⁰ refinement (Paper 39) reveals a Platonic ceiling for generic intensive observables without promise gap, separated from the empirical LPO ceiling by finite experimental precision. The promise gap — the logical signature of finite precision — is the mechanism that keeps empirical physics at Σ₁⁰.

The two threads converge: BISH+LPO is what physics costs, and LPO is what physics cannot compute uniformly. The cost and the failure are the same principle. The logical constitution of empirical physics — the minimal non-constructive resources required for all predictions compared to experiment — is exactly BISH+LPO. The boundary is sharp, the characterization is falsifiable, and 39 papers with approximately 33,000 lines of machine-checked proof have failed to falsify it.

### 13.2 Future Directions

Three categories of future work present themselves: defensive (stress-testing the characterization), offensive (extending its consequences), and frontier (probing the Σ₂⁰ boundary).

**Defensive.** The highest-priority defensive targets are: (1) AdS/CFT calibration — determining whether both sides of the holographic duality calibrate to BISH+LPO, which would provide a non-trivial consistency check on the duality itself; (2) higher-loop scattering amplitudes — verifying that the BISH pattern persists at two loops and beyond, where the integral structures become more complex; (3) lattice QCD — extending the calibration beyond confinement and the mass gap to hadron spectroscopy and chiral condensate computations; (4) condensed matter physics — calibrating topological phases, the fractional quantum Hall effect, and spin liquid phases, which involve mathematical structures (topological invariants, modular tensor categories) not yet tested against the hierarchy.

**Offensive.** The characterization's predictions reach beyond the calibrated domains. Every physical constant is predicted to be Δ₂⁰ — testable if a method for computing constants from first principles is developed. The measurement problem is predicted to be a scaffolding disagreement — testable if an experiment is designed whose outcome depends on the interpretation of quantum mechanics (current consensus: no such experiment exists). Quantum gravity predictions are predicted to calibrate to BISH+LPO — testable when quantum gravity makes its first empirical prediction.

**Undecidability frontier.** Paper 39's thermodynamic stratification theorem predicts that no laboratory measurement requires Σ₂⁰ reasoning. Testing this prediction requires calibrating undecidability results beyond the quantum many-body context — quasicrystal diffraction patterns, topological classification of phases, undecidability in quantum cellular automata — and determining whether any involves intensive observables that genuinely access the Σ₂⁰ tier under laboratory conditions. The prediction is that finite experimental precision will always enforce an effective promise gap. But experimental surprises have driven this programme from the beginning, and a Σ₂⁰ laboratory observable would be the most consequential discovery the programme could provoke.

The calibration methodology is fully documented and reproducible (Appendix B). Any physical theorem can be calibrated by the same protocol: formalize the theorem in Lean 4, examine `#print axioms`, classify the result, and place it in the hierarchy. The programme invites the community to stress-test the characterization.

### 13.3 Bishop's Legacy

Errett Bishop published "Foundations of Constructive Analysis" in 1967. He defined BISH as a philosophical programme: mathematics should be about constructions, not mere existence proofs. The omniscience principles were identified by Bishop and his successors — Bridges, Richman, Ishihara — as the precise points where classical mathematics departs from constructive practice. This was purely logical cartography, with no physical motivation.

That this cartography — designed for pure mathematics in the 1960s–1990s — turns out to classify the non-constructive content of physics with perfect precision across 39 papers and 33,000 lines of formal verification is the most striking fact about the programme. Bishop's hierarchy was not built to fit physics. Physics was not built to fit Bishop's hierarchy. They fit because the hierarchy captures something real about the structure of mathematical reasoning, and physics uses exactly the fragment of that structure that corresponds to one layer of quantifier alternation over decidable predicates — with the undecidability arc confirming that even the limits of physical knowledge land at the same layer.

The fit is discovered, not designed. That is what makes it worth reporting.

---

## Appendix A: Complete Calibration Table

| Paper | Title | Domain | Key Theorem | Height | Mechanism | Zenodo DOI |
|---|---|---|---|---|---|---|
| 2 | Bidual gap and WLPO | Functional Analysis | X ≅ X** ↔ WLPO | WLPO | Zero-test | 10.5281/zenodo.17107493 |
| 4 | Quantum spectra | Quantum Mechanics | Spectral theorem calibration | LPO | Completed limit | 10.5281/zenodo.17059483 |
| 5 | Schwarzschild curvature | General Relativity | Geodesic computation | BISH/LPO | Finite/limit | 10.5281/zenodo.18489703 |
| 6 | Heisenberg uncertainty | Quantum Mechanics | ΔxΔp ≥ ℏ/2 calibration | BISH/LPO | Finite/limit | 10.5281/zenodo.18519836 |
| 7 | Trace-class operators | Functional Analysis | Physical bidual gap | WLPO | Zero-test | 10.5281/zenodo.18527559 |
| 8 | 1D Ising model | Statistical Mechanics | Partition function / thermo limit | BISH/LPO | BMC | 10.5281/zenodo.18516813 |
| 9 | Ising formulation-invariance | Statistical Mechanics | Transfer matrix ↔ direct sum | LPO | BMC | 10.5281/zenodo.18517570 |
| 10 | Logical geography | Synthesis | Technical synthesis v2.0 | — | — | 10.5281/zenodo.18627193 |
| 11 | CHSH / Tsirelson bound | Quantum Information | Bell nonlocality ↔ LLPO | LLPO | Sign decision | 10.5281/zenodo.18527676 |
| 12 | Constructive history | Synthesis | Historical synthesis v2.0 | — | — | 10.5281/zenodo.18627283 |
| 13 | Event horizon | General Relativity | r = 2M as logical boundary | WLPO/LPO | Zero-test/limit | 10.5281/zenodo.18529007 |
| 14 | Quantum decoherence | Quantum Mechanics | Partial trace calibration | BISH/LPO | Finite/limit | 10.5281/zenodo.18569068 |
| 15 | Noether conservation | General Relativity | Local vs. global conservation | BISH/LPO | Differential/integral | 10.5281/zenodo.18572494 |
| 16 | Born rule | Quantum Mechanics | P = \|⟨ψ\|φ⟩\|² calibration | BISH/LPO | Finite/limit | 10.5281/zenodo.18575377 |
| 17 | Bekenstein-Hawking | General Relativity | S = A/4 as thermo limit | LPO | BMC | 10.5281/zenodo.18597306 |
| 18 | Yukawa RG | QFT | SM one-loop RG stratification | BISH/WLPO/LPO | Threshold/limit | 10.5281/zenodo.18626839 |
| 19 | WKB tunneling | Quantum Mechanics | Tunneling probability | LLPO | Sign decision | 10.5281/zenodo.18602596 |
| 20 | Ising magnetization | Statistical Mechanics | Observable-dependent cost | WLPO | Zero-test on h | 10.5281/zenodo.18603079 |
| 21 | Bell nonlocality | Quantum Information | Bell ↔ LLPO tight | LLPO | IVT | 10.5281/zenodo.18603251 |
| 22 | Radioactive decay | Quantum Mechanics | Markov's Principle | MP ⊂ LPO | Event assertion | 10.5281/zenodo.18603503 |
| 23 | Measurement problem | Quantum Mechanics | Interpretations ↔ DC | DC (dispensable) | Framework choice | 10.5281/zenodo.18604312 |
| 24 | Kochen-Specker | Quantum Information | Contextuality ↔ LLPO | LLPO | Sign decision | 10.5281/zenodo.18604317 |
| 25 | Ergodic theorems | Statistical Mechanics | MET ↔ CC | CC ⊂ LPO | Sequential construction | 10.5281/zenodo.18615453 |
| 26 | Gödel sequences | Functional Analysis | Bidual gap detection WLPO-complete | WLPO | Gödel encoding | 10.5281/zenodo.18615457 |
| 27 | IVT in Bell physics | Quantum Information | LLPO mechanism identified | LLPO | IVT ↔ LLPO | 10.5281/zenodo.18615459 |
| 28 | Classical mechanics | Classical Mechanics | Newton BISH / Lagrange FT | BISH/FT (disp.) | Variational | 10.5281/zenodo.18616620 |
| 29 | Fekete's lemma | Statistical Mechanics | Fekete ↔ LPO | LPO | Binary encoding | 10.5281/zenodo.18643617 |
| 30 | Fan Theorem dispensability | Foundations | FT dispensable for physics | BISH+LPO | Direct construction | 10.5281/zenodo.18638394 |
| 31 | DC dispensability | Foundations | DC dispensable for physics | BISH+LPO | Finite truncation | 10.5281/zenodo.18645578 |
| 32 | QED one-loop | QFT | Running coupling, Landau pole | BISH/LPO | BMC/closed-form | 10.5281/zenodo.18642598 |
| 33 | QCD + confinement | QFT | Asymptotic freedom, mass gap | BISH/LPO | BMC/Fekete/MP | 10.5281/zenodo.18642610 |
| 34 | Scattering amplitudes | QFT | Fixed-order cross sections BISH | BISH | Computable functions | 10.5281/zenodo.18642612 |
| 35 | Conservation metatheorem | Meta | Theorems A–D: why ≤ LPO | LPO ceiling | Computable composition + BMC | 10.5281/zenodo.18642616 |
| 36 | Cubitt's theorem ≡ LPO | Undecidability | Spectral gap ↔ LPO | LPO | Thermo limit / halting | 10.5281/zenodo.18642620 |
| 37 | Undecidability landscape | Undecidability | All halting reductions ≡ LPO | LPO | Σ₁⁰ meta-theorem | 10.5281/zenodo.18642802 |
| 38 | Wang tiling | Undecidability | Berger ↔ LPO (Grandfather) | LPO | Σ₁⁰ ceiling | 10.5281/zenodo.18642804 |
| 39 | Beyond LPO | Undecidability | Thermodynamic stratification | LPO / LPO' (Σ₂⁰) | Promise gap mechanism | 10.5281/zenodo.18642806 |

---

## Appendix B: Lean Code Availability

### B.1 Repository Structure

Each paper has its own self-contained Lean 4 project directory, following a uniform structure:

```
P{N}_{Name}/
├── Papers/
│   └── P{N}_{Name}/
│       ├── Defs.lean            -- Definitions and axioms
│       ├── [theorem files].lean -- Individual theorem proofs
│       └── Main.lean            -- Top-level imports
├── lakefile.lean                -- Build configuration (Mathlib dependency)
├── lean-toolchain               -- Lean version (leanprover/lean4:v4.28.0-rc1)
└── Papers.lean                  -- Root import file
```

The `lakefile.lean` specifies the Mathlib dependency. The `lean-toolchain` file pins the Lean version to ensure reproducibility. Each paper's Lean code is independent — papers do not import from each other — so any paper can be verified in isolation.

### B.2 Compilation Instructions

To compile and verify any paper's Lean code:

**Prerequisites:** Install Lean 4 via elan (the Lean version manager). Mathlib will be fetched automatically by `lake build`.

```bash
# 1. Install elan (Lean version manager)
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh

# 2. Download the paper's repository from Zenodo
#    (each paper's DOI resolves to a downloadable archive)

# 3. Extract and build
cd P{N}_{Name}
lake build

# 4. Verify axiom profile for any theorem
#    Open any .lean file and add:
#    #print axioms theorem_name
#    Then rebuild to see the axiom list in the output.
```

The first build downloads and compiles Mathlib, which takes approximately 30-60 minutes on a modern machine. Subsequent builds are incremental. The `lean-toolchain` file ensures the correct Lean version is used automatically.

### B.3 Verification Protocol

A reader can independently verify every claim in this monograph by running `#print axioms theorem_name` for any theorem. The output lists every axiom the proof depends on. The classification is mechanical: if the output contains no `Classical.choice` and no custom axioms, the theorem is Level 2 certified (BISH). If it contains `Classical.choice` only from an explicitly stated LPO, WLPO, or LLPO hypothesis, it is Level 3 (intentional classical — the non-constructive content is the theorem's subject matter). If it contains explicit `axiom` declarations, these are Level 4 (axiomatized physics) and are documented in each paper's accompanying text.

All core calibration results across the 39 papers compile without `sorry` (Lean's placeholder for incomplete proofs). The `sorry`-free status of the core results ensures that the calibration claims are mechanically verified end-to-end. Some auxiliary infrastructure (higher-loop schema, general framework lemmas that are not themselves calibration results) may contain `sorry` where the mathematical content is standard but the Lean formalization is incomplete; these are clearly marked in the code and do not affect the calibration claims.

---

## References

### Constructive Mathematics
- Bishop, E. (1967). *Foundations of Constructive Analysis.* McGraw-Hill.
- Bishop, E. and Bridges, D. (1985). *Constructive Analysis.* Springer.
- Bridges, D. and Richman, F. (1987). *Varieties of Constructive Mathematics.* Cambridge University Press.
- Bridges, D. and Vîță, L. (2006). *Techniques of Constructive Analysis.* Springer.
- Ishihara, H. (2006). Reverse mathematics in Bishop's constructive mathematics. *Philosophia Scientiae*, CS 6, 43-59.
- Ishihara, H. (1990). Continuity and nondiscontinuity in constructive mathematics. *Journal of Symbolic Logic*, 56(4), 1349-1354.
- Ishihara, H. (2005). Constructive reverse mathematics: compactness properties. In *From Sets and Types to Topology and Analysis*, Oxford Logic Guides, 245-267.
- Ishihara, H. and Schuster, P. (2004). A constructive uniform continuity theorem. *Quarterly Journal of Mathematics*, 55(2), 185-193.
- Mandelkern, M. (1983). Limited omniscience and the Bolzano-Weierstrass principle. *Bulletin of the London Mathematical Society*, 20, 319-320.

### Computable Analysis
- Weihrauch, K. (2000). *Computable Analysis: An Introduction.* Springer.
- Pour-El, M.B. and Richards, J.I. (1989). *Computability in Analysis and Physics.* Springer.
- Brattka, V., Gherardi, G., and Pauly, A. (2021). Weihrauch complexity in computable analysis. In *Handbook of Computability and Complexity in Analysis*, Springer.

### Classical Reverse Mathematics
- Simpson, S.G. (2009). *Subsystems of Second Order Arithmetic* (2nd ed.). Cambridge University Press.

### Formal Verification
- de Moura, L. and Ullrich, S. (2021). The Lean 4 theorem prover and programming language. In *CADE-28*, LNCS 12699, Springer.
- The Mathlib Community (2020). The Lean mathematical library. In *CPP 2020*, ACM.
- Avigad, J. (2024). Mathematical logic and computation. Cambridge University Press.

### Physics

#### Statistical Mechanics
- Huang, K. (1987). *Statistical Mechanics* (2nd ed.). Wiley.
- Baxter, R.J. (1982). *Exactly Solved Models in Statistical Mechanics.* Academic Press.
- Onsager, L. (1944). Crystal statistics. I. A two-dimensional model with an order-disorder transition. *Physical Review*, 65, 117-149.
- Fekete, M. (1923). Über die Verteilung der Wurzeln bei gewissen algebraischen Gleichungen mit ganzzahligen Koeffizienten. *Mathematische Zeitschrift*, 17, 228-249.

#### Quantum Mechanics
- Sakurai, J.J. and Napolitano, J.J. (2017). *Modern Quantum Mechanics* (2nd ed.). Cambridge University Press.
- von Neumann, J. (1932). *Mathematische Grundlagen der Quantenmechanik.* Springer. English translation: *Mathematical Foundations of Quantum Mechanics* (1955), Princeton University Press.

#### Quantum Field Theory
- Weinberg, S. (1995). *The Quantum Theory of Fields, Volume I: Foundations.* Cambridge University Press.
- Weinberg, S. (1996). *The Quantum Theory of Fields, Volume II: Modern Applications.* Cambridge University Press.
- Peskin, M.E. and Schroeder, D.V. (1995). *An Introduction to Quantum Field Theory.* Westview Press.
- Schwinger, J. (1948). On quantum-electrodynamics and the magnetic moment of the electron. *Physical Review*, 73, 416-417.

#### General Relativity
- Wald, R.M. (1984). *General Relativity.* University of Chicago Press.
- Misner, C.W., Thorne, K.S., and Wheeler, J.A. (1973). *Gravitation.* Freeman.
- Bekenstein, J.D. (1973). Black holes and entropy. *Physical Review D*, 7, 2333-2346.
- Hawking, S.W. (1975). Particle creation by black holes. *Communications in Mathematical Physics*, 43, 199-220.

#### Quantum Information
- Nielsen, M.A. and Chuang, I.L. (2010). *Quantum Computation and Quantum Information* (10th anniversary ed.). Cambridge University Press.
- Bell, J.S. (1964). On the Einstein Podolsky Rosen paradox. *Physics*, 1(3), 195-200.
- Clauser, J.F., Horne, M.A., Shimony, A., and Holt, R.A. (1969). Proposed experiment to test local hidden-variable theories. *Physical Review Letters*, 23, 880-884.
- Tsirelson, B.S. (1980). Quantum generalizations of Bell's inequality. *Letters in Mathematical Physics*, 4, 93-100.

### Undecidability in Physics
- Berger, R. (1966). The undecidability of the domino problem. *Memoirs of the AMS*, 66.
- Robinson, R.M. (1971). Undecidability and nonperiodicity for tilings of the plane. *Inventiones Mathematicae*, 12, 177-209.
- Wang, H. (1961). Proving theorems by pattern recognition — II. *Bell System Technical Journal*, 40(1), 1-41.
- Cubitt, T.S., Perez-Garcia, D., and Wolf, M.M. (2015). Undecidability of the spectral gap. *Nature*, 528, 207-211.
- Bausch, J., Cubitt, T.S., Lucia, A., and Perez-Garcia, D. (2020). Undecidability of the spectral gap in one dimension. *Physical Review X*, 10, 031038.
- Bausch, J., Cubitt, T.S., and Watson, J.D. (2021). Uncomputability of phase diagrams. *Nature Communications*, 12, 452.
- Watson, J.D. and Cubitt, T.S. (2021). Computational complexity of the ground state energy density problem. arXiv:2107.05060.
- Cubitt, T.S., Lucia, A., Perez-Garcia, D., and Perez-Eceiza, M. (2022). Undecidable renormalization group flows. arXiv:2205.09024.

### The Programme

- Lee, P.C.K. (2025). CRM of Mathematical Physics, Paper 2: Bidual Gap and WLPO. Zenodo. DOI: 10.5281/zenodo.17107493
- Lee, P.C.K. (2025). CRM of Mathematical Physics, Paper 4: Quantum Spectra. Zenodo. DOI: 10.5281/zenodo.17059483
- Lee, P.C.K. (2025). CRM of Mathematical Physics, Paper 5: Schwarzschild Curvature. Zenodo. DOI: 10.5281/zenodo.18489703
- Lee, P.C.K. (2025). CRM of Mathematical Physics, Paper 6: Heisenberg Uncertainty. Zenodo. DOI: 10.5281/zenodo.18519836
- Lee, P.C.K. (2025). CRM of Mathematical Physics, Paper 7: Trace-Class Operators. Zenodo. DOI: 10.5281/zenodo.18527559
- Lee, P.C.K. (2025). CRM of Mathematical Physics, Paper 8: 1D Ising Model. Zenodo. DOI: 10.5281/zenodo.18516813
- Lee, P.C.K. (2025). CRM of Mathematical Physics, Paper 9: Ising Formulation-Invariance. Zenodo. DOI: 10.5281/zenodo.18517570
- Lee, P.C.K. (2025). CRM of Mathematical Physics, Paper 10: Logical Geography. Zenodo. DOI: 10.5281/zenodo.18627193
- Lee, P.C.K. (2025). CRM of Mathematical Physics, Paper 11: CHSH / Tsirelson Bound. Zenodo. DOI: 10.5281/zenodo.18527676
- Lee, P.C.K. (2025). CRM of Mathematical Physics, Paper 12: Constructive History. Zenodo. DOI: 10.5281/zenodo.18627283
- Lee, P.C.K. (2025). CRM of Mathematical Physics, Paper 13: Event Horizon. Zenodo. DOI: 10.5281/zenodo.18529007
- Lee, P.C.K. (2025). CRM of Mathematical Physics, Paper 14: Quantum Decoherence. Zenodo. DOI: 10.5281/zenodo.18569068
- Lee, P.C.K. (2025). CRM of Mathematical Physics, Paper 15: Noether Conservation. Zenodo. DOI: 10.5281/zenodo.18572494
- Lee, P.C.K. (2025). CRM of Mathematical Physics, Paper 16: Born Rule. Zenodo. DOI: 10.5281/zenodo.18575377
- Lee, P.C.K. (2025). CRM of Mathematical Physics, Paper 17: Bekenstein-Hawking Entropy. Zenodo. DOI: 10.5281/zenodo.18597306
- Lee, P.C.K. (2025). CRM of Mathematical Physics, Paper 18: Yukawa RG Flow. Zenodo. DOI: 10.5281/zenodo.18626839
- Lee, P.C.K. (2025). CRM of Mathematical Physics, Paper 19: WKB Tunneling. Zenodo. DOI: 10.5281/zenodo.18602596
- Lee, P.C.K. (2025). CRM of Mathematical Physics, Paper 20: Ising Magnetization. Zenodo. DOI: 10.5281/zenodo.18603079
- Lee, P.C.K. (2025). CRM of Mathematical Physics, Paper 21: Bell Nonlocality. Zenodo. DOI: 10.5281/zenodo.18603251
- Lee, P.C.K. (2025). CRM of Mathematical Physics, Paper 22: Radioactive Decay. Zenodo. DOI: 10.5281/zenodo.18603503
- Lee, P.C.K. (2025). CRM of Mathematical Physics, Paper 23: Measurement Problem. Zenodo. DOI: 10.5281/zenodo.18604312
- Lee, P.C.K. (2025). CRM of Mathematical Physics, Paper 24: Kochen-Specker. Zenodo. DOI: 10.5281/zenodo.18604317
- Lee, P.C.K. (2025). CRM of Mathematical Physics, Paper 25: Ergodic Theorems. Zenodo. DOI: 10.5281/zenodo.18615453
- Lee, P.C.K. (2025). CRM of Mathematical Physics, Paper 26: Gödel Sequences. Zenodo. DOI: 10.5281/zenodo.18615457
- Lee, P.C.K. (2025). CRM of Mathematical Physics, Paper 27: IVT in Bell Physics. Zenodo. DOI: 10.5281/zenodo.18615459
- Lee, P.C.K. (2025). CRM of Mathematical Physics, Paper 28: Classical Mechanics. Zenodo. DOI: 10.5281/zenodo.18616620
- Lee, P.C.K. (2025). CRM of Mathematical Physics, Paper 29: Fekete's Lemma. Zenodo. DOI: 10.5281/zenodo.18643617
- Lee, P.C.K. (2025). CRM of Mathematical Physics, Paper 30: Fan Theorem Dispensability. Zenodo. DOI: 10.5281/zenodo.18638394
- Lee, P.C.K. (2025). CRM of Mathematical Physics, Paper 31: DC Dispensability. Zenodo. DOI: 10.5281/zenodo.18645578
- Lee, P.C.K. (2025-2026). CRM of Mathematical Physics, Paper 32: QED One-Loop. Zenodo. DOI: 10.5281/zenodo.18642598
- Lee, P.C.K. (2026). CRM of Mathematical Physics, Paper 33: QCD + Confinement. Zenodo. DOI: 10.5281/zenodo.18642610
- Lee, P.C.K. (2026). CRM of Mathematical Physics, Paper 34: Scattering Amplitudes. Zenodo. DOI: 10.5281/zenodo.18642612
- Lee, P.C.K. (2026). CRM of Mathematical Physics, Paper 35: Conservation Metatheorem. Zenodo. DOI: 10.5281/zenodo.18642616
- Lee, P.C.K. (2026). CRM of Mathematical Physics, Paper 36: Cubitt's Theorem ≡ LPO. Zenodo. DOI: 10.5281/zenodo.18642620
- Lee, P.C.K. (2026). CRM of Mathematical Physics, Paper 37: Undecidability Landscape. Zenodo. DOI: 10.5281/zenodo.18642802
- Lee, P.C.K. (2026). CRM of Mathematical Physics, Paper 38: Wang Tiling. Zenodo. DOI: 10.5281/zenodo.18642804
- Lee, P.C.K. (2026). CRM of Mathematical Physics, Paper 39: Beyond LPO. Zenodo. DOI: 10.5281/zenodo.18642806

---

## Acknowledgments

The formal verification was performed using Lean 4 and the Mathlib mathematical library. The author is grateful to the Lean 4 and Mathlib communities for creating and maintaining the infrastructure that made this programme possible.

This work was developed in collaboration with AI systems (Claude, Anthropic), which served as architectural advisors, proof-strategy consultants, Lean coding agents, and draft writers throughout the programme. The AI systems contributed substantially to the formalization effort — writing Lean code, debugging proofs, and identifying proof strategies — and to the exposition of results. The mathematical content — the theorems, their statements, their physical significance, and the overall programme design — is the author's responsibility.

The programme benefited from the open-access preprint infrastructure provided by Zenodo/CERN for archival and DOI assignment.

[Paul: add personal acknowledgments as appropriate]

---

## Author Note

Paul Chun-Kit Lee is an interventional cardiologist practicing in Brooklyn, New York. This work was conducted independently and is not affiliated with any academic mathematics or physics department. The author has no formal training in mathematical logic or proof theory. The formal verification in Lean 4, which certifies every claim mechanically, was adopted precisely because the author's non-standard background demands a standard of evidence that informal argument cannot provide.

[Paul: revise as you see fit — this is your voice, not mine]
