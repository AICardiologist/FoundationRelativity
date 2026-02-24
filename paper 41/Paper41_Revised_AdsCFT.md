# Paper 41 (Revised) — The Diagnostic in Action: Axiom Calibration of the AdS/CFT Correspondence

## Abstract

We apply the axiom calibration framework of constructive reverse mathematics to the AdS/CFT correspondence, specifically the Ryu-Takayanagi (RT) formula for holographic entanglement entropy. We show that the holographic dictionary is a *logical isomorphism*: bulk and boundary computations of the same physical observable carry identical axiom cost at every level examined. In the simplest case (vacuum AdS₃), both sides are BISH. In the thermal case (BTZ black hole), the continuous entropy observable remains BISH on both sides, with LLPO entering only for discrete phase classification — and even this cost vanishes for BTZ by symmetry, arising only for generic asymptotically AdS geometries. The FLM quantum correction preserves the BISH calibration for free fields in AdS₃. For the quantum extremal surface (QES) prescription, the Fan Theorem cost of variational existence is strictly scaffolding: the boundary-observable entropy is computable at BISH+LPO without locating the bulk surface, and in the perturbative regime the surface itself is BISH-constructible via the Jacobi equation. The central finding is that holography *projects away* the non-constructive cost of bulk geometry: the Fan Theorem builds the Platonic surface in the unobservable bulk; BISH computes the observable entropy on the boundary.

This paper is the 41st in a programme of constructive reverse mathematics of mathematical physics. It transforms the programme from a completed classification exercise into an active diagnostic tool, applied to the most important open problem in theoretical physics.


## §1. Introduction: From Classification to Diagnosis

Papers 1–39 established that the logical resources required for all empirical predictions in known physics are exactly BISH+LPO. Paper 40 defended this claim against objections and showed the framework has diagnostic power: it distinguishes physical content from mathematical scaffolding. This paper demonstrates that power in action.

The target is the AdS/CFT correspondence — specifically, the Ryu-Takayanagi formula and its quantum extensions. The choice is strategic. AdS/CFT is the most active area of theoretical physics. The RT formula is its most cited result. The Page curve and island formula are its most debated recent developments. A diagnostic tool that provides new information about these problems has a natural audience.

The diagnostic question is simple: *does the holographic dictionary preserve axiom cost?* The correspondence claims that bulk gravitational physics and boundary conformal field theory compute the same physics. Our framework can check whether they compute it at the same logical cost. If yes, the duality is logically transparent. If no, the axiom gap identifies places where the duality performs non-trivial logical work — and these are candidates for where the correspondence might fail or require modification.


## §2. A Necessary Distinction: Observables vs. Decisions

Before presenting the calibrations, we must sharpen a distinction that refines the programme's prior treatment of phase transitions.

The programme has consistently attributed LPO cost to phase transitions, via the Fekete mechanism (Paper 29: Fekete's Subadditive Lemma ≡ LPO). This is correct but requires disambiguation. There are two logically distinct operations at a phase transition:

**The observable computation.** Computing the numerical value of the order parameter, the free energy, or the entropy as a function of the control parameter (temperature, angle, etc.). This is a question about a continuous real-valued function.

**The phase decision.** Declaring which phase the system is in — asserting "the system is in phase A" or "the system is in phase B" as a Boolean classification.

These have different axiom costs, and the difference is physically meaningful.

The Fekete mechanism (Paper 29) concerns the *existence* of a thermodynamic limit — proving that the free energy density f = lim_{N→∞} F_N/N exists as a real number. The sequence F_N/N is subadditive and bounded, so its limit exists by Fekete's lemma. But Fekete's lemma is equivalent to LPO over BISH. The LPO cost is in *computing the limit* — extracting a real number from an infinite sequence whose convergence rate may be non-uniform.

The BTZ entanglement phase transition is a different operation. Both competing quantities — the geodesic lengths L₁(θ) and L₂(θ) — are already in hand as explicit, BISH-computable functions. No limit is required. The entropy is S(A) = min(L₁(θ), L₂(θ)) / 4G_N, and the minimum of two real numbers is BISH-computable via the identity:

    min(x, y) = ½(x + y − |x − y|)

The absolute value function is uniformly continuous, hence BISH-computable. The continuous entropy observable is strictly BISH.

The phase decision — extracting a Boolean flag declaring whether L₁ ≤ L₂ or L₂ ≤ L₁ — is a different matter. For exact real numbers whose difference may be zero, the trichotomy (x < y) ∨ (x = y) ∨ (x > y) is not constructively valid. The weaker disjunction (x ≤ y) ∨ (y ≤ x) is equivalent to LLPO (the Lesser Limited Principle of Omniscience), which is strictly weaker than LPO.

**The reconciliation with Paper 29:** Fekete costs LPO because it computes a limit that does not yet exist as a real number. The BTZ min costs BISH because it selects between values that are already computed. The Fekete mechanism applies when the physical quantity is *defined* by a limit (thermodynamic limit, infinite-volume free energy). The min mechanism applies when the physical quantity is *defined* by a selection (minimum of competing saddle points). These are different mathematical operations with different axiom costs. Both occur at phase transitions, but they contribute differently.

This distinction is not a correction of prior work. It is a *refinement* that becomes visible only when the calibration is applied to a system (BTZ) where the competing quantities are given by closed-form expressions rather than by limits.


## §3. Vacuum AdS₃: The Null Result

### §3.1. Bulk Side

In the Poincaré patch of AdS₃, ds² = (ℓ²/z²)(dz² + dx²), the RT geodesic connecting boundary points (x₁, 0) and (x₂, 0) is a semicircle of radius R = |x₂ − x₁|/2. Its regularized length is:

    L_reg = 2ℓ log(|x₂ − x₁|/ε)

This is an explicit algebraic expression. No variational principle, no compactness, no limit. **Calibration: BISH.**

### §3.2. Boundary Side

The Calabrese-Cardy formula for entanglement entropy of an interval of length ℓ_A in a 2d CFT vacuum state:

    S(A) = (c/3) log(ℓ_A/ε)

Derived via the replica trick: (a) twist operator correlation function for integer n — algebraic, BISH; (b) analytic continuation n → 1 — explicit formula via Carlson's theorem, BISH; (c) differentiation at n = 1 — elementary, BISH. **Calibration: BISH.**

### §3.3. The Matching

Both sides yield the same formula under the Brown-Henneaux identification c = 3ℓ/(2G_N). Both calibrate at BISH. The duality, for this prediction, is a BISH-to-BISH map. The holographic dictionary performs no logical work — it is an identity between two explicit computations.

This is the null result: the simplest instance of RT involves no non-constructive principles whatsoever. It sets the baseline for the thermal case, where the axiom cost structure becomes non-trivial.


## §4. Thermal BTZ: The Phase Transition

### §4.1. Bulk Side: Competing Geodesics

In the BTZ black hole with horizon radius r₊ and AdS radius ℓ, the two competing RT geodesics for a boundary interval of angular extent θ have lengths:

    L₁(θ) = 2ℓ ln((2R/r₊) sinh(r₊θ/2ℓ))

    L₂(θ) = 2ℓ ln((2R/r₊) sinh(r₊(2π − θ)/2ℓ))

where R is a radial UV cutoff. Both are explicit compositions of elementary functions: logarithm, hyperbolic sine, multiplication. **Both are BISH-computable.**

The entanglement entropy is:

    S(A) = min(L₁(θ), L₂(θ)) / 4G_N

By the identity min(x,y) = ½(x + y − |x − y|), and the BISH-computability of the absolute value function, **the continuous entropy observable is BISH.**

### §4.2. The Critical Angle

The critical angle θ_c where L₁ = L₂ is determined by:

    sinh(r₊θ/2ℓ) = sinh(r₊(2π − θ)/2ℓ)

Since sinh is strictly monotone, this gives θ = 2π − θ, hence **θ_c = π**. This is a trivially computable constant — determined by the symmetry of the BTZ geometry.

Consequence: for the BTZ black hole specifically, even the discrete phase classification is BISH. At θ < π, the short geodesic wins. At θ > π, the long geodesic wins. At θ = π, both have equal length. The comparison is decidable because the crossing point is known exactly.

### §4.3. Generic Asymptotically AdS Black Holes

For a generic asymptotically AdS₃ black hole (with matter fields or higher-derivative corrections deforming the geometry), the competing geodesic lengths L₁(θ) and L₂(θ) remain BISH-computable functions (they are determined by explicit ODEs with BISH-computable coefficients). The continuous entropy min(L₁, L₂) remains BISH.

However, the critical angle θ_c is now determined by the equation L₁(θ_c) = L₂(θ_c), which may not have a closed-form solution. The discrete phase decision — "for this specific θ, is L₁ ≤ L₂ or L₂ ≤ L₁?" — costs **LLPO** when θ is near θ_c and the difference L₁ − L₂ cannot be bounded away from zero.

**Calibration summary for thermal RT:**

| Component | BTZ | Generic asym. AdS |
|---|---|---|
| Geodesic lengths L₁, L₂ | BISH | BISH |
| Entropy observable min(L₁, L₂) | BISH | BISH |
| Phase decision (Boolean flag) | BISH (θ_c = π by symmetry) | LLPO |

### §4.4. Boundary Side: Hawking-Page

The boundary thermal partition function involves the free energy F = min(F_AdS, F_BTZ), where F_AdS and F_BTZ are the free energies of thermal AdS and the BTZ black hole respectively. Both are explicit, BISH-computable functions of the temperature. The continuous free energy is BISH. The topological phase classification (declaring "the dominant saddle is AdS" or "the dominant saddle is BTZ") costs LLPO for generic parameters.

**The duality preserves axiom cost exactly.** On both sides: the continuous observable is BISH; the discrete phase classification is LLPO (or BISH for BTZ by symmetry). The holographic dictionary maps each logical operation to its exact counterpart.


## §5. The FLM Quantum Correction

### §5.1. Setup

The Faulkner-Lewkowycz-Maldacena formula:

    S(A) = Area(γ_A)/4G_N + S_bulk(Σ_A)

For a free massive scalar in AdS₃, the bulk entanglement entropy S_bulk is computed via the replica trick on the bulk fields.

### §5.2. Heat Kernel Analysis

The heat kernel on Euclidean AdS₃ (≅ H³) has the explicit Camporesi form:

    K(t, ρ) ∝ t^{−3/2} (ρ/sinh ρ) exp(−ρ²/4t − m²t)

For the branched cover required by the replica trick, the Sommerfeld method of images produces a sum over geodesics to image points at distances ρ_n. The exponential factor exp(−ρ_n²/4t) guarantees the image sum converges with an explicit, BISH-computable Cauchy modulus (since ρ_n grows linearly with n).

UV regularization: the Seeley-DeWitt coefficients are explicit polynomials of local curvature invariants. Subtracting them from the heat kernel integrand yields a function that is smooth at t = 0 and exponentially decaying at t = ∞. The proper-time integral converges to a BISH-computable real number.

ζ-function regularization: for H³, the spectral ζ-function reduces to an explicit one-dimensional proper-time integral via Mellin transform. The analytic continuation to s = 0 is achieved by algebraic integration-by-parts on the explicit formula, yielding ζ'(0) as a BISH-computable quantity.

**Calibration: S_bulk for a free scalar in the AdS₃ vacuum is BISH.** The FLM quantum correction does not increase the axiom cost beyond the classical RT term.

### §5.3. Significance

This is a non-trivial result. One might expect quantum corrections to introduce LPO cost via infinite mode sums or continuum limits. For free fields in maximally symmetric backgrounds, the explicit heat kernel prevents this. The LPO cost would enter for interacting fields (where the mode sum does not close) or for non-symmetric backgrounds (where the heat kernel is not known in closed form). The paper identifies the precise boundary: **BISH for free fields in symmetric backgrounds; LPO expected for interacting or non-symmetric cases, via the standard mechanism (completed limit with non-uniform convergence).**


## §6. The Quantum Extremal Surface: FT as Scaffolding

### §6.1. The Variational Problem

The Engelhardt-Wall QES prescription:

    S(A) = min_γ [Area(γ)/4G_N + S_bulk(Σ_γ)] = min_γ S_gen(γ)

Existence of the minimizing surface γ* by the direct method of calculus of variations requires extracting a convergent subsequence from a minimizing sequence — a compactness argument costing FT (or its infinite-dimensional analogues, Arzelà-Ascoli or Banach-Alaoglu).

### §6.2. The Scaffolding Mechanism

The key insight, confirmed by the analysis: the boundary CFT does not observe the bulk surface γ*. The holographic dictionary states that the boundary entanglement entropy is the *infimum* of the generalized entropy functional:

    S(A) = inf_γ S_gen(γ)

Constructive mathematics can compute the infimum of a bounded functional over a metric space — a real number — by evaluating the functional on successive approximations and applying bounded monotone convergence (LPO via BMC). The infimum is computable at BISH+LPO even if the exact minimizing surface cannot be located without FT.

**FT builds the Platonic geometric surface in the unobservable bulk. BISH computes the observable entropy on the boundary. Holography projects away the FT cost.**

This is the scaffolding meta-theorem for quantum gravity: the compactness cost of bulk geometric existence is scaffolding for the boundary-observable entropy. The Fan Theorem's role in the QES prescription is identical to its role throughout the programme — it provides an existence proof that can be bypassed when only the numerical prediction is needed.

### §6.3. Perturbative Construction

In the perturbative regime (small G_N corrections), the QES is obtained by perturbing the classical RT surface:

    γ_QES = γ_RT + G_N δγ

The deformation δγ satisfies the Jacobi geodesic deviation equation, an ODE sourced by ∇S_bulk. By Picard-Lindelöf (which is BISH for Lipschitz ODEs — the right-hand side is Lipschitz when the bulk state is sufficiently regular), the perturbed surface is **explicitly BISH-constructible** via successive approximation. No compactness needed, no FT, not even LPO.

**Calibration of QES in the perturbative regime: BISH for the surface itself.**

### §6.4. The Island Formula and the Page Curve

The island formula for the Page curve:

    S(A) = min(S_island, S_no-island)

where S_island and S_no-island are the generalized entropies evaluated on the competing QES surfaces (the "island" saddle and the "no-island" saddle).

By the analysis of §4, the continuous entropy value min(S_island, S_no-island) is **BISH** (minimum of two BISH-computable quantities). The discrete Page time decision — "has the Page time occurred?" — costs **LLPO** for generic parameters (the comparison between S_island and S_no-island at the transition point).

The Page curve itself — the continuous plot of entanglement entropy as a function of time — is a BISH-computable function. Every point on the curve can be computed to arbitrary precision without any omniscience principle. What costs LLPO is the meta-physical assertion "the system has transitioned from the no-island phase to the island phase at this precise moment."


## §7. Complete Calibration Table

| Computation | Bulk cost | Boundary cost | Duality preserves? |
|---|---|---|---|
| **Vacuum AdS₃ RT** | BISH | BISH | ✓ (identity) |
| **BTZ RT (entropy value)** | BISH | BISH | ✓ |
| **BTZ RT (phase decision)** | BISH (θ_c = π) | BISH (by symmetry) | ✓ |
| **Generic thermal RT (entropy value)** | BISH | BISH | ✓ |
| **Generic thermal RT (phase decision)** | LLPO | LLPO | ✓ |
| **FLM correction (free field, vacuum)** | BISH | N/A (bulk-only) | — |
| **FLM correction (free field, thermal)** | BISH | N/A (bulk-only) | — |
| **QES surface existence** | FT (scaffolding) | Not observed | Projected away |
| **QES entropy value (perturbative)** | BISH | BISH | ✓ |
| **QES entropy value (non-perturbative)** | LPO (via infimum/BMC) | LPO (expected) | ✓ (predicted) |
| **Island formula (Page curve value)** | BISH | BISH | ✓ |
| **Island formula (Page time decision)** | LLPO | LLPO | ✓ |

The table's most striking feature: no entry exceeds LPO. The BISH+LPO ceiling holds across the entire holographic dictionary — from the simplest vacuum RT to the quantum-corrected island formula for the information paradox.


## §8. What the Diagnostic Reveals

### §8.1. The Holographic Dictionary is a Logical Isomorphism

For every prediction examined, the bulk and boundary computations carry identical axiom cost. The duality does not perform non-trivial logical work — it maps BISH to BISH, LLPO to LLPO, and (where applicable) LPO to LPO. This is a falsifiable prediction: any future computation where the two sides have different axiom costs would identify a logical obstruction within the correspondence.

### §8.2. Holography Projects Away Compactness

The deepest structural finding: the Fan Theorem cost of bulk geometric existence is invisible to the boundary. The boundary CFT computes the entropy value without ever constructing or observing the bulk surface. The compactness that guarantees the surface exists is scaffolding — necessary for the bulk geometric picture, irrelevant to the boundary observable. This is the holographic principle, restated in the language of constructive reverse mathematics: holography is the projection that eliminates FT.

### §8.3. Phase Transitions are Cheaper Than Expected

The observable entropy at a phase transition is BISH — the minimum of two BISH-computable functions. Only the discrete phase classification costs LLPO, and even this cost vanishes for sufficiently symmetric geometries (BTZ). This refines the programme's prior treatment of phase transitions (Paper 29: Fekete ≡ LPO) by distinguishing two operations: computing a limit (LPO, Fekete mechanism) and selecting a minimum (BISH, min mechanism). Both occur at phase transitions; they contribute different axiom costs.

### §8.4. Practical Recommendations

For theorists working on the Page curve and the information paradox:

The physically meaningful axiom cost of the island formula is the saddle-point competition (BISH for the entropy value; LLPO for the phase decision). The FT cost of QES existence is scaffolding — eliminable in the perturbative regime (Jacobi equation, BISH) and projectable away via holography in the non-perturbative regime (boundary infimum, LPO). Computational effort should be directed at characterizing the competition between island and no-island saddles, not at proving existence of the QES via compactness methods.


## §9. Relation to Prior Work

### §9.1. Reconciliation with Paper 29 (Fekete ≡ LPO)

The BTZ calibration does not contradict Paper 29. The operations are different:

**Fekete mechanism** (Paper 29): The physical quantity is *defined* as a limit — the free energy density f = lim_{N→∞} F_N/N. The limit does not exist as a BISH real number without Fekete's lemma, which costs LPO. The LPO cost is in *computing* a quantity that is not yet in hand.

**Min mechanism** (this paper): The physical quantity is *defined* as a minimum — S(A) = min(L₁, L₂)/4G_N. Both L₁ and L₂ are already BISH-computable. The min operation is BISH. No limit is involved.

Both mechanisms occur at phase transitions. The Fekete mechanism applies when the order parameter is defined by an infinite-volume limit. The min mechanism applies when the order parameter is defined by a competition between finitely many saddle points whose values are already known. The distinction is between *computing a new quantity from a sequence* (LPO) and *selecting among existing quantities* (BISH for the value, LLPO for the decision).

This refinement is invisible in systems where the competing quantities are themselves defined by limits (e.g., the Hawking-Page transition in the full infinite-volume partition function). In such cases, the Fekete LPO cost dominates and the min BISH cost is subsumed. The BTZ RT formula is the first calibration in the programme where the competing quantities are given by closed-form expressions, making the min mechanism visible as a separate, cheaper operation.

### §9.2. Position Relative to Döring-Isham Topos Programme

The Döring-Isham programme replaces Boolean propositions with a Heyting algebra internal to a topos, providing a logical framework for quantum theory. Our calibration operates at a different granularity: rather than replacing the propositional logic of quantum theory, it measures the axiom cost of specific computational steps. The two programmes are complementary. The topos framework explains *why* quantum propositions are non-Boolean; the calibration measures *how much* non-constructivity each physical prediction requires.

### §9.3. Position Relative to Cubitt-Perez-Garcia-Wolf

The undecidability of the spectral gap (Cubitt et al.) established that certain questions about infinite-dimensional quantum systems are formally undecidable. Papers 36–37 showed that this undecidability reduces to LPO. Paper 41 extends this analysis into holography: the bulk geometric questions that might seem to require arbitrarily high logical complexity (existence of minimal surfaces in general spacetimes) are projected away by holography, and the boundary observables remain at BISH+LPO.


## §10. Required Lean 4 Infrastructure

### Bridge Axioms (to be axiomatized):

- BTZ_geodesic_length_short / _long: The explicit formulas for L₁(θ), L₂(θ)
- Camporesi_Heat_Kernel: The explicit heat kernel on H³
- Zeta_Reg_Finite: The regularized trace as an evaluated 1D proper-time integral
- QES_Jacobi_ODE: The Jacobi equation for geodesic deviation sourced by ∇S_bulk
- Euler_Lagrange_Sgen: The Euler-Lagrange equation for the generalized entropy functional

### Theorems to Formalize:

- BTZ_entropy_BISH: min(L₁, L₂) is BISH-computable (via Mathlib's min on reals)
- Phase_decision_LLPO: Extracting a Boolean phase flag is equivalent to LLPO
- FLM_correction_BISH: The bulk entropy for a free scalar in AdS₃ is BISH-computable
- QES_perturbative_BISH: The perturbed QES is constructible via Picard-Lindelöf (BISH)
- Infimum_vs_Minimizer: Formal separation of the observable inf S_gen (BISH+LPO) from the geometric argmin (FT)
- Island_decision_LLPO: The Page time decision is equivalent to LLPO
- Holographic_axiom_preservation: For each bulk-boundary pair, the axiom cost is identical

### Mathlib Dependencies:

- Real.min, abs computability
- Picard-Lindelöf existence theorem
- Basic measure theory for the proper-time integral
- Possibly: iInf for the infimum characterization

### Infrastructure Gaps:

- Differential geometry on pseudo-Riemannian manifolds (not in Mathlib; must be axiomatized)
- Spectral geometry and heat kernel methods (not in Mathlib; must be axiomatized)
- Variational derivatives of functionals (not in Mathlib; Part F may require Paper 42)
