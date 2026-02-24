# Paper 18 Discussion: The Fermion Mass Hierarchy and the Limits of CRM as a Generative Methodology

**Date:** February 2026  
**Context:** Working notes for the Constructive Reverse Mathematics series  
**Status:** Internal discussion document, not a draft

---

## 1. What We Tried To Do

The CRM programme has established, across five independent physics domains (Papers 8, 13, 14, 15, 17), that the passage from finite computation to completed infinite limit costs exactly LPO via Bounded Monotone Convergence. Every domain follows the same pattern: the finite-stage computation is BISH, the completed limit costs LPO, and the LPO is dispensable because no experiment can distinguish the limit from a sufficiently close finite approximation.

After Paper 17 (black hole entropy — the fifth LPO domain), we asked a different question: **can CRM thinking be used generatively, not just diagnostically?** Instead of calibrating the logical cost of known physics, could the CRM framework reveal new mechanisms or new approaches to open problems?

The test case was the fermion mass hierarchy — one of the deepest open problems in particle physics. The Standard Model has 13 free parameters in the Yukawa sector (9 fermion masses, 3 CKM mixing angles, 1 CP phase), spanning six orders of magnitude from the electron Yukawa (~2×10⁻⁶) to the top Yukawa (~1). The Higgs mechanism explains *how* particles acquire mass (Yukawa coupling × vacuum expectation value), but not *why* the couplings have their observed values.

The specific hypothesis was:

> The fermion mass problem may be unsolved not because it is hard, but because it is being asked in the wrong logical register. The physics community searches for LPO-level explanations (exact symmetries, all-orders cancellations, continuous flows to fixed points) of a phenomenon that may only have a BISH-level explanation (finite algebraic structure, approximate relations, few-order perturbative effects). CRM thinking — specifically, the discipline of stripping away LPO scaffolding to find the BISH content — might reveal mechanisms invisible to the conventional approach.

---

## 2. The CRM Analysis of Existing Approaches

Before any numerical work, we applied CRM calibration to the five main approaches to the fermion mass problem. This analysis is, we believe, original — nobody has examined the mass problem through a constructive lens.

### 2.1 Flavor Symmetries (A₄, S₄, SU(3) family groups)

These models postulate discrete or continuous symmetry groups broken by flavon vacuum expectation values. The symmetry constrains the Yukawa matrix structure; the flavon VEVs determine the entries.

**CRM verdict: BISH explaining BISH.** Finite group representation theory, flavon potential minimization, Yukawa matrix derivation — all finite algebra. These models *replace* 13 unexplained BISH parameters (Yukawa couplings) with 8–12 unexplained BISH parameters (flavon VEVs, symmetry-breaking couplings). The logical cost is unchanged. The parameters are reorganized, not derived. Compression, not explanation.

### 2.2 Extra Dimensions (Randall-Sundrum)

The mass hierarchy arises from exponential warp factors in 5D geometry. Fermions localized at different positions in the extra dimension have exponentially different overlap integrals with the Higgs brane, producing exponentially different effective Yukawa couplings from O(1) bulk mass parameters.

**CRM verdict: BISH explaining BISH.** The 5D metric solution (ODE with boundary conditions), fermion zero-mode profiles (eigenvalue problem on compact interval), and overlap integrals are all BISH computations. The bulk mass parameters c_i are unexplained inputs. Better compression than flavor symmetries (mild O(1) spread → exponential hierarchy via geometry), but parameters are moved, not eliminated.

**Exception:** If the geometry is derived from string theory with a unique or finite vacuum selection, the derivation stays BISH. If landscape minimization over 10⁵⁰⁰ vacua is required, the computation is formally BISH (finite enumeration) but practically intractable, and anthropic selection operates at a different logical level from physics prediction.

### 2.3 Radiative Mass Generation

Only the top quark gets a tree-level Yukawa coupling; lighter fermion masses arise from loop corrections. The hierarchy comes from loop suppression factors: each loop order is suppressed by α/(4π) ≈ 10⁻³, so successive generations are lighter by roughly three orders of magnitude.

**CRM verdict: BISH with the best compression ratio.** One-loop Feynman diagrams are finite integrals. The hierarchy from loop suppression at successive orders is algebraic. A universal Yukawa coupling plus perturbative expansion structure generates six orders of magnitude from a single input. This is the most constructively natural explanation — largest output from smallest logical input.

**Problem:** Empirical, not logical. The additional particles required by radiative generation models have not been observed. But the logical structure is the cleanest.

### 2.4 The Koide Formula

The charged lepton masses satisfy Q = (m_e + m_μ + m_τ)/(√m_e + √m_μ + √m_τ)² = 2/3 to extraordinary precision (~10⁻⁵). The formula was originally derived from a preon model (now ruled out). Sumino's explanation invokes a U(3)×SU(2) family gauge symmetry whose radiative corrections exactly cancel QED corrections to preserve the relation at all energy scales.

**CRM verdict: Empirically BISH, explanation requires LPO.** Checking Q = 2/3 is finite arithmetic. But Sumino's all-orders cancellation (family gauge + QED corrections cancel exactly to every order in perturbation theory) is a completed infinite statement — it requires LPO. The circulant matrix structure underlying Koide (√m_n = μ[1 + √2 cos(δ + 2πn/3)] with δ ≈ 2/9) is BISH — finite Fourier analysis on ℤ₃.

**Key insight:** The phase δ = 2/9 is a single rational number. If it could be derived from some algebraic property of the Standard Model gauge group at finite loop order, the entire charged lepton mass spectrum would follow from one rational parameter. This is the maximally compressed form of the mass problem for three particles.

### 2.5 The Landscape / Anthropic Approach

The Yukawa couplings are environmental parameters, determined by which string vacuum we inhabit among ~10⁵⁰⁰ possibilities. No dynamical explanation exists; the values are selected by the anthropic requirement that observers exist.

**CRM verdict: Undefined in the CRM framework.** If the landscape is finite (10⁵⁰⁰ vacua), enumeration is BISH in principle (though intractable). The anthropic filter is a finite predicate. But the landscape makes no prediction — it is post-hoc rationalization. CRM calibrates predictions ("given inputs, output is X"), not meta-theories about parameter contingency. The landscape operates at a different logical level from physics.

### 2.6 Summary Table

| Approach | Logical Cost | Unexplained Inputs | Compression |
|---|---|---|---|
| Standard Model (raw) | BISH | 13 Yukawa couplings | None |
| Flavor symmetries | BISH | 8–12 flavon parameters | Modest |
| Randall-Sundrum | BISH | ~6 bulk masses + geometry | Good |
| Radiative generation | BISH | ~1 universal Yukawa | Best |
| Koide (empirical) | BISH | 2 parameters (μ, δ) | Maximal (for 3 masses) |
| Koide (Sumino mechanism) | LPO | 0 (if mechanism works) | Complete, but costs LPO |
| Landscape | BISH (formally) | 0 (but no prediction) | Undefined |

**The critical observation:** Every approach operates within BISH. CRM doesn't discriminate at the level of logical cost — all BISH. What it reveals is that approaches differ in *compression ratio* (unexplained parameters needed to produce the 13 observables). The mass problem is entirely a problem within BISH. No omniscience principle is needed. The mystery is which BISH computation nature performs — a different kind of mystery from the ones CRM was designed to illuminate (where LPO enters and whether it's dispensable).

---

## 3. The Radical Hypothesis: LPO Scaffolding Constrains the Search Space

The analysis above led to a more specific hypothesis. Consider Sumino's mechanism for the Koide formula: he needs the all-orders cancellation (LPO) so that Q = *exactly* 2/3. But the right question might be: "Why is Q = 2/3 to measurable precision at any finite loop order we can compute?" (BISH). These are different questions. The BISH version, freed from the constraint of exact all-orders cancellation, might admit mechanisms the LPO version excludes.

More generally: **the demand for exact mathematical results in physics imposes constraints that may be artifacts of formalism rather than reflections of nature.** When CRM strips away LPO scaffolding, the BISH content that remains is sometimes structurally different — not just "the same thing minus the limit," but a reorganized object with different properties.

Applied to the RG: the standard treatment of renormalization group evolution is as a continuous flow — an ODE integrated from one scale to another, with the solution understood as a limit. This is LPO (continuous flow = completed limit of discrete steps). The BISH content is the discrete map at finite step count. Nobody studies the discrete map as an object in its own right because the continuous flow is the standard tool.

**The specific prediction:** The Standard Model's Yukawa beta functions, treated as a finite discrete map from the Planck scale to the electroweak scale, might contain quasi-fixed-point structure that produces the observed mass hierarchy. The structure would be visible at finite loop order and finite step count — entirely BISH — but invisible in the continuous-flow formalism because the continuous flow imposes additional structure (smoothness, differentiability, convergence) that masks the finite-order algebraic content.

This was the hypothesis we tested numerically.

---

## 4. What We Found

### 4.1 The Computation

We implemented the one-loop Standard Model beta functions for all 9 Yukawa couplings and 3 gauge couplings as a discrete RK4 map from the Planck scale (10¹⁹ GeV) to the electroweak scale (91.2 GeV). We scanned 3,000 random initial conditions (Yukawa couplings log-uniform on [0.01, 10]) and tracked mass ratios, Koide's Q, and attractor structure. We compared results at N = 10, 50, 100, 1000, and 10000 discrete steps, and against scipy's continuous ODE integrator.

### 4.2 Results

**Q1 — Top quasi-fixed-point:** CONFIRMED. y_t(EW) converges to ~1.29 for y_t(Planck) ∈ [0.72, 10] — 58% of the scan range. The overshoot (1.29 vs observed 0.99) is a known artifact of one-loop running. The QFP itself is robust.

**Q2 — Bottom/tau ratio:** WEAK STRUCTURE. Median y_b/y_τ = 2.25 (observed: 2.35), tantalizingly close. But the distribution is broad (std = 19.7), with only 6% of initial conditions within 20% of the observed ratio. This is a preferred region, not a strong attractor. The well-known b-τ unification prediction of SU(5) GUTs is partially visible as a statistical tendency rather than a fixed-point.

**Q3 — Full mass hierarchy attractor:** NOT FOUND. 0 out of 3,000 random initial conditions produce the full hierarchy (all 8 mass ratios within one order of magnitude of observed). The one-loop SM Yukawa RG does not generate inter-generational mass ratios from generic UV conditions. The mass hierarchy is UV-sensitive — it requires input from whatever physics operates at the Planck scale.

**Q4 — Koide from RG:** REQUIRES FINE-TUNING. Mean Q = 0.50, far from 2/3. Only 3.2% of filtered samples land within 1% of 2/3. The Koide relation does not emerge generically from SM RG evolution; it is a property of the specific mass values, not of the dynamical system that produces them.

**Q5 — Discrete map vs continuous flow:** BISH STRUCTURE VISIBLE AT N=10. The top QFP basin is already visible with just 10 RK4 steps. At N=50, the discrete map matches scipy's continuous solution to <0.01%. The QFP is a genuine property of the finite-order discrete map. However — and this is the critical finding — **the discrete map reveals the same structure as the continuous flow, not new structure.** The BISH formulation is more efficient but not more informative. There are no hidden quasi-fixed-points visible at finite N that disappear in the continuous limit.

### 4.3 Score: 1/5 Success Criteria Met

The one success (Q5: BISH structure visible at coarse discretization) confirms the CRM programme's general claim that physically relevant computations are BISH-computable. The four failures refute the specific hypothesis that CRM thinking would reveal new mechanisms for the mass hierarchy.

---

## 5. What This Means for the Programme

### 5.1 The Radical Hypothesis Is Refuted

The hope was that stripping LPO scaffolding from the RG would expose mechanisms invisible to the conventional approach. It doesn't. The discrete map and the continuous flow give the same physics. The LPO content of the continuous formulation (the completed flow as a limit of discrete steps) is dispensable — the BISH content suffices — but the BISH content isn't *different*. It's the same content, computed more efficiently.

This means the fermion mass problem is not a problem of logical register. Physicists are looking in the right place; they just haven't found the answer. The masses require UV input that the Standard Model doesn't determine, and no amount of logical reorganization of the SM's infrared dynamics changes that.

### 5.2 CRM Is Diagnostic, Not Generative

The investigation reveals a scope boundary for the CRM programme. CRM is an excellent *diagnostic* tool — it tells you where logical boundaries are, what costs what, which parts of a derivation are dispensable. Papers 8 through 17 demonstrate this convincingly. But CRM is not a *generative* tool — it doesn't produce new physics from logical considerations.

This is not a limitation to be ashamed of. Thermometers don't cook food. The CRM diagnostic is valuable precisely because it gives rigorous answers to well-posed questions about logical structure. Expecting it to also solve the flavor problem was overreach — interesting overreach, worth attempting, but overreach.

### 5.3 The BISH-Only Domain

What the investigation *does* provide is the first domain in the CRM series where everything is BISH and no LPO boundary appears. The five domains in Papers 8–17 all involve bounded monotone sequences whose completed limits cost LPO. The Yukawa RG involves no such sequence. The "flow" from Planck to electroweak is a finite computation — evaluate the beta function a finite number of times, get a number. Nobody needs the continuous flow to *converge*; they just need the output at the electroweak scale.

This means the CRM diagnostic discriminates. It's not rubber-stamping everything as "BISH plus LPO at the limit." Some physics has an LPO boundary (where completed limits carry physical content — thermodynamic limits, geodesic completeness, exact decoherence, global energy conservation, entropy density convergence). Other physics doesn't (where the computation is inherently finite — perturbative RG evaluation at a specific scale).

The discrimination is structural: **LPO appears when physicists assert the existence of a completed limit, and it doesn't appear when the physical prediction requires only a finite computation.** This sounds tautological, but it isn't — it required numerical verification to confirm that the Yukawa RG's finite computation genuinely captures all the physics, with no hidden dependence on the continuous limit.

### 5.4 The Updated Calibration Picture

| Domain | Paper | BISH Content | LPO Content |
|---|---|---|---|
| Statistical Mechanics | 8 | Finite-volume free energy | Thermodynamic limit |
| General Relativity | 13 | Finite-time geodesic | Geodesic incompleteness |
| Quantum Measurement | 14 | Finite-step decoherence bound | Exact decoherence |
| Conservation Laws | 15 | Local energy conservation | Global energy |
| Quantum Gravity | 17 | Finite entropy count | Entropy density limit |
| **Particle Physics (RG)** | **18** | **Finite-step Yukawa evolution** | **None** |

The sixth row — all BISH, no LPO — completes the diagnostic picture. The LPO boundary is not universal. It appears specifically when the physics involves a passage from finite approximation to completed infinite limit. When the physics is inherently finite (evaluate a perturbative computation at a specific scale), no LPO is needed, and the diagnostic correctly reports this.

---

## 6. Material Worth Preserving

### 6.1 The CRM Analysis of the Mass Problem (§2 above)

The calibration of existing approaches to the fermion mass problem — flavor symmetries as "BISH explaining BISH," radiative generation as "best compression ratio," Koide's formula as "empirically BISH but explanation requires LPO" — is, as far as we know, original. Nobody has examined these approaches through a constructive lens. Even though the analysis didn't lead to new physics, it provides a useful framework for comparing approaches: they all operate within BISH but differ in compression ratio. This material could appear in the technical note, in an updated Paper 10, or in a discussion paper about CRM methodology.

### 6.2 The LPO Scaffolding Insight

The observation that Sumino needs LPO for exact all-orders cancellation, but the physically relevant question (why is Q ≈ 2/3 to observed precision at finite loop order?) is BISH — this is a genuine methodological insight even though it didn't produce a concrete mechanism. The general principle — that demanding exact results imposes constraints that may be artifacts of formalism — deserves articulation even if the specific application to the mass hierarchy was negative.

### 6.3 The Compression Ratio Concept

The idea that CRM can measure *compression* (how many unexplained parameters a theory needs to produce the observables) even when all approaches have the same logical cost (BISH) extends the programme's toolkit beyond the LPO/WLPO/BISH classification. This is a finer-grained diagnostic that might be useful for domains where everything is BISH but some explanations are "better" than others in a formal sense.

---

## 7. Recommended Output

**Technical Note 18** (4–5 pages): "A BISH-Complete Domain: Yukawa Renormalization as a Finite Discrete Map." Frame around the discrimination argument (§5.3). Include Q1 and Q5 as positive findings, Q3 as clean negative, Q2 and Q4 as secondary. Three plots: QFP convergence, N=10 vs continuous comparison, hierarchy scatter. Python script on repository. No Lean (nothing to formalize).

**Material for Paper 10 revision or capstone:** The CRM analysis of existing mass-problem approaches (§2), the compression ratio concept (§6.3), and the updated calibration table (§5.4) with the sixth BISH-only row.

**Archive:** This discussion document and the conversation transcript preserve the full intellectual arc — the hypothesis, the analysis, the computation, and the honest assessment of what worked and what didn't. This is the kind of negative result that is more informative than many positive results, and the reasoning behind it should not be lost.

---

## 8. Final Assessment

We set out to test whether CRM thinking could generate new physics. It can't — or at least, it didn't here. What it can do is provide a rigorous diagnostic framework for understanding the logical structure of existing physics, including a formal basis for comparing different explanations of the same phenomena. The fermion mass investigation confirmed the programme's diagnostic power (the BISH/LPO classification works, the boundary falls where the theory predicts) while establishing the limits of its generative ambition.

The five-domain LPO pattern from Papers 8–17 is real, and Paper 18's BISH-only domain sharpens it: **LPO enters physics through completed limits and nowhere else.** That's a structural finding about mathematical physics as a discipline. It's not as exciting as discovering why the electron weighs what it weighs. But it's true, it's precise, and it's formally verified. In a field where most claims are none of these things, that counts for something.
