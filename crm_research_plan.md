# CRM Programme: Research Plan Beyond BMC↔LPO

## Strategic Assessment

Papers 8–17 established one robust finding: the BMC↔LPO boundary appears universally across five physics domains (statistical mechanics, general relativity, quantum measurement, conservation laws, quantum gravity). Paper 18 established that this boundary does not appear in the Yukawa RG sector — the flavor problem is entirely BISH. Together, these results delineate the scope of the BMC↔LPO diagnostic: it works where physics makes completed-infinite assertions (limits, exact convergence, all-orders results) and returns negative where the physics is inherently finite (boundary conditions, parameter values).

The programme has been monogamous with one constructive principle (BMC/LPO) and one kind of physical assertion (completed limits). The constructive hierarchy contains several other principles, each corresponding to a different kind of physical assertion. Expanding the programme to these principles opens multiple independent research directions with distinct audiences.

This document maps the feasible next steps, ranked by payoff and feasibility.

---

## The Expanded Toolbox

| Constructive Principle | What It Decides | Physical Analogue | Current CRM Status |
|---|---|---|---|
| BMC↔LPO | Does a bounded monotone sequence converge? | Completed limits (thermo, geodesics, decoherence) | 5 domains calibrated (Papers 8–17) |
| LLPO | Given two sequences, if not both have a 1, which is all-zeros? | Exclusion/incompatibility (Bell, contextuality) | Untouched |
| WLPO | Is a sequence all zeros, or not? | Exact equality/symmetry decisions (SSB, phase classification) | Untouched |
| Markov's Principle | If a real ≠ 0, is it eventually apart from 0? | Detectability (tunneling, dark energy, rare decays) | Untouched |
| Fan Theorem | Does every path through an infinite tree hit a bar? | Uniform/compactness assertions (mass gap, uniform convergence) | Untouched |
| Dependent Choice | Can you select from infinitely many nonempty sets? | Gauge fixing, path integral measure, variational problems | Untouched |

---

## Tier 1: High Payoff, Feasible Now

### 1. LLPO and Bell Inequalities

**Target assertion:** No local hidden variable model reproduces quantum correlations (Bell's theorem).

**CRM framing:** The CHSH inequality derivation assumes that measurement outcomes at two settings have predetermined values satisfying locality. The derivation of the bound |S| ≤ 2 is finite linear algebra — BISH. The quantum violation (|S| = 2√2 for a maximally entangled state) is a finite computation — BISH. The physical conclusion — "at least one measurement setting must lack predetermined values" — is a disjunctive assertion: either setting A fails or setting B fails, but you can't constructively determine which. This is LLPO.

**What CRM adds:** Bell's theorem, read constructively, does not say "local realism is false" (an LEM assertion). It says "the assumption that both settings have predetermined values leads to a computable contradiction" (BISH), and "therefore at least one doesn't, but we can't decide which" (LLPO). The distinction between "local realism is false" (classical) and "we can demonstrate incompatibility but not localize the failure" (constructive) is philosophically substantive and has not been made formally.

**Formalization plan:**
- Define LLPO in Lean (analogous to existing LPO definition)
- Formalize CHSH: four observables, locality assumption, algebraic derivation of |S| ≤ 2
- Formalize quantum bound: 2×2 density matrices, Pauli operators, |S| = 2√2
- Prove: CHSH violation → LLPO (the disjunctive conclusion requires LLPO to state)
- Axiom audit: identify exactly which step costs LLPO

**Infrastructure needed:** Finite-dimensional linear algebra (2×2 and 4×4 matrices). Mathlib has this. No analysis, no limits, no series. The cleanest formalization target in the programme.

**Audience:** Quantum information, quantum foundations, philosophy of physics. Much larger than the current CRM audience.

**Estimated effort:** 6–8 weeks. One paper.

**Why this is first priority:** It's finite, algebraic, the physics is uncontested, the Lean formalization is tractable, and it demonstrates that CRM is more than a one-principle tool. It opens the LLPO wing of the programme.

---

### 2. WLPO and Spontaneous Symmetry Breaking

**Target assertion:** The ground state of the Ising model breaks Z₂ symmetry in the thermodynamic limit.

**CRM framing:** This stratifies into three layers:
1. **Finite-volume magnetization** m(L) is a finite sum — BISH (Paper 8 infrastructure).
2. **Thermodynamic limit** m(L) → m(∞) as L → ∞ — LPO (already calibrated in Paper 8).
3. **Symmetry decision** m(∞) = 0 (symmetric) or m(∞) ≠ 0 (broken) — WLPO. The assertion "the magnetization is not identically zero" is exactly WLPO: deciding whether a real number equals zero.

This is the first instance of *stratified* logical cost: one physical phenomenon requiring two constructive principles at different levels. Paper 8 found layer 2. Layer 3 is new.

**What CRM adds:** The phase transition involves two distinct logical costs. Taking the limit costs LPO. Deciding which phase you're in costs WLPO on top of LPO. Finite-volume physics (BISH) can approximate the magnetization arbitrarily closely but cannot decide whether the limit is exactly zero — that's WLPO. This explains constructively why finite-size scaling (a BISH procedure) can estimate the critical temperature but cannot determine the phase with certainty.

**Formalization plan:**
- Define WLPO in Lean
- Extend Paper 8's Ising infrastructure with magnetization
- Prove: phase classification (m = 0 vs m ≠ 0) in the thermodynamic limit ↔ WLPO
- The forward direction (WLPO → phase classification) should be straightforward
- The backward direction (phase classification → WLPO) requires an encoding of WLPO into the magnetization — construct a family of Ising models parameterized by a binary sequence where the limiting magnetization encodes whether the sequence is all zeros

**Infrastructure needed:** Paper 8 Lean code (already exists) plus WLPO definition and the magnetization encoding. Moderate extension of existing infrastructure.

**Audience:** Statistical mechanics, condensed matter theory, mathematical physics.

**Estimated effort:** 8–10 weeks. One paper. Builds directly on Paper 8.

**Why this is second priority:** It extends existing work (Paper 8), demonstrates stratification (two principles in one phenomenon), and introduces WLPO to the programme. The formalization reuses existing infrastructure.

---

### 3. Markov's Principle and Quantum Tunneling

**Target assertion:** A particle tunnels through a finite barrier in finite time.

**CRM framing:** Three distinct assertions, three different logical costs:
1. **The transmission coefficient T is computable** from barrier parameters (height V, width d, particle energy E): T = e^{-2∫√(2m(V-E))dx}. This is a definite integral of an algebraic function — BISH.
2. **T > 0 for any finite barrier**: since T = e^{-something finite}, T is strictly positive. This is BISH (explicit witness: T ≥ e^{-2d√(2mV)}).
3. **The particle eventually tunnels** (if T > 0, detection occurs in finite time): this is Markov's Principle — a nonzero probability implies eventual observation.

The physics community conflates these three assertions. CRM separates them.

**What CRM adds:** The tunneling time controversy (Büttiker-Landauer time, Larmor clock, attoclock experiments) is partly a confusion between:
- "What is the transmission probability?" (BISH — computable)
- "Does tunneling occur?" (BISH — T > 0 is explicit)
- "When does tunneling occur?" (BISH with explicit bound if you accept a probabilistic model; Markov's Principle if you want a deterministic assertion)
- "Does the particle spend time inside the barrier?" (involves asserting properties of the path between preparation and detection — different logical structure entirely)

CRM can't resolve the physics, but it can classify which assertions are computable and which require additional logical principles.

**Formalization plan:**
- Define Markov's Principle in Lean
- Formalize WKB transmission coefficient for rectangular barrier (closed form — BISH)
- State the three assertions formally, prove their logical costs
- The encoding for the backward direction: construct a family of barriers parameterized by a real number where the tunneling time encodes whether the real is apart from zero

**Infrastructure needed:** Basic real analysis (exponentials, integrals on finite intervals). Some of this exists in Mathlib.

**Audience:** Quantum mechanics pedagogy, attosecond physics, philosophy of physics. The tunneling time controversy is active and high-profile.

**Estimated effort:** 8–10 weeks. One paper.

**Why this is third priority:** Connects CRM to an active experimental controversy, uses elementary physics (1D QM), and introduces Markov's Principle to the programme.

---

## Tier 2: High Payoff, Harder Formalization

### 4. LLPO and Kochen-Specker Contextuality

**Target assertion:** No noncontextual hidden variable model exists in Hilbert space dimension ≥ 3.

**CRM framing:** The Kochen-Specker theorem constructs a finite set of vectors (e.g., Peres's 33 vectors in ℝ³, or the original 117 in ℝ³) that cannot all be assigned 0/1 values consistently with the constraint that exactly one vector in each orthogonal basis gets value 1. The existence of such a set is a finite combinatorial fact — BISH (check all assignments by exhaustion). The physical conclusion — "at least one measurement context must lack predetermined values" — is LLPO: a disjunction over contexts without a constructive selection of which one fails.

**What CRM adds:** Contextuality and Bell nonlocality have the same constructive structure (LLPO), despite different physical content (nonlocality is about spatial separation, contextuality is about measurement incompatibility). CRM reveals they're the same *logical* phenomenon dressed in different physics.

**Formalization plan:** Finite linear algebra over ℝ³, orthogonality checking, exhaustive 0/1 assignment verification. All BISH. The LLPO content is in the interpretation. Could share infrastructure with the Bell paper.

**Estimated effort:** 6–8 weeks after the Bell paper (shared LLPO infrastructure).

---

### 5. Fan Theorem and the Yang-Mills Mass Gap

**Target assertion:** The spectrum of the Yang-Mills Hamiltonian has a gap Δ > 0 above the vacuum, uniformly in volume.

**CRM framing:** Lattice Yang-Mills on a finite lattice has a computable spectrum — BISH. The mass gap assertion is that the spectral gap doesn't vanish as the lattice spacing → 0 and volume → ∞. "Doesn't vanish in the limit" involves both a completed limit (LPO) and uniformity of the bound (Fan Theorem / Bar Induction). This is strictly stronger than LPO — it's a compactness assertion.

**What CRM adds:** The Millennium Prize problem, read through CRM, asks whether the mass gap has a BISH witness (an explicit bound Δ > c for computable c) or inherently requires Fan Theorem-level machinery. Lattice QCD provides numerical evidence for a BISH witness but not a proof. The CRM framing clarifies what kind of proof would be needed.

**Feasibility:** Very hard. Requires constructive lattice gauge theory, which doesn't exist. This is a long-term direction, not a near-term paper. But the *framing* (mass gap as Fan Theorem question) could be published as a conceptual paper without full formalization.

**Estimated effort:** 1–2 years for a serious formalization. 3–4 months for a conceptual/framing paper.

---

### 6. Choice Principles and Gauge Fixing

**Target assertion:** A global gauge-fixing condition exists for non-abelian gauge theory.

**CRM framing:** Gauge fixing = selecting one representative from each gauge orbit. For finite lattice: finitely many orbits, each finite — BISH. For continuum: uncountably many orbits — requires choice. Gribov's theorem: no global smooth gauge fixing exists for non-abelian theories — a constructive obstruction to choice. The Gribov obstruction is a *proof* that the required choice principle fails in this setting.

**What CRM adds:** Gribov copies reframed as a constructive phenomenon — the failure of a specific choice principle in gauge theory. The Faddeev-Popov procedure (which assumes global gauge fixing) silently invokes a choice principle that Gribov proved unavailable. CRM makes this logical gap explicit.

**Feasibility:** Hard. Requires formalizing fiber bundles, connections, gauge orbits. Far beyond current Mathlib. Conceptual paper feasible; full formalization is a multi-year project.

---

## Tier 3: Speculative

### 7. Existential Witnesses and the String Landscape

The claim "there exists a string compactification reproducing the Standard Model" is a non-constructive existential over ~10^500 vacua. Constructively: either produce a witness or the claim is empty. The logical content of the landscape is about *search* — computational complexity of finding SM-like vacua in a vast discrete space. Connects CRM to computational complexity theory. Very speculative, no clear formalization path.

### 8. Constructive Quantum Field Theory

The full programme: reformulate QFT axioms (Wightman or Osterwalder-Schrader) constructively and determine which axioms require which constructive principles. This would be the ultimate CRM project but requires formalizing distribution theory, analytic continuation, and functional analysis constructively. Multi-decade project. The constructive analysis community (Bridges, Richman, Ye) has some of the mathematical infrastructure but none of the physics connections.

---

## Recommended Sequence

| Order | Project | Principle | Timeline | Builds On |
|---|---|---|---|---|
| 1 | Bell / CHSH | LLPO | 6–8 weeks | New (standalone) |
| 2 | Ising symmetry breaking | WLPO + LPO | 8–10 weeks | Paper 8 |
| 3 | Quantum tunneling | Markov | 8–10 weeks | New (standalone) |
| 4 | Kochen-Specker | LLPO | 6–8 weeks | Project 1 |
| 5 | Yang-Mills mass gap (conceptual) | Fan Theorem | 3–4 months | Framing paper only |
| 6 | Gauge fixing (conceptual) | Choice | 3–4 months | Framing paper only |

Projects 1–4 are full papers with Lean formalization and axiom audits, continuing the established CRM methodology. Projects 5–6 are conceptual/framing papers that identify the relevant constructive principles without full formalization. Total timeline for projects 1–4: approximately 8–10 months.

---

## What This Achieves

The current programme has one tool (BMC↔LPO) applied to six domains (five positive, one negative). The expanded programme would have four tools (LPO, LLPO, WLPO, Markov) applied across classical mechanics, quantum mechanics, statistical mechanics, quantum foundations, and quantum gravity.

The central claim upgrades from "completed limits in physics cost LPO" to "the constructive hierarchy maps onto the hierarchy of physical assertions — limits (LPO), exclusion (LLPO), phase classification (WLPO), detectability (Markov), uniformity (Fan Theorem)." That's a much stronger and more general thesis, and it's testable paper by paper.

The most important strategic consequence: the programme stops being "the BMC↔LPO programme" and becomes "the constructive calibration of mathematical physics" — a systematic audit of which constructive principles underwrite which physical conclusions. That's a research programme with decade-scale depth, not a single finding applied to multiple domains.

---

## Risk Assessment

**The main risk** is that the new principles (LLPO, WLPO, Markov) turn out to have the same template problem as BMC↔LPO — a single encoding trick applied repeatedly with different gap lemmas. If LLPO calibrations all use the same Bell-type encoding with different physical wrappers, we're back to the hammer-and-nail problem at a larger scale.

**Mitigation:** The principles are mathematically distinct (LLPO is about disjunctions, WLPO about decidability of equality, Markov about apartness, Fan Theorem about uniformity). Their physical manifestations should require genuinely different encoding strategies. The Bell encoding (two incompatible measurement settings) is structurally different from the BMC encoding (running maximum of a two-valued sequence), which is evidence that different principles require different mathematical techniques.

**Secondary risk:** The Lean formalization of LLPO/WLPO/Markov may require Mathlib infrastructure that doesn't exist yet (finite-dimensional quantum mechanics, spectral theory, probabilistic assertions). Mitigation: start with Bell/CHSH, which requires only 2×2 and 4×4 matrix algebra — well within current Mathlib.

**Third risk:** The audience for "constructive calibration of physics" may be too small for the effort. Mitigation: the Bell paper (Project 1) targets the quantum information community, which is large, active, and receptive to foundational work. If that paper lands well, it validates the expanded programme. If it doesn't, we learn something about audience before investing 10 months.

---

## Appendix: Relationship to Papers 17 and 18

Paper 17 (quantum gravity, BMC↔LPO) is the capstone of the accumulation phase. Paper 18 (Yukawa RG, BISH-only) is the scope-finding paper. Together they establish that BMC↔LPO is real but bounded — it appears where physics makes completed-limit assertions and is absent where the physics is inherently finite.

The expanded programme begins where Paper 18's negative result points: toward other constructive principles that might apply where LPO doesn't. The flavor problem remains outside CRM's scope (it's about specific numerical values, not logical structure). But quantum foundations (Bell, contextuality), phase transitions (symmetry breaking), and quantum dynamics (tunneling, mass gaps) are all domains where constructive principles other than LPO should play roles — and where CRM has not yet looked.

The gauge coupling unification observation from Paper 18's appendix (exact unification is LPO scaffolding, approximate unification is BISH) remains the one instance where the scaffolding principle produced a non-trivial UV insight. Whether to develop this into a standalone paper or leave it as an appendix observation is an open question. It doesn't require new constructive principles — it's a further application of LPO — but it does connect CRM to GUT phenomenology, which is a different audience from the foundations community targeted by the expanded programme.
