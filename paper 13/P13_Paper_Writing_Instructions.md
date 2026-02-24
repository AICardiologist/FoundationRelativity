# Paper 13: The Event Horizon as a Logical Boundary — Writing Instructions

## For the Writing/Coding Agent

**Status:** Lean formalization complete (1,021 lines, 8 files, zero sorry, zero errors, 3100 build jobs). Paper not yet written. This document provides full instructions for drafting the LaTeX paper.

**Core result:**
```
theorem schwarzschild_interior_geodesic_incompleteness_iff_LPO :
    SchwarzschildInteriorGeodesicIncompleteness ↔ LPO
```

**Axiom profile:**
- Main theorem: `propext, Classical.choice, Quot.sound, bmc_of_lpo`
- Forward direction (→ LPO): `propext, Classical.choice, Quot.sound` (no extra axioms)
- Reverse direction (LPO →): adds `bmc_of_lpo` (axiomatized from Paper 8)
- BISH results (cycloid, Kretschner): `propext, Classical.choice, Quot.sound` only (Mathlib infra)

---

## METADATA

- **Title:** The Event Horizon as a Logical Boundary: Schwarzschild Interior Geodesic Incompleteness and LPO in Lean 4
- **Author:** Paul Chun-Kit Lee
- **Affiliation:** Independent Researcher, New York
- **Series number:** Paper 13 in the Constructive Reverse Mathematics series
- **Lean version:** Lean 4 / Mathlib (current toolchain)
- **Build status:** 3100 jobs, zero errors, zero sorry
- **Zenodo DOI:** (to be assigned)
- **Companion papers:** Paper 1 (Schwarzschild exterior, BISH), Paper 8 (1D Ising, BMC ↔ LPO)

---

## ABSTRACT (~200 words)

Draft covering these points:

1. We formalize in Lean 4 a decomposition of Schwarzschild interior physics into constructive content layers.

2. **BISH content (Height 0):** The explicit cycloid geodesic r(η) = M(1 + cos η) reaches r = 0 at τ* = πM constructively. The Kretschner scalar K = 48M²/r⁶ diverges constructively. All finite-proper-time predictions are computable without omniscience.

3. **LPO content (Height 1):** The abstract principle that every bounded monotone decreasing sequence in [0, 2M) converges to a definite limit — the completed-limit formulation of geodesic incompleteness — is equivalent to LPO (the Limited Principle of Omniscience).

4. The event horizon at r = 2M thus demarcates not only the causal boundary (from which light cannot escape) but a logical boundary: the exterior geometry (Paper 1) and the interior's finite-time physics are BISH, while the singularity assertion as a completed-limit principle requires exactly LPO.

5. Formalization: 1,021 lines across 8 modules, one interface assumption (`bmc_of_lpo`, the Bridges-Vîță equivalence imported from Paper 8).

6. One sentence on Classical.choice methodology: "The `Classical.choice` in the axiom profile arises from Mathlib infrastructure; the constructive calibration is established by proof-content analysis (see §X and Paper 10)."

---

## 1. INTRODUCTION (~2 pages)

### §1.1 Physical Context

The Schwarzschild solution describes the geometry of a non-rotating, uncharged black hole. The event horizon at r = 2M is the boundary of the region from which future-directed causal curves can reach infinity. Inside the horizon, the radial coordinate r becomes timelike — a freely falling observer necessarily moves toward decreasing r and reaches the curvature singularity at r = 0 in finite proper time.

This "geodesic incompleteness" — the fact that timelike geodesics terminate at the singularity — is the physical content that the Penrose singularity theorem (1965) generalizes to arbitrary spacetimes satisfying energy conditions. For Schwarzschild, the explicit solution is available: a radially infalling particle dropped from rest at the horizon follows the cycloid r(η) = M(1 + cos η), τ(η) = M(η + sin η), reaching r = 0 at proper time τ* = πM.

### §1.2 The CRM Question

From the standpoint of constructive reverse mathematics, the question is: what is the logical cost of asserting geodesic incompleteness?

The answer turns out to be more subtle than "BISH" or "LPO." It decomposes:

- The **specific** cycloid geodesic reaching r = 0 is constructively computable (BISH). The endpoint is given by explicit trigonometric evaluation: r(π) = M(1 + cos π) = 0.

- The **abstract principle** that every bounded monotone decreasing sequence in the interior converges to a definite limit — the completed-limit formulation that underlies the general assertion of geodesic incompleteness — is equivalent to LPO.

This decomposition mirrors Paper 8's treatment of the 1D Ising model, where finite-size bounds are BISH but the thermodynamic limit (a completed-limit assertion about the free energy sequence) costs LPO.

### §1.3 Contributions

State as a numbered list (this is one place where a list is appropriate):

1. Machine-verified proof that SchwarzschildInteriorGeodesicIncompleteness ↔ LPO (1,021 lines, zero sorry)
2. Explicit BISH content: cycloid computability, Kretschner divergence, finite-time approaching — all Height 0
3. The event horizon as a logical boundary: the first result calibrating a general-relativistic singularity assertion
4. Connection to Paper 8 via BMC ↔ LPO, extending the pattern from statistical mechanics to gravitation

### §1.4 Related Work

- Paper 1 (Lee 2026): Schwarzschild exterior curvature verification, BISH (Height 0)
- Paper 8 (Lee 2026): 1D Ising model, BMC ↔ LPO for the thermodynamic limit
- Bridges and Vîță (2006): BMC ↔ LPO equivalence (the result imported as `bmc_of_lpo`)
- Echenim and Mhalla (2024): Formalization of CHSH in Isabelle/HOL (classical, no constructive analysis)
- No prior CRM analysis of GR singularities exists in the literature

---

## 2. MATHEMATICAL CONTENT (~2-3 pages)

### §2.1 The Schwarzschild Interior

Define the interior domain: 0 < r < 2M, M > 0. State the signature flip: g_tt and g_rr swap sign, making r timelike. Note that the metric components remain well-defined for r > 0.

### §2.2 The Cycloid Geodesic (BISH)

Present the explicit solution for E = 1 (dropped from rest at the horizon):

```
r(η) = M(1 + cos η)
τ(η) = M(η + sin η)
```

where η ∈ [0, π]. State and prove (informally, referencing the Lean):

- r is monotonically decreasing on [0, π]: r'(η) = -M sin η < 0
- r(0) = 2M (horizon), r(π) = 0 (singularity)
- τ(π) = πM (finite proper time)
- For any ε > 0, there exists η such that r(η) < ε (constructive approaching)

**Key point:** All of this is BISH. The cycloid is an explicit computable function. No omniscience principle is needed.

### §2.3 The Completed-Limit Formulation (LPO)

Define SchwarzschildInteriorGeodesicIncompleteness as:

> For every sequence a : ℕ → ℝ satisfying:
> - a is antitone (non-increasing)
> - a n ≥ 0 for all n
> - a 0 < 2M (starts in the interior)
> 
> there exists L : ℝ such that a converges to L.

This is the **universally quantified** completed-limit assertion. It says: any monotone bounded sequence in the interior has a definite limit. This captures the logical content of "every radially infalling trajectory has a definite endpoint" — not just the cycloid, but *any* monotone bounded trajectory.

**Theorem.** SchwarzschildInteriorGeodesicIncompleteness ↔ LPO.

### §2.4 Forward Direction: Incompleteness → LPO

Given α : ℕ → Bool (an arbitrary binary sequence), construct:

```
geodesicCoupling α M 0 n = if runMax α n then 0 else M
```

where `runMax α n = true` iff ∃ k ≤ n, α k = true.

This sequence is:
- Antitone (it can only jump from M to 0, never back)
- Non-negative
- Starts at M (or 0), which is < 2M

If ∀ n, α n = false: the sequence is constantly M, limit = M.
If ∃ n, α n = true: the sequence eventually drops to 0, limit = 0.

The gap δ = M between these cases is the "decision amplifier." If SchwarzschildInteriorGeodesicIncompleteness gives a definite limit L, comparing L against M/2 decides ∃ n, α n = true vs. ∀ n, α n = false. This is LPO.

### §2.5 Reverse Direction: LPO → Incompleteness

LPO implies BMC (Bounded Monotone Convergence) by the Bridges-Vîță equivalence [imported as `bmc_of_lpo`]. Given any antitone sequence a bounded in [0, 2M), BMC gives convergence to a definite limit. Done.

### §2.6 The Honest Decomposition

**IMPORTANT — THIS IS THE CENTRAL MESSAGE OF THE PAPER. Write it clearly.**

The paper does NOT claim "computing the cycloid endpoint costs LPO." The cycloid is BISH. The paper claims:

| Content | Principle | Certification |
|---------|-----------|---------------|
| Cycloid r(π) = 0 | BISH | Height 0 (machine-verified) |
| Cycloid approaching: ∀ε > 0, ∃η, r(η) < ε | BISH | Height 0 (machine-verified) |
| Kretschner K → ∞ as r → 0 | BISH | Height 0 (machine-verified) |
| "Every antitone bounded sequence in [0,2M) has a limit" | LPO | ↔ equivalence (machine-verified) |

The event horizon separates the BISH exterior (Paper 1) from the interior where the *general completed-limit principle* costs LPO. The specific solution is constructive; the universal assertion is not.

---

## 3. LEAN FORMALIZATION (~1.5 pages)

### §3.1 Architecture

| Module | Lines | Content |
|--------|-------|---------|
| Basic.lean | 168 | LPO, BMC, Interior, runMax + lemmas |
| RadialGeodesic.lean | 250 | Cycloid parametrization, monotonicity, approaching |
| Incompleteness.lean | 167 | SchwarzschildInteriorGeodesicIncompleteness + coupling |
| LPO_Forward.lean | 91 | → direction via gap encoding |
| LPO_Reverse.lean | 57 | ← direction via BMC |
| BISH_Content.lean | 128 | Kretschner, cycloid computability |
| Certificates.lean | 85 | #print axioms audit |
| Main.lean | 75 | Assembly |
| **Total** | **1,021** | |

### §3.2 Key Design Decisions

**Cycloid-first approach.** Rather than formalizing the ODE for geodesic motion (which would require Lean ODE infrastructure that doesn't exist), we work with the closed-form cycloid solution directly. The monotonicity, boundedness, and convergence properties are explicit from trigonometric identities. This is Option A from the formalization plan.

**Abstract incompleteness.** SchwarzschildInteriorGeodesicIncompleteness quantifies over all antitone non-negative sequences starting below 2M, not over solutions of the geodesic equation. This is the correct level of abstraction for CRM: the logical content is the completed-limit principle, and the geodesic equation is the physical motivation for why such sequences arise.

**BMC import.** The `bmc_of_lpo` axiom imports the Bridges-Vîță equivalence from Paper 8. This is the same interface assumption used in Paper 8 and documented in the series methodology (Paper 10, §X).

### §3.3 Axiom Audit

```
#print axioms schwarzschild_interior_geodesic_incompleteness_iff_LPO
-- [propext, Classical.choice, Quot.sound, bmc_of_lpo]

#print axioms r_cycloid_at_pi
-- [propext, Classical.choice, Quot.sound]  (BISH — Mathlib infra only)

#print axioms bish_content_complete
-- [propext, Classical.choice, Quot.sound]  (BISH — Mathlib infra only)
```

The `Classical.choice` in the BISH results arises from Mathlib's real number infrastructure, not from the mathematical content. See §X (or reference Paper 10) for the series-wide methodology on this point.

---

## 4. THE EVENT HORIZON AS A LOGICAL BOUNDARY (~1.5 pages)

This is the interpretive section — the physics payoff.

### §4.1 The Causal Boundary

In classical GR, the event horizon at r = 2M is the boundary of the causal past of future null infinity. Light signals from r < 2M cannot reach distant observers. This is a statement about the global causal structure of the spacetime.

### §4.2 The Logical Boundary

Our result reveals a second boundary coinciding with the event horizon:

**Exterior (r > 2M):** Paper 1 establishes that the Schwarzschild geometry — metric components, Christoffel symbols, Riemann tensor, Ricci flatness, Kretschner scalar — is BISH. No omniscience principle is needed.

**Interior (0 < r < 2M):** The finite-time physics remains BISH (cycloid computability, curvature divergence). But the *completed assertion* that geodesics terminate — the universal statement that every bounded monotone trajectory converges — costs LPO.

The horizon thus demarcates not only what can communicate with infinity, but what can be asserted without surveying an infinite set.

### §4.3 Connection to Paper 8

The pattern is identical to the 1D Ising model:

| | Paper 8 (Ising) | Paper 13 (Schwarzschild) |
|---|---|---|
| BISH content | Finite-size partition function | Cycloid geodesic, Kretschner scalar |
| LPO content | Thermodynamic limit (f.e. convergence) | Geodesic incompleteness (completed limit) |
| Physical interpretation | Phase transitions require idealization | Singularities require idealization |
| Encoding technique | Coupling constant modulation | Sequence coupling (geodesicCoupling) |

Both cases instantiate the same principle: **completed infinite limits in physics cost LPO, but the finite approximations that carry empirical content are BISH.**

### §4.4 What This Does NOT Claim

**Be explicit. This section preempts the strongest objection.**

> This paper does not claim that "reaching the singularity costs LPO" in any operational sense. A freely falling observer following the cycloid geodesic computes r(τ) constructively at every finite proper time, and the limit r → 0 is constructively approachable (for any ε, we can find τ with r(τ) < ε). The LPO cost attaches to the *universally quantified completeness principle* — the assertion that every bounded monotone trajectory in the interior converges to a definite limit — not to any particular trajectory.
>
> The physical content is this: classical GR's assertion of geodesic incompleteness, when formulated as a completed-limit principle over all infalling trajectories, carries the same logical cost (LPO) as the thermodynamic limit in statistical mechanics. Both are instances of Bounded Monotone Convergence applied to physically motivated monotone sequences.

---

## 5. DISCUSSION (~1 page)

### §5.1 The Calibration Table

Paper 13 adds a new row:

| Layer | Principle | Status | Source |
|-------|-----------|--------|--------|
| Schwarzschild exterior | BISH | Calibrated | Paper 1 |
| Interior finite-time physics | BISH | Calibrated | Paper 13 |
| Geodesic incompleteness (completed limit) | LPO | Calibrated | Paper 13 |

Combined with the Ising rows (Paper 8) and the entanglement rows (Paper 11), the pattern strengthens: all LPO costs arise from completed infinite limits, all finite-time/finite-size physics is BISH.

### §5.2 The Penrose Singularity Theorem

The Penrose theorem (1965) generalizes geodesic incompleteness from Schwarzschild to arbitrary spacetimes satisfying: (i) a trapped surface exists, (ii) the null energy condition holds, (iii) a Cauchy surface exists. Formalizing the Penrose theorem in Lean 4 would require massive infrastructure (global hyperbolicity, trapped surfaces, energy conditions) far beyond our scope.

However, our result suggests a prediction: the Penrose theorem, when formalized constructively, should calibrate at or above LPO. The completed-limit content is the same — asserting that geodesics terminate — and the additional hypotheses (energy conditions, Cauchy surfaces) may introduce further costs. This is stated as an open problem.

### §5.3 Open Problems

1. **Penrose theorem calibration.** Does the full Penrose singularity theorem, including trapped surface and energy condition hypotheses, calibrate above LPO?

2. **Cosmic censorship.** Weak cosmic censorship (singularities hidden behind horizons) involves a universal quantifier over all generic initial data. What is its logical cost?

3. **Hawking radiation.** The quantum process by which black holes evaporate involves the thermodynamic limit (infinite number of modes). Does the Hawking temperature calculation inherit the LPO cost, or is it dispensable?

---

## 6. CERTIFICATION METHODOLOGY (~0.5 pages)

**Same framework as Papers 7, 10, 11. Keep brief and reference Paper 10.**

### §6.1 Axiom Profile

All theorems carry `[propext, Classical.choice, Quot.sound]` from Mathlib plus `bmc_of_lpo` for the reverse direction. The BISH results (cycloid, Kretschner) have `Classical.choice` from Mathlib infrastructure only.

### §6.2 Certification Level

Paper 13 is "structurally verified" in the series terminology (Paper 10, §X):
- The BISH content is finite-dimensional/explicit computation — constructively valid by inspection
- The LPO equivalence uses `bmc_of_lpo` intentionally (this IS the classical content)
- No P13_Minimal artifact is planned (the logical structure — BMC ↔ LPO instantiated on [0, 2M) — is simple enough that the full artifact suffices)

### §6.3 The bmc_of_lpo Axiom

The equivalence BMC ↔ LPO is due to Bridges and Vîță (2006). It is axiomatized in Paper 13 rather than re-proved because:
- Paper 8 already uses the same axiom
- The Bridges-Vîță proof is standard and uncontroversial
- Re-proving it would add ~200 lines of Lean for zero epistemic gain

The axiom is conservative: it introduces no new logical content beyond what LPO already provides.

---

## 7. REPRODUCIBILITY BOX

```
Repository: github.com/AICardiologist/FoundationRelativity
Path: Papers/P13_EventHorizon/
Build: lake build (3100 jobs, 0 errors, 0 sorry)
Lean toolchain: [current version]
Mathlib: [current version]
Zenodo DOI: [to be assigned]
Interface axiom: bmc_of_lpo (Bridges-Vîță, imported from Paper 8)
Axiom audit: Certificates.lean
```

---

## CRITICAL WRITING GUIDANCE

### The Central Tension

The paper has one potentially controversial claim: calling the BMC-on-[0,2M) equivalence "geodesic incompleteness." A hostile referee could object: "This is just BMC for a specific class of sequences. The name 'SchwarzschildInteriorGeodesicIncompleteness' is a physical interpretation you've bolted on."

**How to handle this:** Don't hide it. Address it head-on in §2.3 and §4.4:

> In classical general relativity, geodesic incompleteness IS a completed-limit assertion about monotone sequences. The radial coordinate along any infalling timelike geodesic is a monotone decreasing function of proper time, bounded below by 0. The assertion "the spacetime is geodesically incomplete" means these sequences converge. Our formalization strips away the differential geometry (we do not formalize the Lorentzian metric, parallel transport, or the geodesic equation as an ODE) and isolates the exact logical content: Bounded Monotone Convergence for decreasing sequences in [0, 2M). This extraction of logical content from physical assertion is the standard methodology of constructive reverse mathematics.

> The Brouwerian counterexample (geodesicCoupling) is not a geodesic — it is a valid element of the domain of the universally quantified proposition. This is standard CRM methodology: the counterexample demonstrates that the universal principle carries LPO strength, while specific instances (the cycloid) are constructive.

### Tone

Confident, not defensive. The decomposition (BISH cycloid + LPO completed-limit) is clean and honest. The paper's value is the decomposition itself — showing that the event horizon separates constructive content from non-constructive content — not a claim that "computing singularities requires LPO."

### What NOT to Include

- Do NOT formalize the Penrose theorem or discuss it at length. State it as an open problem.
- Do NOT discuss Kruskal-Szekeres coordinates. Irrelevant.
- Do NOT discuss quantum gravity. Out of scope.
- Do NOT reproduce the naysayer response document verbatim. Incorporate its insights into the paper's own voice.
- Do NOT add extensive philosophical discussion. Paper 10 handles the philosophy; Paper 13 is a formalization paper.

---

## ESTIMATED LENGTH

~12-15 pages including references and reproducibility box. This is a focused paper — one theorem, one decomposition, one punchline.
