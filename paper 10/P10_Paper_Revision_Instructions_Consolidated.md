# Paper 10 Revision Instructions (Consolidated)

## For the Writing Agent

**Paper 10** is the synthesis/conceptual paper for the CRM series: "A Logical Geography of Physical Idealizations." It has no Lean formalization of its own. Its role is to present the calibration table, state the working hypothesis, report the formulation-invariance test, position the programme against existing literature, establish the series-wide certification methodology, and state open problems.

**Current state:** ~5,500 words, on Zenodo. LaTeX version exists. The paper was written before Paper 11 (Tsirelson/Bell entropy, BISH) and Paper 13 (Schwarzschild interior, LPO) were complete. It needs updating to incorporate these results and — critically — to add the methodology section that all other papers in the series reference.

**IMPORTANT:** The agent does not have the full text open; these instructions are written from extensive conversation history. Adapt section references if they have shifted. The intent of each edit matters more than the exact line numbers.

**Target audience:** *Foundations of Physics* / *Studies in History and Philosophy of Modern Physics*. Philosophical register, not Lean syntax.

---

## EDIT 1 — THE METHODOLOGY SECTION (HIGHEST PRIORITY)

This is the single most important edit in the entire series revision. Papers 7, 8, 11, and 13 all say "see Paper 10" for the certification methodology. That section must exist and be definitive.

### Location: New section, after CRM background, before the calibration table. Probably §3 or §4.

### Title: "Methodology: Formalization in a Classical Metatheory"

### Full Content Guidance (~2 pages):

**§X.1 — The Standard CRM Methodology**

CRM has always operated within a classical metatheory. Bridges and Richman prove their equivalences using informal mathematics that implicitly includes excluded middle at the meta-level. Ishihara works in classical set theory. Simpson's *Subsystems of Second-Order Arithmetic* uses ZFC as the metatheory for reverse mathematics over RCA₀. The question is never whether the metatheory is constructive; it is always whether the *object-level theorem* can be stated and proved using only the principles under investigation.

This paper's companion formalizations (Papers 1–9, 11, 13) adopt the same methodology in a mechanized setting. Lean 4 with Mathlib is the classical metatheory. The constructive content is extracted by inspecting what the proofs actually use, as reported by `#print axioms`.

**§X.2 — Three Certification Levels**

The formalizations in this series achieve different levels of certification for their constructive claims:

1. **Mechanically certified.** The Lean build target compiles without `Classical.choice` in the `#print axioms` output. Constructive purity is verified by the machine itself. Example: Paper 2's P2_Minimal — a dependency-free Lean build target that certifies the core WLPO ↔ bidual gap equivalence without any Mathlib imports.

2. **Structurally verified.** The Lean build target compiles with `Classical.choice` inherited from Mathlib's typeclass infrastructure, but the proof structure uses only constructively valid reasoning (finite-dimensional algebra, explicit computation, Hahn-Banach for separable spaces). The BISH claim is established by mathematical argument about proof content, supported by the machine-checked proof structure. Examples: Papers 7 (P7_Full), 8A, 9A, 11, 13 (BISH content).

3. **Intentional classical content.** The proof uses classical principles by design — the classical content is the *theorem*, not an artifact of the library. `#print axioms` correctly reports classical axioms because the theorem *requires* them. Examples: Paper 8B (LPO appears because BMC ≡ LPO is the theorem), Paper 13 main theorem (LPO equivalence is the result), Paper 7 reverse direction (WLPO appears as a hypothesis).

**§X.3 — The Mathlib Question**

Why does `Classical.choice` appear in proofs about finite matrices (Paper 11) or explicit trigonometric computations (Paper 13's cycloid)?

Mathlib imports `Classical.em` and `Classical.choice` at the library level. These enter the axiom profile through typeclass resolution — when Lean resolves `Decidable` instances for ℝ, ℂ, or matrix entries, it traces through classical infrastructure regardless of whether the proof term actually uses decidability. The result: `#print axioms` cannot distinguish between "this theorem requires classical logic" and "this theorem's proof happens to be written in a library that assumes classical logic."

This is not a defect. It is the expected behavior of a classical metatheory. Just as Bridges and Richman's informal proofs do not mechanically certify BISH by virtue of being written in English, Lean proofs do not mechanically certify BISH by virtue of compiling. What the Lean proofs provide is something informal proofs cannot: a machine-checked guarantee that every step type-checks, that no implicit gaps exist, and that axiom dependencies are exhaustively reported.

**§X.4 — The Role of Minimal Artifacts**

Where the constructive claim is non-trivial or the proof involves genuine logical content, the series provides dependency-free "minimal" artifacts. These are separate Lean build targets that axiomatize Mathlib-dependent results and verify the logical reduction chain without classical imports.

| Paper | Full Artifact | Minimal Artifact | Certification |
|-------|-------------|-----------------|---------------|
| 2 | P2_Full (Mathlib, 3100 lines) | P2_Minimal (dep-free, ~200 lines) | Mechanically certified |
| 7 | P7_Full (Mathlib, 754 lines) | P7_Minimal (dep-free, ~150 lines) [forthcoming] | Mechanically certified (pending) |
| 8A | Transfer matrix (BISH) | — | Structurally verified |
| 8B | BMC ↔ LPO | — | Intentional classical |
| 9 | Combinatorial Ising | — | Structurally verified (import-audited) |
| 11 | Tsirelson + Bell (500 lines) | — | Structurally verified |
| 13 (BISH) | Cycloid, Kretschner (128 lines) | — | Structurally verified |
| 13 (LPO) | Main theorem (1021 lines) | — | Intentional classical |

No minimal artifact is needed for Papers 11 or 13's BISH content: finite-dimensional matrix algebra (Paper 11) and explicit trigonometric evaluation (Paper 13) being BISH is uncontroversial. The minimal artifacts are reserved for cases where the logical architecture itself is substantive (Papers 2, 7).

**§X.5 — Limitations**

A fully constructive Lean library for CRM — separating classical and constructive content at the typeclass level, allowing mechanical BISH certification without dependency-free artifacts — does not currently exist. Building one is a major infrastructure project beyond this series' scope. The methodology described above is the best available approach given current tooling, and mirrors the standard practice in CRM where the metatheory is classical and the constructive content is established by mathematical argument.

---

## EDIT 2 — UPDATE CALIBRATION TABLE

The current table was written before Papers 11 and 13. Add their rows:

### Paper 11 rows (BISH — quantum compositional structure):

| Layer | Principle | Status | Source |
|-------|-----------|--------|--------|
| Bell nonlocality (CHSH/Tsirelson bound) | BISH | Calibrated | Paper 11 |
| Entanglement entropy (qubit Bell state) | BISH | Calibrated | Paper 11 |
| Partial trace (finite-dim) | BISH | Calibrated | Paper 11 |

### Paper 13 rows (GR singularities):

| Layer | Principle | Status | Source |
|-------|-----------|--------|--------|
| Schwarzschild interior finite-time physics | BISH | Calibrated | Paper 13 |
| Geodesic incompleteness (completed limit) | LPO | Calibrated | Paper 13 |

### Significance of these additions:

Paper 11 extends the calibration from "states, limits, spectra" to "tensor products, entanglement, correlations." The BISH results confirm that **quantum compositional structure — the infrastructure of entanglement itself — carries no non-constructive cost.** All costs in quantum theory arise from infinite-dimensional limits, not from the algebraic structure of quantum mechanics.

Paper 13 extends from statistical mechanics to **gravitation**. The event horizon as a logical boundary is a new kind of result — the first time a geometric boundary in physics coincides with a logical boundary in the constructive hierarchy. The LPO cost of geodesic incompleteness mirrors Paper 8's thermodynamic limit, strengthening the pattern that completed infinite limits cost exactly LPO.

Add a paragraph stating this explicitly after the updated table.

---

## EDIT 3 — STRENGTHEN THE WORKING HYPOTHESIS

The working hypothesis should now be updated to reflect the expanded evidence base. It should be stated crisply:

> **Working Hypothesis.** In the constructive reverse mathematics of mathematical physics, all non-constructive costs arise from infinite-dimensional idealization layers (thermodynamic limits, operator completions, bidual passages, singularity assertions as completed limits), not from the finite-dimensional or finite-time physical content (algebraic relations, symmetries, conservation laws, entanglement structure, cycloid geodesics, curvature scalars).

The evidence now spans:
- Functional analysis: bidual gap in ℓ¹ ↔ WLPO (Paper 2), trace-class non-reflexivity ↔ WLPO (Paper 7)
- Statistical mechanics: thermodynamic limit ↔ LPO (Paper 8), formulation-invariant (Paper 9)
- Quantum information: Tsirelson bound, Bell entropy = BISH (Paper 11)
- General relativity: exterior = BISH (Paper 1), interior finite-time = BISH (Paper 13), geodesic incompleteness ↔ LPO (Paper 13)

Note: Paper 13 is especially significant because it demonstrates the pattern in a completely different physical domain (gravitation vs. statistical mechanics), using the same logical equivalence (BMC ↔ LPO) applied to a different class of physically motivated monotone sequences.

---

## EDIT 4 — ADD PAPER 13 TO §6 (FORMULATION-INVARIANCE) OR DISCUSSION

Paper 13's connection to Paper 8 is methodologically significant. Both papers use the BMC ↔ LPO equivalence but apply it to different physical systems:

- Paper 8: coupling constant modulation → free energy sequence → BMC
- Paper 13: sequence coupling → infalling trajectory sequence → BMC

This is a different kind of invariance than formulation-invariance (Papers 8/9, same physics in different formalisms). It's **domain invariance**: the same logical structure appears in unrelated physical theories. If the paper has a section discussing the pattern across domains, Paper 13 should be mentioned there.

---

## EDIT 5 — FIX VAN WIERST BIBLIOGRAPHY

A previous review noted a corrupted title in the van Wierst *Synthese* 2019 reference. The correct citation needs to be verified and fixed. The agent should search for: van Wierst 2019 Synthese constructive mathematics phase transitions.

---

## EDIT 6 — VERIFY MP/WLPO HIERARCHY

Search the document for any claims about MP and WLPO relationships. Verify:

- LPO → WLPO → LLPO (correct)
- LPO → MP (correct)
- MP and WLPO are **independent** over BISH (correct)
- MP does NOT imply WLPO (correct)
- WLPO does NOT imply MP (correct)

If there is a hierarchy diagram, verify it reflects these relationships.

---

## EDIT 7 — ADD INFINITE-DIMENSIONAL ENTANGLEMENT AS OPEN PROBLEM

Paper 11 makes a natural new open problem:

> **Problem X. Infinite-dimensional entanglement entropy.** Paper 11 establishes that finite-dimensional entanglement structure (Tsirelson bound, Bell state entropy, partial trace) is BISH. Does passage to infinite-dimensional entanglement — von Neumann entropy of partial traces in S₁(H), entanglement measures for infinite-dimensional systems — introduce new logical costs? Does it inherit the WLPO cost of Paper 7's non-reflexivity for S₁(H)?

Also add, if not already present:

> **Problem Y. Singularity calibration beyond Schwarzschild.** Paper 13 calibrates geodesic incompleteness for the Schwarzschild interior at LPO. Does the full Penrose singularity theorem — including trapped surfaces, energy conditions, global hyperbolicity — calibrate above LPO? Does cosmic censorship (universal quantifier over all generic initial data) have a definite logical cost?

---

## EDIT 8 — UPDATE ABSTRACT

The abstract should now mention:
- The expanded calibration table (how many rows, spanning BISH to undecidable)
- Paper 11's BISH results for entanglement
- Paper 13's LPO result for geodesic incompleteness (the event horizon as a logical boundary)
- The formulation-invariance evidence (Papers 8+9)
- The certification methodology (three levels)
- That this is a conceptual/synthesis paper with no new formalization

---

## EDIT 9 — UPDATE CROSS-REFERENCES AND DOIS

Ensure all paper references include current Zenodo DOIs:
- Paper 2: 10.5281/zenodo.16916266 (minimal), 10.5281/zenodo.18501689 (full)
- Paper 7: 10.5281/zenodo.18509795
- Paper 9: 10.5281/zenodo.18517570
- Paper 11: [add DOI when available]
- Paper 13: [add DOI when available]

Add Paper 13 to the bibliography:
```
Lee, P. C.-K. (2026). The event horizon as a logical boundary:
Schwarzschild interior geodesic incompleteness and LPO in Lean 4.
Preprint. Paper 13 in the CRM series.
```

---

## EDIT 10 — VERIFY LITERATURE POSITIONING

The paper should engage substantively with:

1. **Batterman (2005, 2010):** Idealizations are explanatorily indispensable. Our work sharpens this: not just "necessary" but "necessary at strength exactly LPO" or "exactly WLPO." Paper 13 adds: singularity assertions cost the same as thermodynamic limits.

2. **van Wierst (2019):** Constructive mathematics and phase transitions. Paper 8 provides machine-verified calibration extending van Wierst's philosophical analysis.

3. **Gisin (2020-2021):** Constructive real analysis constrains fundamental physics. Our series provides the technical infrastructure for Gisin's programme.

4. **Döring-Isham (2008-2011):** Topos approach to quantum theory. Complementary: they study internal logic of presheaf topoi; we study constructive strength of theorems about operator algebras.

5. **Cubitt et al. (2015):** Undecidability of the spectral gap. Top of our calibration table. Our contribution is the fine structure (BISH, WLPO, LPO) below undecidability.

Verify these engagements exist. If any are missing, add them.

---

## EDIT 11 — PAPER 13 REVIEW FINDINGS

Having reviewed Paper 13's writeup in detail, I note the following about its quality — these may affect what Paper 10 says about it:

**Strengths:**
- The honest decomposition (§2.6) is excellent. Clearly separates BISH cycloid from LPO completed-limit.
- The "What This Does NOT Claim" section (§4.4) is exactly right — preempts the strongest objection without being defensive.
- The encoding objection response (§6.1) is mathematically honest: acknowledges the objection is "mathematically correct and interpretively irrelevant."
- Limitations section (§6.3) is unusually thorough — six explicit limitations including "does not verify the cycloid solves the geodesic equation."

**Points Paper 10 can reference:**
- Paper 13's event-horizon-as-logical-boundary result is the strongest "punchline" for the series — it gives a concrete physical surface where the constructive hierarchy changes.
- The domain invariance (same BMC ↔ LPO, different physics) between Papers 8 and 13 is strong evidence that the calibration is not an artifact of specific encodings.
- Paper 13's Limitation 4 is honest: "Whether this particular instance captures the full logical content of geodesic incompleteness in a more complete formalization of GR is an open question." Paper 10 should cite this transparency.

---

## SUMMARY TABLE

| # | Edit | Priority | Scope |
|---|------|----------|-------|
| 1 | Certification methodology section | **CRITICAL** | ~2 pages, new section |
| 2 | Calibration table: add Papers 11 + 13 | **HIGH** | Table + 2 paragraphs |
| 3 | Working hypothesis: update with full evidence | HIGH | 1 paragraph + evidence list |
| 4 | Domain invariance: Paper 13 ↔ Paper 8 | MEDIUM | 1 paragraph |
| 5 | van Wierst bibliography fix | LOW | 1 entry |
| 6 | MP/WLPO hierarchy verification | MEDIUM | Spot check |
| 7 | Open problems: add infinite-dim entanglement + Penrose | MEDIUM | 2 paragraphs |
| 8 | Abstract update | HIGH | ~6 sentences |
| 9 | DOIs and bibliography updates | LOW | Throughout |
| 10 | Literature positioning: verify completeness | MEDIUM | Spot check |
| 11 | (Reference material for agent, not an edit) | — | — |

| 12 | Paper 28 additions (calibration table + methodology table) | MEDIUM | Table row + 1 paragraph |

**Total revision scope:** ~3–4 pages of new content (mostly the methodology section and calibration table updates), plus spot-checks throughout. The methodology section (Edit 1) is the piece that makes the entire series cohere.

---

## EDIT 12 — ADD PAPER 28 (NEWTON VS. LAGRANGE)

Paper 28 formalizes the constructive stratification of classical mechanics: the Newtonian (equation-of-motion) formulation is BISH while the Lagrangian (variational/optimization) formulation requires FT.

### Calibration table row:

| Layer | Principle | Status | Source |
|-------|-----------|--------|--------|
| Discrete EL equations (harmonic oscillator) | BISH | Calibrated | Paper 28 |
| Discrete action minimizer existence | FT | Calibrated | Paper 28 |

### Methodology table row (§X.4):

| Paper | Full Artifact | Minimal Artifact | Certification |
|-------|-------------|-----------------|---------------|
| 28 | Stratification (401 lines) | — | Structurally verified |

Paper 28 is Level 2 (structurally verified): Classical.choice appears uniformly from Mathlib's ℝ; the BISH/FT separation is established by proof content (explicit algebraic witness vs. EVT reduction). FanTheorem appears as a hypothesis in the FT half but not in the BISH half.

### Significance for §Working Hypothesis:

Paper 28 extends the pattern to classical mechanics: the finite-step algebraic content (solving the EL equation) is BISH, while the variational/optimization framing (asserting a minimizer exists) costs FT. This is a new domain (Lagrangian mechanics) confirming the pattern that non-constructive costs arise from optimization/extremality assertions, not from the equation-of-motion content itself.

### Cross-reference:

Paper 28's Stratification.lean references "Paper 10 §Methodology" for the full discussion of Classical.choice in Mathlib's ℝ. This reference must resolve correctly in the revised Paper 10.

---

## TONE GUIDANCE

Paper 10 is the philosophy paper. Its register differs from the formalization papers:
- Accessible language (not Lean syntax or Mathlib API names)
- Frame technical claims in terms philosophers of physics can evaluate
- Avoid excessive hedging while being honest about limitations
- Make the working hypothesis falsifiable and the open problems genuine
- The right tone: "We have established a methodology, applied it to examples spanning functional analysis, statistical mechanics, quantum information, and general relativity, obtained a consistent pattern, and stated precise conditions under which the pattern could fail."
