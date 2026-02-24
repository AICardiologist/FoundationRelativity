# Terminology Concordance

## Note on Terminology

The author is a medical professional, not a specialist in constructive analysis or reverse mathematics. This program was developed as an outsider's investigation into the logical structure of mathematical physics. In several cases, the author coined terminology independently before discovering the standard vocabulary — effectively reinventing the wheel, and sometimes giving it a different name. This concordance maps the program's non-standard terms to their established equivalents, both as a service to readers coming from constructive analysis and as an honest acknowledgment that better names already existed in many cases. Where the program's term has been retained despite a standard alternative, the reason is noted.

---

## Core Terminology

### Bidual Gap

- **Standard term:** Non-reflexivity of Banach spaces; failure of the canonical embedding $X \hookrightarrow X^{**}$ to be surjective.
- **Program term:** Bidual gap.
- **Note:** "Bidual gap" was coined before the author encountered the standard terminology. "Non-reflexivity" is a negation describing what fails; "bidual gap" names the positive geometric phenomenon — a measurable distance between $X$ and $X^{**}$. The non-standard term has been retained in titles for accessibility, but all papers using it should include "non-reflexivity" in the abstract and keywords to ensure discoverability.

### Scaffolding

- **Standard term:** Dispensable / eliminable (proof-theoretic contexts); artefact (physics contexts).
- **Program term:** Scaffolding.
- **Definition:** A mathematical principle is *scaffolding* for a physical prediction if the prediction can be derived without that principle — i.e., the principle is eliminable. The metaphor is architectural: the structure is used during construction but is not part of the finished building.

### Axiom Cost

- **Standard term:** Proof-theoretic strength; reverse-mathematical classification; calibration level.
- **Program term:** Axiom cost.
- **Note:** "Proof-theoretic strength" suggests a total ordering (stronger/weaker), which is misleading for independent principles such as the Fan Theorem and LPO. "Axiom cost" conveys the economic metaphor — each theorem has a price in logical resources — which aligns with the program's cost-benefit framing of mathematical idealisation.

### Axiom Calibration

- **Standard term:** Reverse-mathematical classification; proof-theoretic calibration.
- **Program term:** Axiom calibration.
- **Note:** The physical analogy is deliberate: one calibrates an instrument against known standards before deploying it on unknown targets. The term "calibration" is already used informally in the constructive reverse mathematics literature.

### Logical Geography

- **Standard term:** Reverse-mathematical classification; proof-theoretic landscape.
- **Program term:** Logical geography.
- **Note:** Used in Paper 10's title to signal that the paper is a survey and atlas — a map of the logical terrain of mathematical physics — rather than a proof of a single theorem.

### Omniscience Spine

- **Standard term:** Omniscience hierarchy; omniscience principles.
- **Program term:** Omniscience spine.
- **Note:** "Hierarchy" suggests a total order, which is correct for the linear chain LLPO < WLPO < LPO but misleading when the Fan Theorem and Dependent Choice are included (both are independent of the chain). "Spine" suggests the central linear chain with branches — more accurate for the full picture. The standard terms "omniscience principles" or "omniscience hierarchy" are used in technical sections throughout the program.

### Bridge Axiom

- **Standard term:** No exact equivalent. Closest: physical axiom, empirical hypothesis, domain axiom.
- **Program term:** Bridge axiom.
- **Definition:** A bridge axiom encodes a single, well-established physical fact as a typed axiom in Lean 4. The Lean type-checker verifies that theorems follow *from* bridge axioms; it does not verify the bridge axioms themselves. Bridge axioms are the program's interface between formal mathematics and empirical physics. The term is original to this program because the methodology itself — encoding physics as typed axioms in a proof assistant for constructive calibration — is novel.

### The Diagnostic

- **Standard term:** No equivalent.
- **Program term:** The diagnostic; the calibration framework; the instrument.
- **Note:** Refers to the complete methodology: formalise a physical result in Lean 4, identify bridge axioms encoding the physics, determine the minimal constructive principle beyond BISH required for the proof, and record the result in the calibration table. "The axiom calibration framework" is used in technical writing; "the diagnostic" appears in discussion sections.

---

## Constructive Analysis Terminology

### BISH, LPO, WLPO, LLPO

Standard throughout. No discrepancy with the literature. Bishop's constructive mathematics (BISH) and the Limited Principle of Omniscience and its variants are used in their established senses (Bishop 1967; Bridges–Richman 1987; Ishihara 2006).

### Fan Theorem (FT)

- **Standard statement:** The Fan Theorem concerns uniform continuity of functions on the Cantor fan, or equivalently bar induction on the binary tree.
- **Program usage:** FT is sometimes formulated as the extreme value theorem (EVT) for continuous functions on $[0,1]$, which is equivalent to the standard Fan Theorem (Julian–Richman; see Bridges–Richman 1987 or Diener 2018, Chapter 3).
- **Note:** The equivalence FT ↔ EVT should be cited explicitly whenever the EVT formulation is used, to avoid ambiguity about which principle is intended.

### Bounded Monotone Convergence (BMC)

- **Standard term:** BMC is used in the literature, but the precise formulation matters.
- **Program usage:** BMC asserts that every bounded monotone sequence of reals converges, without requiring a computable modulus of convergence. The equivalence BMC ↔ LPO under this formulation is established by Ishihara (2006) and formalised in Paper 29 via Fekete's subadditive lemma.

### Dependent Choice (DC)

Standard. The program distinguishes DC (countable dependent choice) from DC$_\omega$ (dependent choice for natural-number-indexed sequences). This distinction is standard in the constructive analysis literature.

### Markov's Principle (MP)

Standard. "If a computation cannot fail to halt, then it halts." No discrepancy.

---

## Formalisation Terminology

### Bridge Axiom Assembly

- **Standard term:** No equivalent.
- **Program term:** A theorem that combines bridge axioms with genuine proofs. Distinguished from "genuine proof" (uses no bridge axioms) in the CRM audit tables accompanying each paper.

### CRM Audit

- **Standard term:** No equivalent.
- **Program term:** CRM audit; axiom audit.
- **Note:** The table in each paper classifying every theorem as "genuine proof," "bridge axiom assembly," or "intentional classical." Introduced in Paper 10's methodology section. This classification is a methodological contribution of the program.

### Zero-Sorry Build

- **Standard term:** "Complete formalisation" or "fully verified" (in the Lean community).
- **Program term:** Zero-sorry build; 0-sorry.
- **Definition:** The Lean 4 build compiles with no `sorry` — Lean's marker for unproved assertions — confirming that every stated theorem follows logically from the declared axioms. This is standard terminology in the Lean community but may be unfamiliar to readers from constructive analysis or physics.

---

## Terms with No Non-Standard Usage

The following terms are used in their standard senses throughout the program and require no concordance entry: thermodynamic limit, perturbative/non-perturbative, Page time, Casimir energy, entanglement entropy, holographic dictionary, Ryu–Takayanagi formula, QES (quantum extremal surface), Fekete's subadditive lemma, Picard–Lindelöf theorem, Weihrauch degree.
