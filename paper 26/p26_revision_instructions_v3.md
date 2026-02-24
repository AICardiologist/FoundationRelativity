# Paper 26 Revision Instructions (v3 — FINAL)

## What the math says

Paper 26 proves two things:

1. An injective order-preserving map Φ from Π⁰₁/∼_PA into ℓ∞/c₀ such that Φ([φ]) = 0 iff φ is refutable.

2. A calibration chain: WLPO ↔ Π⁰₁ consistency decidable ↔ gap detection decidable.

**Critical structural fact:** This proof does NOT depend on Paper 2. Paper 2 proved gap detection is WLPO-complete via functional analysis (Ishihara kernel, dual space structure). Paper 26 proves gap detection is WLPO-complete via arithmetic (proof search, Gödel sequences). These are independent proofs of the same result through unrelated constructions.

The paper is therefore: **an independent, arithmetic proof that bidual gap detection is WLPO-complete, together with the explicit reduction (Gödel sequences) that provides it.**

---

## Title

**Change to:** "An Arithmetic Proof That Bidual Gap Detection Is WLPO-Complete"

**Subtitle:** "Gödel Sequences, Explicit Reductions, and a Lean 4 Formalization"

---

## Abstract

Rewrite to say exactly this (in proper academic prose):

We give a new proof that deciding membership in the bidual gap ℓ∞/c₀ is WLPO-complete over Bishop-style constructive mathematics, independent of the functional-analytic proof in [Paper 2]. The proof proceeds via arithmetic: we construct an injective order-preserving map Φ from the Lindenbaum algebra of Π⁰₁ sentences of Peano Arithmetic into ℓ∞/c₀, using bounded proof-search sequences ("Gödel sequences"). We prove Φ([φ]) = 0 iff φ is PA-refutable. Since Π⁰₁ consistency decidability is known to be WLPO-equivalent, this yields gap detection is WLPO-complete by a route entirely independent of [Paper 2]. That two unrelated methods — functional-analytic (Paper 2) and arithmetic (this paper) — both establish WLPO-completeness of gap detection is evidence that this classification is robust. The construction is formalized in Lean 4 (1,213 lines, 30 standard axioms for PA metamathematics, Mathlib-compatible).

---

## Introduction rewrite

**Paragraph 1 — Paper 2's result.** Paper 2 proved that detecting the bidual gap — deciding whether the canonical embedding J_X: X → X** is surjective — is WLPO-complete over BISH. The proof used functional analysis: an Ishihara kernel extracted from a gap witness, reducing gap detection to tail-behavior decidability. This established gap detection as a constructive complexity benchmark.

**Paragraph 2 — The question.** Is Paper 2's result an artifact of its proof method, or is the WLPO-completeness of gap detection a robust classification? An independent proof via different methods would provide evidence for robustness.

**Paragraph 3 — This paper's contribution.** We prove gap detection is WLPO-complete by an entirely different route — through arithmetic rather than functional analysis. The proof constructs an explicit reduction from Π⁰₁ consistency (a known WLPO-complete problem) to gap membership. Each Π⁰₁ sentence φ maps to a "Gödel sequence" v^φ in ℓ∞, constructed from bounded proof search. The sequence lies in c₀ iff φ is refutable. The map is injective on PA-equivalence classes. This reduces Π⁰₁ consistency to gap membership, and since Π⁰₁ consistency is WLPO-complete (Ishihara; Bridges-Richman), gap detection is WLPO-complete.

**Paragraph 4 — Independence.** This proof shares no machinery with Paper 2. Paper 2 works with dual spaces, functionals, and thresholds. This paper works with Gödel numbering, proof predicates, and sentence equivalence. The two proofs arrive at the same classification via independent constructions, confirming that WLPO-completeness of gap detection is not an artifact of either approach.

**Paragraph 5 — Scope and limitations.** The reduction maps into ℓ∞/c₀, which is a mathematical abstraction. The Gödel sequences are engineered from the proof predicate. The paper establishes a complexity-class result, not a physical correspondence. Physical interpretations of WLPO are treated in other papers of the series.

---

## Section title changes

- Discussion/conclusion → "Independence, Robustness, and the Constructive Complexity Classification"
- "The Order-Embedding" → "The Reduction Map" (or "The Gödel Sequence Reduction")
- "Correspondence" anywhere in headings → "Reduction"
- Other section titles: keep as is if they describe technical content accurately

---

## Discussion/Conclusion rewrite

**Point 1 — Two proofs, one result.** Paper 2 and this paper independently prove gap detection is WLPO-complete. Paper 2's proof is functional-analytic: it extracts an Ishihara kernel from a gap witness. This paper's proof is arithmetic: it reduces Π⁰₁ consistency to gap membership via Gödel sequences. The methods share no common machinery. The shared conclusion is therefore robust — WLPO-completeness of gap detection is not an artifact of either proof technique.

**Point 2 — Why two proofs matter.** In complexity theory, a single proof that a problem is NP-complete might depend on features of the specific reduction. Multiple independent reductions from different NP-complete problems provide stronger evidence that the classification is natural. Similarly, two independent proofs of WLPO-completeness from different mathematical domains (functional analysis and arithmetic) provide stronger evidence that gap detection is genuinely WLPO-complete, not just "provably equivalent to WLPO by a clever trick."

**Point 3 — The reduction as complexity-class identification.** The Gödel sequence construction reduces Π⁰₁ consistency to gap membership. Combined with the known WLPO ↔ Π⁰₁ equivalence, this places gap detection in the Π⁰₁ decidability class. Every WLPO-calibrated problem in the CRM programme (bidual gap, decoherence tail behavior, etc.) is therefore Π⁰₁-equivalent — it is exactly as hard as deciding consistency of arithmetic sentences. This gives the WLPO level of the calibration table an arithmetic characterization.

**Point 4 — Relation to Cubitt et al. (BRIEF).** Cubitt-Perez-Garcia-Wolf reduced the halting problem (Σ⁰₁-complete) to spectral gap existence. That sits above LPO in the constructive hierarchy. This paper reduces Π⁰₁ consistency (WLPO-complete) to gap membership in ℓ∞/c₀. Both are reduction results placing analytic problems in arithmetic complexity classes, at different levels of the hierarchy.

**Point 5 — Limitations.** (i) ℓ∞/c₀ is not physical. (ii) Gödel sequences are engineered. (iii) The paper is a complexity-class result, not a physical result. (iv) The order-embedding is not a lattice isomorphism — honestly downgraded. (v) The 30 PA metamathematics axioms are standard but would require significant formalization effort to eliminate.

**Point 6 — What the two proofs together suggest.** Paper 2 showed gap detection is hard for functional-analytic reasons (dual space structure forces WLPO). This paper shows gap detection is hard for arithmetic reasons (Π⁰₁ sentences embed into the gap). That both routes yield WLPO suggests that WLPO-completeness captures something intrinsic about the gap, not something imposed by a particular proof strategy. Whether this intrinsic character can be made precise (e.g., via a completeness theorem for WLPO reductions) is an open question.

---

## Language replacements throughout the paper

| Find | Replace with |
|------|-------------|
| "the bidual gap contains arithmetic incompleteness" | "Π⁰₁ consistency reduces to gap membership" |
| "incompleteness lives inside ℓ∞/c₀" | "the Gödel sequence construction embeds Π⁰₁ sentences into ℓ∞/c₀" |
| "the gap has arithmetic depth" | "gap detection is WLPO-complete, independently confirmed by arithmetic reduction" |
| "Gödel-Gap correspondence" (as name of result) | "Gödel-Gap reduction" or "arithmetic WLPO-completeness proof" |
| "correspondence" (describing the main theorem) | "reduction" |
| "discovers" or "reveals" (about the embedding) | "establishes" or "proves" |
| "meeting point" | do not use |
| "same logical shape" | do not use |
| "contains" (gap contains X) | "admits a reduction from" |
| "witnesses" (gap witnesses X) | "is the target of a reduction from" |

---

## What does NOT change

- All Lean code listings and references
- All theorem statements  
- The Gödel sequence construction (v^φ definition and properties)
- The canonical representative approach (well-definedness)
- The injectivity proof
- The detection theorem (Φ([φ]) = 0 iff refutable)
- The calibration chain proof
- The axiom budget (30 axioms, discussion of each)
- The 3 sorries (discussion of what they are and why they're technical)
- The downgrade from lattice isomorphism to order-embedding
- The remark about generality (works for any consistent recursively axiomatized theory)
- The remark about PA representability for the reverse direction

---

## The one-sentence summary of the revised paper

"We give an arithmetic proof, independent of [Paper 2], that bidual gap detection is WLPO-complete, via explicit reduction from Π⁰₁ consistency through Gödel sequences; formalized in Lean 4."

Every sentence in the paper should serve this summary. If a sentence doesn't serve it, cut it or rewrite it.
