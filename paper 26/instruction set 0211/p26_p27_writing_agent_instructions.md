# Papers 26 & 27: Revision Instructions for Writing Agent

## Overview

You have two papers to revise and three new TikZ figures to insert. Paper 26 needs a substantial framing rewrite (title, abstract, introduction, discussion, conclusion). Paper 27 needs six minor edits. The technical sections (theorems, proofs, Lean code, axiom audits) in both papers are correct and do not change.

You also have access to the full collection of papers in the series. Use them to **verify** specific claims before finalizing edits.

---

# PART 1: PAPER 26 REVISION

## Source files
- **Paper to revise:** `paper26_godel_gap.tex`
- **Revision instructions:** `p26_revision_instructions_v3.md` (the ONLY version to use — ignore v1 and v2)
- **New Figure 1 (proof search):** `p26_new_figure.tex` — insert in §5 after Definition 5.1, before Theorem 5.2
- **New Figure 3 (physical chain):** `p26_physical_figure.tex` — insert in the revised Discussion section

## What changes

### Title
**Old:** "The Gödel-Gap Correspondence: Arithmetic Incompleteness Inside the Bidual Gap ℓ∞/c₀"
**New:** "An Arithmetic Proof That Bidual Gap Detection Is WLPO-Complete: Gödel Sequences, Explicit Reductions, and a Lean 4 Formalization"

### Abstract
Complete replacement. See `p26_revision_instructions_v3.md` for the full text. Key framing: independent proof of WLPO-completeness via arithmetic, not "discovery" of incompleteness inside the gap.

### Introduction
Complete rewrite into 5 paragraphs. See v3 instructions for the paragraph-by-paragraph structure:
1. Paper 2's result
2. The question (is WLPO-completeness robust or artifact?)
3. This paper's contribution (arithmetic route)
4. Independence from Paper 2
5. Scope and limitations

### Discussion (§8)
Complete rewrite into 6 subsections per v3 instructions:
1. Two proofs, one result
2. Why two proofs matter (NP-completeness analogy)
3. Reduction as complexity-class identification
4. Comparison with Cubitt et al. (BRIEF)
5. Limitations (5 items — be honest)
6. What the two proofs together suggest

### Conclusion (§9)
Rewrite to match revised framing. No "contains," no "natural analytic habitat," no "structural necessity." State: two independent proofs confirm WLPO-completeness is robust. The Π⁰₁ characterization gives WLPO an arithmetic identity.

### Section title changes
- "The Gödel-Gap Correspondence" → "The Gödel Sequence Reduction"
- "Arithmetic Incompleteness Inside the Bidual Gap" (discussion heading) → "Independence, Robustness, and Limitations"
- "Correspondence" in any heading → "Reduction"

### Language replacements (throughout entire paper)
Apply these systematically — search and replace in all sections including technical ones:

| Find | Replace with |
|------|-------------|
| "the bidual gap contains arithmetic incompleteness" | "Π⁰₁ consistency reduces to gap membership" |
| "incompleteness lives inside ℓ∞/c₀" | "the Gödel sequence construction embeds Π⁰₁ sentences into ℓ∞/c₀" |
| "the gap has arithmetic depth" | "gap detection is WLPO-complete, independently confirmed by arithmetic reduction" |
| "Gödel-Gap correspondence" (as name of result) | "Gödel sequence reduction" or "arithmetic WLPO-completeness proof" |
| "correspondence" (describing the main result) | "reduction" |
| "discovers" or "reveals" (about the embedding) | "establishes" or "proves" |
| "contains" (gap contains X) | "admits a reduction from" |
| "witnesses" (gap witnesses X) | "is the target of a reduction from" |
| "natural analytic habitat" | delete entirely |
| "structural necessity" | delete or replace with "consequence of the reduction" |
| "meeting point" | do not use |
| "same logical shape" | do not use |

**Exception:** The existing Figure 2 (the map Φ diagram in §6) can keep "Gödel-Gap map Φ" in its caption, or change to "reduction map Φ" — either is fine since it's labeling the mathematical object, not making a philosophical claim.

### Existing Figure 2 (§6, the Φ diagram)
Keep the diagram unchanged. Optionally update caption: "The Gödel-Gap map Φ" → "The reduction map Φ."

### §8.4 "Arithmetic Complexity of Physical Theories" — CRITICAL
The current text claims LLPO governs Σ⁰₁ disjunctions and LPO governs full Σ⁰₁ decidability. **Paper 26 does NOT prove these claims.** It only establishes the WLPO/Π⁰₁ instance. Options:
- (a) Cut the subsection entirely and note "arithmetic characterization of other hierarchy levels is deferred to the survey"
- (b) Keep but explicitly mark the LLPO and LPO claims as conjectural, citing the specific papers that establish those calibrations (if they exist)

**VERIFICATION TASK:** Check Papers 8, 10, 13, 21, 27 to see if any of them explicitly prove LLPO ↔ Σ⁰₁ disjunction or LPO ↔ Σ⁰₁ decidability. If not, these claims must be marked as conjectural or removed.

## What does NOT change
- All Lean code listings and references
- All theorem statements (Theorems 5.2, 5.3, 6.1, 6.2, 6.3, 7.1, 7.2)
- The Gödel sequence construction (Definition 5.1)
- The canonical representative approach
- The injectivity proof
- The detection theorem
- The calibration chain proof
- The axiom budget (30 axioms) and discussion of each
- The 3 sorries discussion
- The generality remark (works for any consistent recursively axiomatized theory)
- The PA representability remark
- The AI methodology section
- The module structure table
- §§2–7 technical content (except language replacements per the table above)

---

# PART 2: PAPER 27 EDITS

## Source file
- **Paper to revise:** `paper27_llpo_bell.tex`
- **Edit instructions:** `p27_edit_instructions.md`

## Six edits (all minor)

### Edit 1: Lines 576–579
**Old:** "Paper 26 achieved a full correspondence between the Lindenbaum algebra..."
**New:** "Paper 26 gave an independent arithmetic proof that bidual gap detection is WLPO-complete, via an explicit reduction from Π⁰₁ consistency..."

### Edit 2: Lines 579–580
**Old:** "does not achieve the analogous result"
**New:** "does not attempt an analogous reduction"

### Edit 3: Comparison table (line 648)
Change Paper 26's "Direction" from "Full correspondence" to "Reduction (both directions)"
Change Paper 27's "Logical algebra" from "IVT instances" to "—"

### Edit 4: Bibliography (lines 717–718)
**Old:** "Paper 26: Arithmetic incompleteness inside the bidual gap"
**New:** "Paper 26: An arithmetic proof that bidual gap detection is WLPO-complete"

### Edit 5: Lines 659–661
**Old:** "Whether this pattern extends to a categorical framework..."
**New:** "Whether calibrations at different levels of the hierarchy share enough structural uniformity to support a categorical framework remains open. Papers 26 and 27 operate at different constructive levels with different proof architectures (reduction vs.\ forward calibration), so the evidence for uniform structure is currently limited."

### Edit 6: Stratification diagram (line 626)
**Old:** "Gap detection in ℓ∞/c₀ (Paper 26)"
**New:** "Gap detection in ℓ∞/c₀ (Papers 2, 26)"

## Nothing else changes in Paper 27

---

# PART 3: VERIFICATION TASKS

Before finalizing, verify the following claims against the actual papers in the series. You have all papers available.

### V1: Paper 2 independence
Confirm that Paper 2 proves WLPO ↔ gap detection via functional analysis (Ishihara kernel, dual space structure), NOT via arithmetic/Gödel sequences. This establishes that P26's proof is genuinely independent.
**Check:** Paper 2's main theorem and proof method.

### V2: Paper 7 WLPO calibration
Confirm that Paper 7 proves constructive witnessing of singular states in S₁(H) requires WLPO. This is cited in Figure 3 (physical chain).
**Check:** Paper 7's main theorem.

### V3: Paper 9 WLPO calibration
Confirm that Paper 9 calibrates decoherence at WLPO (not some other level). Figure 3 cites it.
**Check:** Paper 9's calibration result.

### V4: Paper 13 LPO calibration
Confirm that Paper 13 calibrates Schwarzschild geodesic incompleteness at LPO (NOT WLPO). This is why Figure 3 does NOT include geodesics — they're one level higher.
**Check:** Paper 13's main theorem.

### V5: Paper 21 LLPO calibration
Confirm Paper 21 proves LLPO ↔ BellSignDecision. Paper 27 cites this.
**Check:** Paper 21's main theorem.

### V6: LLPO ↔ Σ⁰₁ disjunction claim
Search Papers 10, 21, 27 for any proof that LLPO is equivalent to Σ⁰₁ disjunction decidability. Paper 26 §8.4 currently asserts this. If no paper proves it, flag it for removal or mark as conjectural.

### V7: LPO ↔ Σ⁰₁ decidability claim
Search Papers 8, 10, 13 for any proof that LPO is equivalent to full Σ⁰₁ decidability. Paper 26 §8.4 currently asserts this. If no paper proves it, flag it for removal or mark as conjectural.

### V8: Paper 26 axiom count
The paper claims 30 custom axioms. Verify this matches the Lean formalization if available. (Low priority — trust the existing count unless you find contradictory evidence.)

### V9: Paper 27 axiom count
The paper claims 6 axioms. The P27 edit instructions say 6. The abstract says 6. Verify consistency.

---

# PART 4: FIGURE INSERTION

## Figure 1: Proof-search process
- **File:** `p26_new_figure.tex`
- **Location in P26:** §5 (The Gödel Sequence), after Definition 5.1, before Theorem 5.2
- **Label:** `fig:proof-search`
- **Purpose:** Shows how a single Gödel sequence is generated step-by-step by bounded proof search, with branching into consistent (all 1s forever) and refutable (drops to 0) outcomes. WLPO annotated at bottom.

## Figure 2: The reduction map Φ (EXISTING)
- **Already in paper** at §6
- **Label:** `fig:godelgap`
- **Change:** Optionally update caption from "Gödel-Gap map" to "reduction map." Diagram stays as is.

## Figure 3: Physical chain
- **File:** `p26_physical_figure.tex`
- **Location in P26:** Discussion section (revised §8), near the "Limitations" subsection or at the start of the discussion
- **Label:** `fig:physical-chain`
- **Purpose:** Shows three physical questions (Papers 2, 7, 9) all formalizing to WLPO, with Paper 26 providing arithmetic explanation. Prevents reader from confusing "gap encodes arithmetic" with "physics is arithmetic."
- **CRITICAL:** All three physical examples must calibrate at WLPO. Do NOT include geodesic incompleteness (that's LPO, Paper 13). The three examples are: signal vanishing (P2), singular state witness (P7), decoherence completion (P9). Run verification tasks V2 and V3 to confirm.

---

# PART 5: ONE-SENTENCE SUMMARIES

After revision, each paper should serve exactly one summary:

**Paper 26:** "We give an arithmetic proof, independent of Paper 2, that bidual gap detection is WLPO-complete, via explicit reduction from Π⁰₁ consistency through Gödel sequences; formalized in Lean 4."

**Paper 27:** "LLPO is equivalent to the exact Intermediate Value Theorem; Bell angle optimization reduces to IVT instances; therefore angle-finding calibrates at LLPO, strictly below gap detection (WLPO); formalized in Lean 4 with zero sorries."

Every sentence in each paper should serve its summary. If a sentence doesn't serve it, cut it or rewrite it.
