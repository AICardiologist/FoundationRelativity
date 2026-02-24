# Paper 27 Edit Instructions

## Overview

Paper 27 is well-framed and mostly correct. These are minor edits to align P26 references with P26's v3 revision and fix a few small issues. No structural rewrite needed.

---

## Edit 1: Update P26 reference in Discussion §7.1 (lines 576–579)

**Current text:**
"Paper 26 achieved a full correspondence between the Lindenbaum algebra $\Pi^0_1/{\sim_{\mathsf{PA}}}$ and the bidual gap $\ell^\infty/c_0$, with a clean detection theorem: an element is zero if and only if the sentence is refutable."

**Replace with:**
"Paper 26 gave an independent arithmetic proof that bidual gap detection is WLPO-complete, via an explicit reduction from $\Pi^0_1$ consistency: the Gödel sequence construction maps each $\Pi^0_1$ sentence to an element of $\ell^\infty/c_0$ that is zero if and only if the sentence is refutable."

**Reason:** P26's v3 revision reframes it as a reduction theorem / independent WLPO-completeness proof, not a "full correspondence."

---

## Edit 2: Update P26 reference in Discussion §7.1 (lines 579–580)

**Current text:**
"The present paper does not achieve the analogous result for $\LLPO$ and Bell correlations."

**Replace with:**
"The present paper does not attempt an analogous reduction for $\LLPO$ and Bell correlations."

**Reason:** "Does not achieve" implies failure. "Does not attempt" is accurate — it was a deliberate scope decision.

---

## Edit 3: Update comparison table (line 648)

**Current:**
| Feature | Paper 26 | Paper 27 |
| Direction | Full correspondence | Forward calibration |
| Logical algebra | Π⁰₁/∼ | IVT instances |

**Change to:**
| Feature | Paper 26 | Paper 27 |
| Direction | Reduction (both directions) | Forward calibration |
| Logical algebra | Π⁰₁/∼_PA | — |

**Reason:** P26 is now framed as a reduction, not a correspondence. P27 doesn't build an algebraic structure of IVT instances, so "—" is more honest than implying it does.

---

## Edit 4: Update P26 bibliography entry (lines 717–718)

**Current:**
"Paper 26: Arithmetic incompleteness inside the bidual gap---a Lean 4 formalization."

**Replace with:**
"Paper 26: An arithmetic proof that bidual gap detection is WLPO-complete---a Lean 4 formalization."

**Reason:** Match P26's revised title.

---

## Edit 5: Soften categorical speculation (lines 659–661)

**Current text:**
"Whether this pattern extends to a categorical framework (a functor from constructive principles to physical theories) remains an open question."

**Replace with:**
"Whether calibrations at different levels of the hierarchy share enough structural uniformity to support a categorical framework remains open. Papers 26 and 27 operate at different constructive levels with different proof architectures (reduction vs.\ forward calibration), so the evidence for uniform structure is currently limited."

**Reason:** P26 and P27 don't have the same proof shape. Claiming they're "two data points" for a categorical pattern overstates what they provide. Be honest about the gap.

---

## Edit 6: Update Level 3 label in stratification diagram (line 626)

**Current:**
"Gap detection in $\ell^\infty/c_0$ (Paper 26)"

**Replace with:**
"Gap detection in $\ell^\infty/c_0$ (Papers 2, 26)"

**Reason:** Paper 2 established the WLPO ↔ gap detection result. Paper 26 gave an independent proof. Citing only P26 here omits the original result.

---

## Nothing else changes

The abstract, introduction, technical sections, axiom audit, stratification theorem, mechanism explanation, conclusion, and all Lean code listings are correct as written. The paper's scope (forward calibration + mechanism explanation) is right and does not need adjustment.
