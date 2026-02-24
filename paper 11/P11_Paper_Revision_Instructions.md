# Paper 11 Revision Instructions: Honest Disclosure of Certification Methodology

## Instructions for Writing/Coding Agent

**Goal:** Revise the Paper 11 LaTeX document to accurately describe what the Lean formalization certifies and what the BISH claim rests on. No new Lean code is needed. The existing formalization (500 lines, 8 modules, zero sorry, zero errors) is adequate for the paper's conclusion. This is a paper edit only.

**Context:** An internal audit of the CRM paper series identified Paper 11 as having the widest gap between its claim ("Tsirelson bound and Bell entropy are BISH") and its formal certification (`#print axioms` shows `[propext, Classical.choice, Quot.sound]` throughout). The BISH claim is mathematically correct — nobody disputes that finite-dimensional matrix algebra is constructive. But the paper must be precise about *how* it knows this: the Lean artifact verifies proof correctness; the BISH status is established by mathematical argument about the proof's content, not by a Classical.choice-free axiom certificate.

---

## What Does NOT Need Changing

- The Lean code: leave it exactly as is. Zero sorry, zero errors, zero warnings. Adequate.
- The theorem statements: correct as stated.
- The calibration table entries: BISH for Tsirelson, BISH for Bell entropy, BISH for partial trace. All correct.
- The overall narrative: Paper 11 establishes that quantum compositional structure (tensor products, entanglement, correlations) is constructively free. This is the correct punchline.

---

## What MUST Change

### 1. Section 6: "The Classical.choice Question" — Complete Rewrite

The current Section 6 (titled "The Classical.choice Question") needs to be rewritten to be more precise and less defensive. The current version argues that `Classical.choice` is "purely architectural" — which is true but informally justified. The revision should:

**Replace the current Section 6 with the following structure:**

#### §6.1 The Axiom Profile

State the facts plainly:

> All theorems in this paper — `tsirelson_bound`, `bellState_partialTrace`, `bellState_entropy` — carry the axiom profile `[propext, Classical.choice, Quot.sound]`. The `Classical.choice` dependency enters through Mathlib's typeclass resolution infrastructure, specifically through `Decidable` instances on ℝ and ℂ that Lean inserts automatically when resolving inner product space and matrix algebra typeclasses.

#### §6.2 What the Formalization Certifies

Be explicit about the two distinct claims:

> The Lean formalization provides two kinds of evidence:
>
> First, **proof correctness**: the theorem statements are correctly formalized, the proofs compile without sorry, and the proof chain is machine-checked. This is the primary function of the artifact.
>
> Second, **proof structure**: the proof steps consist entirely of finite-dimensional matrix algebra — Kronecker products, dot products, explicit matrix computation via `fin_cases`, algebraic identities verified by `ring` and `norm_num`. No step invokes limits, suprema, convergence, or decidability of real-number equality.

#### §6.3 What the Formalization Does NOT Certify

This is the key addition. Be honest:

> The formalization does **not** provide a mechanical certificate of constructive purity. Because Mathlib imports `Classical.choice` at the library level, `#print axioms` cannot distinguish between theorems that genuinely require classical reasoning and theorems that inherit classical dependencies through infrastructure. A mechanical BISH certificate would require either (a) a Mathlib-free formalization of the relevant linear algebra, or (b) a constructive Lean library that separates classical and constructive content at the typeclass level. Neither currently exists.
>
> The BISH claim therefore rests on **mathematical argument**: the proof content is finite-dimensional linear algebra over explicitly given matrices, which is uncontroversially constructive in the CRM literature. This is the standard methodology of constructive reverse mathematics, where the metatheory (here Lean + Mathlib) is classical, and the object-level claim (here "the proof is BISH") is established by inspecting the proof's mathematical content.

#### §6.4 Comparison with Other Papers in the Series

Keep the comparison table but update the framing:

| Paper | Result | Axiom Profile | Certification Level |
|-------|--------|---------------|-------------------|
| Paper 2 | Bidual gap ↔ WLPO | Clean in P2_Minimal | **Mechanically certified** (dependency-free artifact) |
| Paper 8 | Ising Part A: BISH | `Classical.choice` | Structurally verified (Mathlib infra) |
| Paper 8 | Ising Part B: LPO | `Classical.choice` + `bmc_of_lpo` | Intentional classical content |
| Paper 11 | Tsirelson bound | `Classical.choice` | **Structurally verified** (Mathlib infra) |
| Paper 11 | Bell entropy | `Classical.choice` | **Structurally verified** (Mathlib infra) |

> Paper 2's P2_Minimal artifact represents the gold standard: a dependency-free build target that mechanically certifies constructive purity. Papers 8 and 11 use the weaker "structurally verified" methodology, where the BISH claim is supported by mathematical argument about proof content rather than by a clean axiom certificate. A systematic treatment of the certification methodology across the series is given in Paper 10 [Lee 2026, §X].

---

### 2. Abstract — Minor Qualification

The current abstract says something like "the results calibrate the compositional layer at the BISH level." Add one sentence of qualification:

> The `Classical.choice` dependency in the axiom profile arises from Mathlib's typeclass infrastructure rather than from the mathematical content; the BISH calibration is established by proof-content analysis within the standard CRM methodology (see §6).

This is one sentence. Don't overdo it.

---

### 3. §5.2 "Significance" Discussion — Add One Paragraph

After the existing discussion of why BISH calibration of entanglement is non-trivial, add:

> A methodological note: the BISH status of Paper 11's results is, in some sense, expected — finite-dimensional linear algebra is paradigmatically constructive. The value of the formalization is not in *discovering* that matrix multiplication is constructive, but in *demonstrating* within a machine-checked framework that the conceptual infrastructure of quantum entanglement — the CHSH operator construction, the partial trace, the entropy computation — compiles correctly and carries no hidden non-constructive dependencies beyond the ambient library's classical foundation. The artifact is primarily a verification of correctness; the calibration claim is a consequence of the proof's mathematical content.

---

### 4. Remove Overclaimed `#print axioms` Expectations

The original blueprint (§5.1) had comments like:

```
-- Expected: [propext, Quot.sound]
-- NO Classical.choice
```

If any version of these expectations appears in the paper or in code comments, **remove them or correct them**. The actual output is `[propext, Classical.choice, Quot.sound]`, and the paper should state this accurately. Do not claim the axiom profile is what you wished it were.

In `Main.lean` or in any code listings in the paper, the comments should read:

```lean
#print axioms tsirelson_bound
-- Output: [propext, Classical.choice, Quot.sound]
-- Classical.choice enters via Mathlib typeclass infrastructure.
-- The mathematical content is finite-dimensional matrix algebra (BISH).
```

---

### 5. Reference to Paper 10 Methodology Section

Add a forward reference to Paper 10's methodology section (which addresses the Classical.choice issue across the entire series). Something like:

> For a systematic treatment of the relationship between Mathlib's classical foundations and the series' constructive claims, see Paper 10 [Lee 2026], §X, which establishes three levels of certification — mechanically certified, structurally verified, and paper-level — and classifies each paper accordingly.

If Paper 10 doesn't yet have a DOI, use "[forthcoming]".

---

## What NOT to Do

1. **Do NOT add a P11_Minimal artifact.** The audit concluded this is unnecessary. Finite-dimensional matrix algebra being BISH is obvious; a dependency-free artifact would be expensive engineering for a trivially true claim.

2. **Do NOT remove the `Classical.choice` discussion.** Transparency is a feature, not a bug. The paper is stronger for addressing it than for ignoring it.

3. **Do NOT weaken the BISH claim.** The results ARE BISH. The paper should say so clearly. The revision is about being precise about *how we know* they are BISH (mathematical argument + proof structure analysis), not about hedging the claim itself.

4. **Do NOT add extensive philosophical discussion.** The Section 6 rewrite should be 1-1.5 pages. Don't turn it into a philosophy paper about classical metatheories. State the facts, acknowledge the limitation, point to Paper 10 for the full treatment, move on.

5. **Do NOT restructure the rest of the paper.** Sections 1-5 and 7 are fine. The revision is surgical: Section 6, one sentence in the abstract, one paragraph in §5.2, corrected code comments.

---

## Summary of Edits

| Section | Action | Scope |
|---------|--------|-------|
| Abstract | Add one qualifying sentence about Classical.choice | ~1 sentence |
| §5.2 | Add methodological paragraph | ~1 paragraph |
| §6 | Complete rewrite with §6.1-6.4 structure | ~1.5 pages |
| Code listings / comments | Correct `#print axioms` expectations | A few lines |
| References | Add forward reference to Paper 10 methodology | ~1 sentence |

**Total revision scope:** ~2 pages of new/revised text. The rest of the paper is untouched.

---

## Tone Guidance

The revision should be **confident but precise**. The results are correct. The BISH claim holds. The only thing being fixed is the *epistemology* — how we justify the claim. The tone should be: "Here is what the artifact certifies, here is what the mathematical argument establishes, here is the gap between the two, and here is why the gap doesn't undermine the conclusion." No hand-wringing, no excessive hedging, no apology. Just accuracy.
