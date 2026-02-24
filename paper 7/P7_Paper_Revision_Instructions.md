# Paper 7 Revision Instructions: Certification Methodology and P7_Minimal Integration

## Instructions for Writing Agent

**Goal:** Revise the Paper 7 LaTeX document (`paper7_writeup.tex`) to (1) add honest disclosure of the Classical.choice / BISH certification methodology (same framework as Paper 11), (2) reference the forthcoming P7_Minimal artifact, and (3) fix any remaining issues identified in the series-wide audit. No changes to the Lean code (P7_Full) are needed.

**Current state of Paper 7:**
- 754 lines Lean 4, 8 files, 7/8 sorry-free (only `Instance.lean` has sorry)
- 1 interface axiom: `ell1_not_reflexive` (engineering boundary, not mathematical gap)
- `wlpo_of_nonreflexive_witness` eliminated via 196-line Ishihara kernel adaptation
- Key technical contribution: Lemma B (closed subspace of reflexive is reflexive) via Hahn-Banach, not James's theorem — not in Mathlib4
- Axiom profile: `[propext, Classical.choice, Quot.sound]` + `ell1_not_reflexive`
- Paper: 15 pages, compiled, all four previous reviewer issues resolved
- Zenodo DOI: 10.5281/zenodo.18509795

---

## Edit 1: Add Certification Methodology Section (~1 page)

### Location: New §6.3 or expand existing §6

The current §6 ("Interface Assumptions") discusses the `ell1_not_reflexive` axiom and the engineering boundary with Paper 2. It needs a new subsection addressing the Classical.choice issue — parallel to Paper 11's §6 but tailored to Paper 7's specifics.

### Content for new subsection: "§6.X The Classical Metatheory"

Write the following (adapt tone and length to match the existing paper style):

**§6.X.1 Axiom Profile**

> All theorems in the P7_Full formalization carry the axiom profile `[propext, Classical.choice, Quot.sound]` plus the interface assumption `ell1_not_reflexive`. The `Classical.choice` dependency enters through Mathlib's normed space and functional analysis infrastructure — specifically through the Hahn-Banach theorem (`exists_extension_norm_eq`), the `NormedSpace` typeclass hierarchy, and `Decidable` instances on ℝ.

**§6.X.2 What the Formalization Certifies**

> The Lean formalization provides two forms of evidence. First, proof correctness: the theorem statements are correctly formalized, the proofs compile without sorry (in 7 of 8 files), and the proof chain — from the Ishihara kernel construction through Lemma B to the main equivalence — is machine-checked. Second, proof structure: the forward direction (non-reflexivity witness → WLPO) uses the Ishihara kernel construction, which is a constructive algorithm with no classical case analysis; the reverse direction (WLPO → non-reflexivity) uses WLPO explicitly as a hypothesis, and the Lemma B step (closed subspace of reflexive is reflexive) uses Hahn-Banach extension and geometric separation, both of which are constructively available for separable spaces [Bridges and Vîță 2006, §4.3].

**§6.X.3 Certification Levels**

> The BISH claim for the overall equivalence rests on mathematical argument about proof content, not on a Classical.choice-free axiom certificate. A forthcoming supplementary artifact (P7_Minimal) will provide a dependency-free logical skeleton — analogous to the P2_Minimal artifact of Paper 2 [Lee 2026a] — that certifies the reduction structure without Mathlib. In P7_Minimal, the forward direction (Ishihara kernel) and Lemma B are axiomatized with references to their P7_Full proofs, and the logical chain is verified to use no classical axioms beyond the explicitly listed assumptions. The P7_Full proofs supply the mathematical content; P7_Minimal certifies the logical architecture.
>
> For a systematic treatment of the certification methodology across the series, see Paper 10 [Lee 2026, forthcoming].

**NOTE TO AGENT:** If P7_Minimal has already been built by the time this edit is made, replace "forthcoming" with the actual build status and axiom output. If not, keep "forthcoming."

---

## Edit 2: Mention P7_Minimal in the Reproducibility Box

### Location: The existing reproducibility box (mdframed environment)

Add a new item:

```latex
\item \textbf{Minimal artifact (forthcoming)}: \texttt{Papers.P7\_PhysicalBidualGap.P7\_Minimal.Main}
  — dependency-free logical skeleton, no Mathlib imports.
  Axiomatizes Lemma B and Ishihara kernel; certifies reduction chain
  with no \texttt{Classical.choice}.
```

If P7_Minimal already exists and has been built, update with actual status (zero sorry, zero errors, and `#print axioms` output).

---

## Edit 3: Fix §8.2 Markov's Principle — VERIFY THIS WAS DONE

In a previous revision round, I flagged that §8.2 incorrectly stated "WLPO is implied by Markov's Principle." This was reported as fixed, with the corrected text stating: LPO ⇒ WLPO ⇒ LLPO, with LPO independently implying MP, while MP is independent of WLPO over BISH.

**Agent task:** Verify this correction is present in the current version. If you see any claim that MP implies WLPO or WLPO implies MP, it is wrong. The correct relationships are:

```
LPO → WLPO → LLPO
LPO → MP
MP and WLPO are independent over BISH
```

Cite: Bridges and Vîță 2006, Theorem 1.3 and surrounding discussion.

---

## Edit 4: Strengthen the Physical Discussion (§8)

The audit noted that Paper 7 is "physically understated." The connection to algebraic quantum field theory is the strongest physics angle and should be more prominent. Check that §8 includes the following points (from earlier review discussions). If any are missing, add them:

**4a. Normal vs. Singular States**

> In the algebraic formulation of quantum mechanics (Bratteli-Robinson, Vol. 2, Chapter 5), the space S₁(H) represents normal states on the observable algebra B(H). The bidual B(H)* contains singular states — linear functionals that cannot be represented by any density matrix. The decomposition ω = ω_n + ω_s into normal and singular components is the noncommutative analogue of the Lebesgue decomposition. Our result calibrates the logical cost of this decomposition: constructively *exhibiting* a singular state (rather than merely proving normality fails) requires exactly WLPO.

**4b. Thermodynamic Limit**

> In the thermodynamic limit (infinite volume), finite-volume Gibbs states (density matrices in S₁(H)) may converge to states that are singular with respect to the identity representation. The KMS condition for thermal equilibrium at inverse temperature β defines states on the quasilocal algebra that, in general, are not normal. The WLPO cost of singular-state existence thus calibrates the logical strength of the thermodynamic limit in quantum statistical mechanics, complementing Paper 8's LPO calibration for the classical (1D Ising) thermodynamic limit.

**4c. Superselection Sectors**

> Singular states produce GNS representations disjoint from the identity representation, corresponding physically to inequivalent thermodynamic phases and superselection sectors. The WLPO boundary thus demarcates not just a mathematical distinction (reflexive vs. non-reflexive) but a physical one (states representable by density matrices vs. states requiring the full bidual).

If these points are already in §8, no action needed. If they are present but brief, consider expanding slightly. If absent, add as a subsection "§8.X Physical Interpretation."

---

## Edit 5: Abstract — Add Certification Qualification

Same pattern as Paper 11. Add one sentence to the abstract:

> The `Classical.choice` dependency in the axiom profile arises from Mathlib's functional analysis infrastructure; the constructive validity of the equivalence is established by proof-content analysis within the standard CRM methodology (see §6.X). A dependency-free logical skeleton (P7_Minimal) supplementing this formalization is [available / forthcoming].

Integrate naturally — don't make it the first or last sentence.

---

## Edit 6: Cross-Reference to Paper 10 Methodology

Add a forward reference to Paper 10's methodology section wherever the Classical.choice issue is discussed:

> A systematic treatment of the relationship between Mathlib's classical foundations and the constructive claims across the paper series is given in Paper 10 [Lee 2026, forthcoming], which establishes three certification levels — mechanically certified, structurally verified, and paper-level — and classifies each paper accordingly. Paper 7 is classified as "structurally verified" (pending upgrade to "mechanically certified" upon completion of P7_Minimal).

---

## Edit 7: Ensure Consistency with Paper 2's Current State

Paper 2 has two build targets: P2_Minimal (dependency-free, sorry-free) and P2_Full (Mathlib-based). Any references to Paper 2 in Paper 7 should reflect this architecture. Specifically:

- When citing Paper 2's WLPO ↔ bidual gap result, note that it is "mechanically certified via the dependency-free P2_Minimal artifact"
- When discussing the `ell1_not_reflexive` interface assumption, note that it is "proved in Paper 2's P2_Full target on Lean v4.23.0-rc2; porting to Paper 7's Mathlib v4.28 is blocked by version migration cost, not by mathematical content"

These points may already be in §6. Verify and strengthen if needed.

---

## Edit 8: Check Table 1 Line Counts

The paper reports 754 lines across 8 files. Verify the per-file breakdown sums correctly. The previously reported breakdown (before the WLPOFromWitness addition) was 514 lines across 6 files. After the revision:

- Original 6 files: ~514 lines
- WLPOFromWitness.lean: 196 lines  
- Instance.lean: 51 lines
- Adjustments to Main.lean and Papers.lean: ~-7 lines

Total should be approximately 754. If the table doesn't reflect the current state, update it.

---

## Edits NOT Needed for Other Papers

Based on the full audit, here are brief notes on what other papers need. These are NOT part of the Paper 7 revision task but are listed here for reference:

**Paper 1 (GR/Schwarzschild):** Reframe "Axiom Calibration" / "Height Certificate" language as "the proof is finitistic." Low priority, minor wording changes only.

**Paper 2:** No changes needed. Gold standard of the series.

**Paper 8:** More prominent disclosure of `bmc_of_lpo` axiom. One paragraph addition to §X explaining that the Bridges-Vîță BMC ↔ LPO equivalence is imported as an axiom because reproving it is out of scope.

**Paper 9:** No changes needed. Import audit methodology is sound.

**Paper 10 (Synthesis):** Add the methodology section described in the audit document (three certification levels, Mathlib classical metatheory discussion). This is the highest-leverage edit in the series but is a separate task.

**Paper 11 (Tsirelson/Bell):** Separate revision instructions already provided.

---

## Summary of Paper 7 Edits

| Location | Edit | Scope |
|----------|------|-------|
| §6 (new subsection) | Classical.choice methodology disclosure | ~1 page |
| Reproducibility Box | Add P7_Minimal entry | 3-4 lines |
| §8.2 | Verify MP/WLPO fix is present | Verification only |
| §8 | Strengthen physics discussion if understated | 0.5-1 page |
| Abstract | Add one certification-methodology sentence | ~2 sentences |
| Cross-references | Add Paper 10 methodology forward reference | ~2 sentences |
| Paper 2 references | Ensure P2_Minimal architecture is mentioned | Verify/strengthen |
| Table 1 | Verify line counts match 754 total | Verification only |

**Total revision scope:** ~2-3 pages of new/revised text. Core technical content unchanged.

---

## Tone Guidance

Same as Paper 11: confident but precise. The equivalence is correct. The BISH content of the forward direction (Ishihara kernel) is genuinely constructive — it's a constructive algorithm, and the 196-line self-contained proof in WLPOFromWitness.lean is strong evidence. The reverse direction uses WLPO as hypothesis (so classical content is *intended*). Lemma B uses Hahn-Banach, which is constructively available for separable spaces. The paper should convey all of this clearly without either overclaiming ("`#print axioms` certifies BISH") or underclaiming ("we can't be sure it's constructive").
