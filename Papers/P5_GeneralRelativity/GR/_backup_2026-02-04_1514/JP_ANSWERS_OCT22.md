# JP's Answers to 5 Questions - October 22, 2025

## Context
This documents JP's responses to the 5 tactical questions posed in `TACTICAL_REPORT_FOR_JP_OCT22.md`.

---

## Question 1: Should I integrate your 6 micro-lemma skeletons now?

**JP's Answer**:

**Keep the file unchanged for now** (clean state preserved).

When you're ready to restore `ricci_identity_on_g_rθ_ext`, paste the skeletons, wire them into Step 6, and **keep their bodies sorry while you fill them one by one**. That keeps the edit set tightly scoped to the restoration.

**Recommendation**: Wait until ready to restore proof, then paste all at once.

---

## Question 2: C¹ lemmas for g and Γtot to reference?

**JP's Answer**:

**Yes—already present in this file** and sufficient for Phase 2B:

Existing lemmas to use:
- `differentiableAt_g_all_r` / `differentiableAt_g_all_θ`
- `differentiableAt_Γtot_all_r` / `differentiableAt_Γtot_all_θ`

Use them exactly as in the drop-in stubs (saved in `JP_SKELETONS_OCT22_PASTE_READY.lean`) to discharge the ∂/Σ interchange obligations.

**Pattern**:
```lean
have hF_r : ∀ k, DifferentiableAt_r (...) ∨ Idx.r ≠ Idx.r := by
  intro k
  left
  exact (DifferentiableAt.mul
    (differentiableAt_Γtot_all_r M r θ h_ext k Idx.θ a)
    (differentiableAt_g_all_r M r θ h_ext k b))
```

---

## Question 3: Replace dCoord_g_via_compat_ext_temp's sorry by pointing to the later proof?

**JP's Answer**:

**Not safely.**

Lean can't reference a later lemma before it's defined. You'd need to move the proven lemma earlier (or keep the temporary sorry forward decl).

**Easiest approach**: Keep the temp lemma until you reorder sections.

**Future work**: Can reorder file sections to prove `dCoord_g_via_compat_ext` earlier, then remove temp forward declaration.

---

## Question 4: Delete deprecated/false lemmas now?

**JP's Answer**:

**Safer sequencing**:

1. **First grep for usages.** If there are none, JP recommends removing the false lemma (`regroup_right_sum_to_RiemannUp_NEW`) to avoid accidental dependence.

2. **Keep the big deprecated block commented** until all call-sites are migrated to the CORRECT pathway; then delete the whole block in one PR with a short note pointing to the counterexample.

**Action plan**:
- **Immediately**: Check if `regroup_right_sum_to_RiemannUp_NEW` (line 8523) has any uses
  - If no uses: Delete it with note about flat polar coordinates counterexample
- **Later**: Delete entire block comment (lines 1910-2089) after verifying no dependencies

---

## Question 5: ASCII names for the 12 lets?

**JP's Answer**:

**Yes—use ASCII names.**

**Recommended names**:
```lean
Gb, Ar, Br, Cr, Dr, Pr, Qr, Ath, Bth, Cth, Dth, Pth, Qth
```

**Reason**: This avoids the parser hiccup you saw with `ᵇ` (superscript b).

**Pattern**:
```lean
let Gb  : Idx → ℝ := fun ρ => g M ρ b r θ
let Ar  : Idx → ℝ := fun ρ => - Γtot M r θ ρ a Idx.r * g M ρ b r θ
let Br  : Idx → ℝ := fun ρ => - Γtot M r θ ρ b Idx.r * g M a ρ r θ
-- ... (9 more)
```

---

## Additional Offer from JP

JP offered to draft two additional lemmas:
- **Metric symmetry** (explicit, non-simp, simp_rw-friendly)
- **Lower-index torsion-free** (explicit, non-simp, simp_rw-friendly)

These would be useful for lines ~8454/~8467 (symmetry applications in Phase 2B).

**Status**: Offer pending acceptance.

---

## Guardrail Reminder (JP's emphasis)

Keep using the single-file target to validate any change:

```bash
cd /Users/quantmann/FoundationRelativity
lake build Papers.P5_GeneralRelativity.GR.Riemann
```

**No "build is fine" declarations until that exits 0.** 👍

---

## Files Created

1. **`JP_SKELETONS_OCT22_PASTE_READY.lean`** - All skeletons ready to copy/paste
2. **`JP_ANSWERS_OCT22.md`** - This file (answers to 5 questions)

---

**Date**: October 22, 2025
**Status**: Ready to proceed with restoration when user decides
**Next decision**: Accept JP's offer to draft metric symmetry + torsion-free lemmas?
