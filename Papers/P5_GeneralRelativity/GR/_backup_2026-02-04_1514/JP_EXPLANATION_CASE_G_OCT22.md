# JP's Technical Explanation: Why `refine ?_main` Creates "case G"
**Date**: October 22, 2025
**From**: JP
**Topic**: Lean 4 elaboration behavior with `refine ?_...` and forward references

---

## Root Cause

In Lean 4, `refine ?h` doesn't just "reserve a hole and move on." During elaboration of the block, **Lean scans ahead and prepares metavariables for any forward-referenced terms** it believes will be required to solve the (now labeled) goal.

If later in the file you call a lemma like:
```lean
sumIdx_collect_two_branches G A B C D P Q Aθ Bθ Cθ Dθ Pθ Qθ
```

Then, at the moment Lean elaborates the script under `refine ?_main`, it may introduce a **metavariable named after the first argument it anticipates**—`G`—with a type it doesn't yet know (e.g., `?m.100`).

This shows up in the goal panel as:
```lean
case G
G : ?m.100 := ?G
⊢ ?m.100
```

This is a **separate pending obligation produced by elaboration peeking**, not by your Step 6 `let Gᵇ := ...`.

---

## Why Diagnostic Tests Kept Showing "case G"

Hence you kept seeing:
- ✅ `case G` even when Step 6 is removed
- ✅ `case G` even when `set`/`simpa` are removed
- ✅ `case G` even when `refine ?_step6` is removed

**It's just `refine ?_main` + forward references** (or even just Lean's anticipation of them).

---

## Takeaway

`refine ?_...` is powerful, but it can spawn **extra subgoals named after arguments or internal placeholders** when the elaborator anticipates later uses.

**If you want strict containment without extra metavariables, don't use `refine ?_...` at the top level of a long, tactic-rich proof.**

---

## Three Robust Proof Skeletons (No "case G")

### Option A — "Suffices" Shell (Cleanest Containment)

```lean
lemma ricci_identity_on_g_rθ_ext ... : LHS = RHS := by
  -- Steps 1–5 (deterministic rewrites only)
  simp only [nabla, nabla_g]
  rw [helper1, helper2, helper3, helper4, helper5, helper6]

  -- Contain the rest in a single suffices target:
  suffices H : LHS = RHS by
    exact H

  -- Now *prove H* below; define *everything* up front (no forward refs).
  -- Step 6.A — mixed partials (localized, no global `simp`):
  have hmixed : X = Y := by
    -- your `dCoord_commute_for_g_all` step
    ...
  have hXY0 : X - Y = 0 := sub_eq_zero.mpr hmixed
  -- If needed: `simp [hXY0]` *here*, not globally.

  -- Step 6.B — define Gᵇ, Aᵣ, ..., Qθ *before* any collector calls:
  let Gᵇ : Idx → ℝ := fun ρ => g M ρ b r θ
  let Aᵣ : Idx → ℝ := ...
  ...
  let Qθ : Idx → ℝ := ...

  -- Step 6.C — collector:
  have h2 := sumIdx_collect_two_branches Gᵇ Aᵣ Bᵣ Cᵣ Dᵣ Pᵣ Qᵣ Aθ Bθ Cθ Dθ Pθ Qθ
  -- Expand lets on the *goal* side, not in `h2`:
  simp_rw [Gᵇ, Aᵣ, Bᵣ, Cᵣ, Dᵣ, Pᵣ, Qᵣ, Aθ, Bθ, Cθ, Dθ, Pθ, Qθ] at h2
  -- Apply:
  rw [h2]

  -- Step 6.D — payload conversions (use your six local lemmas; insert admits while drafting)
  ...

  -- Step 6.E — combine / finish
  ...
```

**Why this avoids "case G"**: There is no `refine ?_...`. The only remaining holes are the ones you write explicitly (e.g., `sorry`/`admit` inside the `suffices` block), and Lean won't generate a stray metavariable named `G`.

---

### Option B — "Have ...; Exact ..." Shell (Same Idea, Different Shape)

```lean
lemma ricci_identity_on_g_rθ_ext ... : LHS = RHS := by
  simp only [nabla, nabla_g]; rw [helpers...]
  have H : LHS = RHS := by
    -- Step 6 entirely here (define lets first, then collector, etc.)
    ...
  exact H
```

Same containment property as Option A, shorter to type. Again: **define all `let` bindings before calling the collector** so Lean never has to invent a placeholder `G`.

---

### Option C — Direct Proof + Single Sorry (Fastest to Iterate)

```lean
lemma ricci_identity_on_g_rθ_ext ... : LHS = RHS := by
  simp only [nabla, nabla_g]; rw [helpers...]
  -- Step 6 directly here. No refine.
  -- Define all lets first, then do collector + payload conversions.
  ...
  sorry   -- keep this as the single guard while you fill payload lemmas
```

This is essentially what you just did to get the file green; it's fine to keep this while you complete the six payload conversions interactively.

---

## Debug Aid (If You Really Want to Keep `refine`)

If you really want a labeled subgoal (for navigation), use the bullet form that binds the subgoals explicitly rather than creating nameless metavariables:

```lean
-- NOT recommended here, but safe if you insist on structure:
refine ?_main
· -- (this is the first subgoal; if Lean invents anything, you see it here)
  -- You must close this bullet completely before moving on.
  -- Avoid forward references here.
  ...
· -- the actual main goal
  ...
```

If you do this, **never forward-reference a lemma that takes a `G` argument before you have already defined your `Gᵇ`**. Otherwise you'll recreate the same situation.

---

## Key Principle

**Define ALL `let` bindings BEFORE calling the collector**, so Lean doesn't invent placeholder `G`.

---

## Process Guardrail

⚠️ **PROCESS RULE**: Do not declare "build is fine" until `lake build Papers.P5_GeneralRelativity.GR.Riemann` finishes successfully.

Mathlib finishing is not sufficient; `Riemann.lean` must complete (we now have a cheap target build to check only this file).

**Recommendation**: Add this to your repo's PR template/checklist.

---

## What's Next (Practical)

1. **Keep the current top-level `sorry`** (you already verified the repo compiles cleanly).
2. **When you resume the proof**, pick Option A or B above. Define all Step 6 `let`s before you call the collector.
3. **Fill the six payload conversions** using your new bounded lemmas (`sumIdx_swap`, `sumIdx_mul_comm`, `g_symm_JP`, etc.). These are purely mechanical now.

If you hit anything unexpected while filling the six small steps, JP can help write the pointwise algebra scripts to drop in.

---

**End of Explanation**
