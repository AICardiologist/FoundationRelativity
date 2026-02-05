# Paul's Guidance: Durable Pattern & Splitter Closure

**Date**: October 29, 2025
**From**: Paul (via user message)
**To**: JP
**Context**: Post-recursion fix - building durable patterns and closing splitter goals

---

## Paul's Complete Guidance

### 1. Lock in a Non-Simp "Packing" API

**Action**: Keep all "shape-changing" algebraic lemmas off simp; use `rw`/`exact` instead.

**Add the right-constant version**:

```lean
/-- Symmetric right-constant version. -/
lemma sumIdx_factor_const_from_sub_right
    (c : ℝ) (A B : Idx → ℝ) :
  sumIdx (fun k => A k * c - B k * c) = (sumIdx A - sumIdx B) * c := by
  classical
  calc
    sumIdx (fun k => A k * c - B k * c)
        = sumIdx (fun k => A k * c) - sumIdx (fun k => B k * c) := by
          simpa using sumIdx_map_sub (fun k => A k * c) (fun k => B k * c)
    _ = sumIdx A * c - sumIdx B * c := by
          simp [sumIdx_mul]   -- add this lemma if you don't have it
    _ = (sumIdx A - sumIdx B) * c := by ring
```

**Notes**:
- If you don't have `sumIdx_mul : sumIdx (fun k => A k * c) = sumIdx A * c`, add it alongside `mul_sumIdx`
- Do NOT mark either with `@[simp]`
- Use them with `rw` or `simp (only := [mul_sumIdx])` when you want one specific direction

---

### 2. Tame the Simp Set Locally Around μ/ν Splitters

**Add local attribute hygiene**:

```lean
section Splitters

-- Keep these out of the global simp set to avoid oscillation.
local attribute [-simp] mul_sumIdx sumIdx_mul
-- If either carried @[simp] from elsewhere, the above neutralizes it locally.

-- When you *do* want a one-off simplification, make it explicit:
--   simp (only := [mul_sumIdx])    -- push left-constant out
--   simp (only := [sumIdx_mul])    -- push right-constant out

-- Your μ- and ν-splitter proofs…
end Splitters
```

This preserves your current `exact`-based closure while preventing someone from reintroducing the loop later.

---

### 3. Close the Two Splitter "Unsolved Goals": Normalize, Then Use Structural Identity

**Strategy**:
1. Normalize both sums to the same index shape with reindexing lemmas
2. Use a pointwise identity to show `X ρ = Y ρ` (or their difference is zero)
3. Finish with `sumIdx_eq_zero_of_pointwise` style lemma or by `congr + simp` at index level

**Congruence lemma** (if you don't have it):

```lean
/-- Congruence for `sumIdx` over equal integrands. -/
lemma sumIdx_congr
    (A B : Idx → ℝ)
    (h : ∀ ρ, A ρ = B ρ) :
  sumIdx A = sumIdx B := by
  classical
  -- whatever `sumIdx` is, this is your library's `sum_congr` analogue
  -- implement once and reuse
  admit
```

**Then in the splitter**:

```lean
-- after `rw [sumIdx_factor_const_from_sub_left …]`:
suffices H : (∀ ρ, Γtot M r θ ρ μ a * Γtot M r θ b ν ρ
                  = Γtot M r θ ρ ν a * Γtot M r θ b μ ρ) by
  have : sumIdx (fun ρ => Γtot … μ a * Γtot … ν ρ)
        = sumIdx (fun ρ => Γtot … ν a * Γtot … μ ρ) := by
          exact sumIdx_congr _ _ H
  simpa using congrArg (fun t => g M b b r θ * (t - _)) this
-- now prove H pointwise using whatever Γtot symmetry/commutation you have.
```

The exact identity for H depends on the algebraic properties you have for `Γtot` (commutativity, symmetry in indices, etc.).

---

### 4. The "+2 Errors": Most Likely Bookkeeping, Not Semantic Regressions

**How to verify**:
- Rebuild the pre-fix baseline and capture errors as machine-readable
- Use `--server` plus an editor plugin or `lean --json` output
- Diff diagnostics by **goal pretty-print**, not by line number
- Line numbers are the noisiest signal; goal texts are the stable ones

**If you want to debug inside the file**:

```lean
set_option pp.all true
set_option pp.beta true
-- Optionally:
-- set_option trace.simp.rewrite true
-- set_option trace.simp.prove   true
```

Run only the splitter sections to see exactly where elaboration took a different path.

---

### 5. Make the Packing Rewrite One-Liners

**Drop `have h_pack` noise**:

```lean
-- Instead of:
have h_pack := sumIdx_factor_const_from_sub_left (g M b b r θ) …
rw [h_pack]

-- Just write:
exact sumIdx_factor_const_from_sub_left
        (g M b b r θ) (fun ρ => …) (fun ρ => …)
```

This keeps the proof term small and avoids a named local binding whose only purpose is to be rewritten immediately.

---

### 6. If You Intend to Generalize Beyond ℝ, Widen the Lemmas Now

**Your packing lemmas are linearity statements**:

```lean
variable {α : Type*} [Semiring α]
lemma sumIdx_factor_const_from_sub_left
    (c : α) (A B : Idx → α) : … := …
```

For general Semiring, finish the last step with:
```lean
by simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_add, add_mul]
```

Or keep `ring` if `α` has `Ring` and `DecidableEq`.

---

### 7. Minimal Checklist to Drive the Error Count Down

1. Introduce `sumIdx_factor_const_from_sub_right` and, if missing, `sumIdx_mul`. Do NOT mark with `@[simp]`.
2. Neutralize any global `@[simp]` on `mul_sumIdx`/`sumIdx_mul` locally around splitters with `local attribute [-simp] …`.
3. Rewrite both splitter proofs to close with a pointwise equality and `sumIdx_congr`, as sketched above.
4. Diff diagnostics by goal text, not line numbers, to confirm the "+2" are not genuine new blockers.
5. Remove incidental `h_pack` names in favor of direct `exact …` when the lemma matches syntactically.

---

## Goal States for Splitter Closure

Paul requested these goal states to provide the exact pointwise H and the precise rw/calc chain.

### Line 7248 (μ-splitter)

**Context**:
```
M r θ : ℝ
μ ν a b : Idx
```

**Available hypotheses**:
- `first_block` : nested sum equality
- `first_block_packed` : packed form with g M b b r θ factored
- `swap₁`, `swap₂` : commutativity of products in sums
- `first_block_aligned` : aligned form
- `second_block` : second block equality
- `second_block_packed` : packed second block
- `bb_core_reindexed` : reindexing identity for bb_core

**Goal**:
```lean
⊢ (g M b b r θ *
      ((sumIdx fun e => Γtot M r θ b ν e * Γtot M r θ e μ a)
       - sumIdx fun e => Γtot M r θ b μ e * Γtot M r θ e ν a) +
    sumIdx fun ρ => g M ρ ρ r θ *
      (Γtot M r θ ρ μ a * Γtot M r θ ρ ν b
       - Γtot M r θ ρ ν a * Γtot M r θ ρ μ b))
  =
  g M b b r θ *
      ((sumIdx fun e => Γtot M r θ b μ e * Γtot M r θ e ν a)
       - sumIdx fun e => Γtot M r θ b ν e * Γtot M r θ e μ a) +
    sumIdx fun ρ => g M ρ ρ r θ *
      (Γtot M r θ ρ μ a * Γtot M r θ ρ ν b
       - Γtot M r θ ρ ν a * Γtot M r θ ρ μ b)
```

**Observation**: The LHS and RHS differ only in the `g M b b r θ` term - the order of the difference is swapped (A - B vs B - A). The second `sumIdx` term is identical on both sides. This appears to require showing the difference equals its negative, which would only hold if the terms are equal.

---

### Line 7550 (ν-splitter)

**Context**:
```
M r θ : ℝ
μ ν a b : Idx
```

**Available hypotheses**:
- `first_block` : nested sum equality
- `first_block_packed` : packed form with g M a a r θ factored
- `swap₁`, `swap₂` : commutativity of products in sums
- `first_block_aligned` : aligned form
- `second_block` : second block equality
- `aa_core_reindexed` : reindexing identity for aa_core

**Goal**:
```lean
⊢ (g M a a r θ *
      ((sumIdx fun e => Γtot M r θ a ν e * Γtot M r θ e μ b)
       - sumIdx fun e => Γtot M r θ a μ e * Γtot M r θ e ν b) +
    sumIdx fun ρ => g M ρ ρ r θ *
      (Γtot M r θ ρ μ b * Γtot M r θ ρ ν a
       - Γtot M r θ ρ ν b * Γtot M r θ ρ μ a))
  =
  g M a a r θ *
      ((sumIdx fun e => Γtot M r θ a μ e * Γtot M r θ e ν b)
       - sumIdx fun e => Γtot M r θ a ν e * Γtot M r θ e μ b) +
    sumIdx fun ρ => g M ρ ρ r θ *
      (Γtot M r θ ρ μ b * Γtot M r θ ρ ν a
       - Γtot M r θ ρ ν b * Γtot M r θ ρ μ a)
```

**Observation**: Mirror structure to line 7248 with a/b swapped. Same pattern: g M a a r θ multiplying swapped differences.

---

## Analysis

**Critical Observation**: Both goals have the structure:
```
g * (A - B) + C = g * (B - A) + C
```

Where:
- `A` and `B` are different `sumIdx` expressions
- `C` is identical on both sides
- This reduces to proving: `g * (A - B) = g * (B - A)`
- Which is: `g * (A - B) = -g * (A - B)`
- This only holds if `A = B` or `g = 0`

**Question for Paul**: Is there a symmetry property of `Γtot` that makes these sums equal? Or is there a sign error in how the goal was set up? The goal structure suggests we need to prove that two different sumIdx expressions are actually equal, allowing the differences to cancel to zero.

---

## Implementation Notes for JP

Once Paul provides the exact closure strategy:

1. **Add the congruence lemma** if not present
2. **Identify the Γtot symmetry** that proves the pointwise equality
3. **Apply the pattern** Paul provides for both splitters
4. **Verify** that the "+2 errors" resolve as cascading effects

The key will be understanding what algebraic property of `Γtot` (commutativity, antisymmetry, etc.) makes the two sum expressions equal.

---

**Prepared by**: Claude Code
**Session date**: October 29, 2025
**Status**: Awaiting Paul's closure strategy based on goal states

**Note to JP**: Paul is providing guidance for building durable patterns and has requested these goal states to provide you with the exact proof strategy. His expertise in Lean tactics and algebraic manipulation will provide the most direct path to closure.
