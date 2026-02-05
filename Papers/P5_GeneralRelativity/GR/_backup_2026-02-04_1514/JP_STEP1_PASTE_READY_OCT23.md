# JP's Paste-Ready Code for algebraic_identity Steps 1-6
**Date**: October 23, 2025 (Final Drop-In Patterns)
**Status**: Ready to paste by hand into Riemann.lean

---

## Location: Inside `algebraic_identity` lemma

**File**: `Riemann.lean` line ~6128
**After**: `classical` line
**Before**: Current `sorry` at line 6288

---

## STEP 1A: Expand μ-branch of P_terms

**Paste this block immediately after `classical`:**

```lean
  -- === Step 1A: Expand the μ-branch of P_terms ===
  -- Bring `nabla_g` definition into the goal in a stable shape.
  have hPμ :
    dCoord μ (fun r θ => nabla_g M r θ ν a b) r θ
    =
    dCoord μ (fun r θ =>
      dCoord ν (fun r θ => g M a b r θ) r θ
      - sumIdx (fun ρ => Γtot M r θ ρ ν a * g M ρ b r θ)
      - sumIdx (fun ρ => Γtot M r θ ρ ν b * g M a ρ r θ)) r θ := by
    simp [nabla_g, sub_eq_add_neg]

  -- Split the outer dCoord over the three terms (difference rule twice).
  have hPμ_expand :
    dCoord μ (fun r θ =>
      dCoord ν (fun r θ => g M a b r θ) r θ
      - sumIdx (fun ρ => Γtot M r θ ρ ν a * g M ρ b r θ)
      - sumIdx (fun ρ => Γtot M r θ ρ ν b * g M a ρ r θ)) r θ
    =
      dCoord μ (fun r θ => dCoord ν (fun r θ => g M a b r θ) r θ) r θ
      - dCoord μ (fun r θ => sumIdx (fun ρ => Γtot M r θ ρ ν a * g M ρ b r θ)) r θ
      - dCoord μ (fun r θ => sumIdx (fun ρ => Γtot M r θ ρ ν b * g M a ρ r θ)) r θ := by
    -- First subtraction
    have h₁ := dCoord_sub_of_diff μ
      (fun r θ => dCoord ν (fun r θ => g M a b r θ) r θ)
      (fun r θ => sumIdx (fun ρ => Γtot M r θ ρ ν a * g M ρ b r θ))
      r θ (by discharge_diff) (by discharge_diff)
      (by discharge_diff) (by discharge_diff)
    -- Second subtraction (apply to the result of the first minus the third term)
    have h₂ := dCoord_sub_of_diff μ
      (fun r θ =>
        dCoord ν (fun r θ => g M a b r θ) r θ
        - sumIdx (fun ρ => Γtot M r θ ρ ν a * g M ρ b r θ))
      (fun r θ => sumIdx (fun ρ => Γtot M r θ ρ ν b * g M a ρ r θ))
      r θ (by discharge_diff) (by discharge_diff)
      (by discharge_diff) (by discharge_diff)
    -- normalize parentheses
    simpa [sub_eq_add_neg] using
      (h₂.trans (by simpa [sub_eq_add_neg] using h₁).symm)

  -- Push dCoord μ through the first Σ (ρ, ν, a · b branch), with product rule inside Σ.
  have hPμ_sum1 :
    dCoord μ (fun r θ => sumIdx (fun ρ => Γtot M r θ ρ ν a * g M ρ b r θ)) r θ
    =
    sumIdx (fun ρ =>
      dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ * g M ρ b r θ
    + Γtot M r θ ρ ν a * dCoord μ (fun r θ => g M ρ b r θ) r θ) := by
    refine dCoord_sumIdx μ (fun ρ r θ => Γtot M r θ ρ ν a * g M ρ b r θ) r θ ?_ ?_
    · intro ρ; exact (DifferentiableAt_r_mul_of_cond _ _ r θ μ (by discharge_diff) (by discharge_diff))
    · intro ρ; exact (DifferentiableAt_θ_mul_of_cond _ _ r θ μ (by discharge_diff) (by discharge_diff))
    -- product rule inside Σ
    simp [dCoord_mul_of_diff, (by discharge_diff), (by discharge_diff)]

  -- Same for the second Σ (ρ, ν, b · a branch).
  have hPμ_sum2 :
    dCoord μ (fun r θ => sumIdx (fun ρ => Γtot M r θ ρ ν b * g M a ρ r θ)) r θ
    =
    sumIdx (fun ρ =>
      dCoord μ (fun r θ => Γtot M r θ ρ ν b) r θ * g M a ρ r θ
    + Γtot M r θ ρ ν b * dCoord μ (fun r θ => g M a ρ r θ) r θ) := by
    refine dCoord_sumIdx μ (fun ρ r θ => Γtot M r θ ρ ν b * g M a ρ r θ) r θ ?_ ?_
    · intro ρ; exact (DifferentiableAt_r_mul_of_cond _ _ r θ μ (by discharge_diff) (by discharge_diff))
    · intro ρ; exact (DifferentiableAt_θ_mul_of_cond _ _ r θ μ (by discharge_diff) (by discharge_diff))
    simp [dCoord_mul_of_diff, (by discharge_diff), (by discharge_diff)]

  -- Bundle the μ-branch expansion into a single convenient rewrite.
  have hPμ_full :
    dCoord μ (fun r θ => nabla_g M r θ ν a b) r θ
    =
      dCoord μ (fun r θ => dCoord ν (fun r θ => g M a b r θ) r θ) r θ
      - sumIdx (fun ρ =>
          dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ * g M ρ b r θ
        + Γtot M r θ ρ ν a * dCoord μ (fun r θ => g M ρ b r θ) r θ)
      - sumIdx (fun ρ =>
          dCoord μ (fun r θ => Γtot M r θ ρ ν b) r θ * g M a ρ r θ
        + Γtot M r θ ρ ν b * dCoord μ (fun r θ => g M a ρ r θ) r θ) := by
    simpa [hPμ_sum1, hPμ_sum2] using hPμ.trans hPμ_expand
```

---

## STEP 1B: Expand ν-branch (mirror with μ ↔ ν)

**Paste this block right after Step 1A:**

```lean
  -- === Step 1B: Expand the ν-branch (mirror with μ ↔ ν) ===
  have hPν :
    dCoord ν (fun r θ => nabla_g M r θ μ a b) r θ
    =
    dCoord ν (fun r θ =>
      dCoord μ (fun r θ => g M a b r θ) r θ
      - sumIdx (fun ρ => Γtot M r θ ρ μ a * g M ρ b r θ)
      - sumIdx (fun ρ => Γtot M r θ ρ μ b * g M a ρ r θ)) r θ := by
    simp [nabla_g, sub_eq_add_neg]

  have hPν_expand :
    dCoord ν (fun r θ =>
      dCoord μ (fun r θ => g M a b r θ) r θ
      - sumIdx (fun ρ => Γtot M r θ ρ μ a * g M ρ b r θ)
      - sumIdx (fun ρ => Γtot M r θ ρ μ b * g M a ρ r θ)) r θ
    =
      dCoord ν (fun r θ => dCoord μ (fun r θ => g M a b r θ) r θ) r θ
      - dCoord ν (fun r θ => sumIdx (fun ρ => Γtot M r θ ρ μ a * g M ρ b r θ)) r θ
      - dCoord ν (fun r θ => sumIdx (fun ρ => Γtot M r θ ρ μ b * g M a ρ r θ)) r θ := by
    have h₁ := dCoord_sub_of_diff ν
      (fun r θ => dCoord μ (fun r θ => g M a b r θ) r θ)
      (fun r θ => sumIdx (fun ρ => Γtot M r θ ρ μ a * g M ρ b r θ))
      r θ (by discharge_diff) (by discharge_diff)
      (by discharge_diff) (by discharge_diff)
    have h₂ := dCoord_sub_of_diff ν
      (fun r θ =>
        dCoord μ (fun r θ => g M a b r θ) r θ
        - sumIdx (fun ρ => Γtot M r θ ρ μ a * g M ρ b r θ))
      (fun r θ => sumIdx (fun ρ => Γtot M r θ ρ μ b * g M a ρ r θ))
      r θ (by discharge_diff) (by discharge_diff)
      (by discharge_diff) (by discharge_diff)
    simpa [sub_eq_add_neg] using
      (h₂.trans (by simpa [sub_eq_add_neg] using h₁).symm)

  have hPν_sum1 :
    dCoord ν (fun r θ => sumIdx (fun ρ => Γtot M r θ ρ μ a * g M ρ b r θ)) r θ
    =
    sumIdx (fun ρ =>
      dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ * g M ρ b r θ
    + Γtot M r θ ρ μ a * dCoord ν (fun r θ => g M ρ b r θ) r θ) := by
    refine dCoord_sumIdx ν (fun ρ r θ => Γtot M r θ ρ μ a * g M ρ b r θ) r θ ?_ ?_
    · intro ρ; exact (DifferentiableAt_r_mul_of_cond _ _ r θ ν (by discharge_diff) (by discharge_diff))
    · intro ρ; exact (DifferentiableAt_θ_mul_of_cond _ _ r θ ν (by discharge_diff) (by discharge_diff))
    simp [dCoord_mul_of_diff, (by discharge_diff), (by discharge_diff)]

  have hPν_sum2 :
    dCoord ν (fun r θ => sumIdx (fun ρ => Γtot M r θ ρ μ b * g M a ρ r θ)) r θ
    =
    sumIdx (fun ρ =>
      dCoord ν (fun r θ => Γtot M r θ ρ μ b) r θ * g M a ρ r θ
    + Γtot M r θ ρ μ b * dCoord ν (fun r θ => g M a ρ r θ) r θ) := by
    refine dCoord_sumIdx ν (fun ρ r θ => Γtot M r θ ρ μ b * g M a ρ r θ) r θ ?_ ?_
    · intro ρ; exact (DifferentiableAt_r_mul_of_cond _ _ r θ ν (by discharge_diff) (by discharge_diff))
    · intro ρ; exact (DifferentiableAt_θ_mul_of_cond _ _ r θ ν (by discharge_diff) (by discharge_diff))
    simp [dCoord_mul_of_diff, (by discharge_diff), (by discharge_diff)]

  have hPν_full :
    dCoord ν (fun r θ => nabla_g M r θ μ a b) r θ
    =
      dCoord ν (fun r θ => dCoord μ (fun r θ => g M a b r θ) r θ) r θ
      - sumIdx (fun ρ =>
          dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ * g M ρ b r θ
        + Γtot M r θ ρ μ a * dCoord ν (fun r θ => g M ρ b r θ) r θ)
      - sumIdx (fun ρ =>
          dCoord ν (fun r θ => Γtot M r θ ρ μ b) r θ * g M a ρ r θ
        + Γtot M r θ ρ μ b * dCoord ν (fun r θ => g M a ρ r θ) r θ) := by
    simpa [hPν_sum1, hPν_sum2] using hPν.trans hPν_expand
```

**Status after Steps 1A-1B**: You have separated into:
- Mixed partials: `dCoord μ dCoord ν g` vs `dCoord ν dCoord μ g`
- Main pieces: (∂Γ)·g and Γ·Γ·g
- Payload: Γ·(∂g) on each branch

---

## STEPS 2-4: Collector Options

**You already have the a-branch bindings defined** (lines 6188-6202):
```lean
let Gab  : Idx → ℝ := fun ρ => g M ρ b r θ
let Aμ   : Idx → ℝ := fun ρ => dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ
let Bν   : Idx → ℝ := fun ρ => dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ
let Cμ   : Idx → ℝ := fun ρ => sumIdx (fun lam => Γtot M r θ ρ μ lam * Γtot M r θ lam ν a)
let Dν   : Idx → ℝ := fun ρ => sumIdx (fun lam => Γtot M r θ ρ ν lam * Γtot M r θ lam μ a)
let Pμ   : Idx → ℝ := fun ρ => Γtot M r θ ρ ν a * dCoord μ (fun r θ => g M ρ b r θ) r θ
let Qν   : Idx → ℝ := fun ρ => Γtot M r θ ρ μ a * dCoord ν (fun r θ => g M ρ b r θ) r θ
```

### OPTION A: Single-Branch Collector (a-branch then b-branch separately)

**Step 2 (a-branch):**
```lean
  -- Step 2 (a-branch): package main vs payload
  have hCollect_a :
    ( (sumIdx (fun ρ => Aμ ρ * Gab ρ + Pμ ρ))
    -   sumIdx (fun ρ => Bν ρ * Gab ρ + Qν ρ)
    +   sumIdx (fun ρ => Gab ρ * Cμ ρ)
    -   sumIdx (fun ρ => Gab ρ * Dν ρ) )
    =
    sumIdx (fun ρ => Gab ρ * ((Aμ ρ - Bν ρ) + (Cμ ρ - Dν ρ)))
    + sumIdx (fun ρ => Pμ ρ - Qν ρ) := by
    exact sumIdx_collect_comm_block_with_extras Gab Aμ Bν Cμ Dν Pμ Qν
```

**Step 3 (a-branch):**
```lean
  -- Step 3 (a-branch): payload cancels with the Γ·∂g part from C_terms_a
  have hPayload_a :
    sumIdx (fun ρ => Pμ ρ - Qν ρ)
    + (  sumIdx (fun ρ => - Γtot M r θ ρ μ a * dCoord ν (fun r θ => g M ρ b r θ) r θ)
       + sumIdx (fun ρ =>   Γtot M r θ ρ ν a * dCoord μ (fun r θ => g M ρ b r θ) r θ) )
    = 0 := by
    ring_nf
    simp [Pμ, Qν, sumIdx_add_distrib, sumIdx_map_sub]
```

**Step 4: Repeat for b-branch**
- Define mirror bindings: `Gba`, `Aμᵇ`, `Bνᵇ`, `Cμᵇ`, `Dνᵇ`, `Pμᵇ`, `Qνᵇ` (with `a ↔ b`)
- Apply `hCollect_b` (same pattern as hCollect_a)
- Apply `hPayload_b` (same pattern as hPayload_a)

---

### OPTION B: Two-Branch Collector (μ and ν simultaneously)

**Define ν-branch bindings:**
```lean
  let Aν  : Idx → ℝ := fun ρ => dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ
  let Bμ  : Idx → ℝ := fun ρ => dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ
  let Cν  : Idx → ℝ := fun ρ => sumIdx (fun lam => Γtot M r θ ρ ν lam * Γtot M r θ lam μ a)
  let Dμ  : Idx → ℝ := fun ρ => sumIdx (fun lam => Γtot M r θ ρ μ lam * Γtot M r θ lam ν a)
  let Pν  : Idx → ℝ := fun ρ => Γtot M r θ ρ μ a * dCoord ν (fun r θ => g M ρ b r θ) r θ
  let Qμ  : Idx → ℝ := fun ρ => Γtot M r θ ρ ν a * dCoord μ (fun r θ => g M ρ b r θ) r θ
```

**Step 2+ (both branches at once):**
```lean
  -- Step 2+ (both branches at once): main vs payload for μ and ν
  have hTwo :
    ( (sumIdx (fun ρ => Aμ ρ * Gab ρ + Pμ ρ))
    -   sumIdx (fun ρ => Bν ρ * Gab ρ + Qν ρ)
    +   sumIdx (fun ρ => Gab ρ * Cμ ρ)
    -   sumIdx (fun ρ => Gab ρ * Dν ρ) )
    -
    ( (sumIdx (fun ρ => Aν ρ * Gab ρ + Pν ρ))
    -   sumIdx (fun ρ => Bμ ρ * Gab ρ + Qμ ρ)
    +   sumIdx (fun ρ => Gab ρ * Cν ρ)
    -   sumIdx (fun ρ => Gab ρ * Dμ ρ) )
    =
    ( sumIdx (fun ρ => Gab ρ * ((Aμ ρ - Bν ρ) + (Cμ ρ - Dν ρ)))
    - sumIdx (fun ρ => Gab ρ * ((Aν ρ - Bμ ρ) + (Cν ρ - Dμ ρ))) )
    +
    ( sumIdx (fun ρ => Pμ ρ - Qν ρ)
    - sumIdx (fun ρ => Pν ρ - Qμ ρ) ) := by
    simpa using
      sumIdx_collect_two_branches Gab Aμ Bν Cμ Dν Pμ Qν Aν Bμ Cν Dμ Pν Qμ
```

Then cancel both payload sums with corresponding `C_terms_a`/`C_terms_b` Γ·∂g pieces (two `ring_nf; simp [...]` steps).

---

## STEP 5: Clairaut Cancellation (Mixed Partials)

**Once payloads are gone, cancel mixed partials by smoothness:**

```lean
  have hmixed :
    dCoord μ (fun r θ => dCoord ν (fun r θ => g M a b r θ) r θ) r θ
    =
    dCoord ν (fun r θ => dCoord μ (fun r θ => g M a b r θ) r θ) r θ := by
    simpa using dCoord_commute_for_g_all M r θ a b μ ν

  -- Use: by simp [hmixed, sub_eq_add_neg] wherever (∂μ∂νg - ∂ν∂μg) difference appears
```

---

## STEP 6: Recognize Riemann (Definitionally)

**With only (∂Γ)·g + Γ·Γ·g remaining on each branch:**

**a-branch Riemann recognition:**
```lean
  -- a-branch Riemann recognition
  have hRa :
    sumIdx (fun ρ =>
      g M ρ b r θ *
        ( dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ
        - dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ
        + sumIdx (fun lam =>
            Γtot M r θ ρ μ lam * Γtot M r θ lam ν a
          - Γtot M r θ ρ ν lam * Γtot M r θ lam μ a) ))
    =
    - Riemann M r θ b a μ ν := by
    unfold Riemann
    simp [RiemannUp, sumIdx_add_distrib, sumIdx_map_sub, g_symm]
```

**b-branch (mirror with a ↔ b):**
```lean
  -- b-branch (mirror with a ↔ b)
  have hRb :
    sumIdx (fun ρ =>
      g M a ρ r θ *
        ( dCoord μ (fun r θ => Γtot M r θ ρ ν b) r θ
        - dCoord ν (fun r θ => Γtot M r θ ρ μ b) r θ
        + sumIdx (fun lam =>
            Γtot M r θ ρ μ lam * Γtot M r θ lam ν b
          - Γtot M r θ ρ ν lam * Γtot M r θ lam μ b) ))
    =
    - Riemann M r θ a b μ ν := by
    unfold Riemann
    simp [RiemannUp, sumIdx_add_distrib, sumIdx_map_sub, g_symm]

  -- Combine hRa and hRb to close the goal.
  -- (Your calc chain can `rw [hRa, hRb]` at the appropriate point.)
```

---

## After algebraic_identity Completes

### ricci_identity_on_g_general

**Already structured** (lines 6290-6301) - should close immediately once `algebraic_identity` is proven.

### ricci_identity_on_g_rθ_ext

**Replace the sorry with:**

```lean
have : nabla (fun M r θ a b => nabla_g M r θ Idx.θ a b) M r θ Idx.r a b
     = nabla2_g M r θ Idx.r Idx.θ a b := rfl
have : nabla (fun M r θ a b => nabla_g M r θ Idx.r a b) M r θ Idx.θ a b
     = nabla2_g M r θ Idx.θ Idx.r a b := rfl
simpa using ricci_identity_on_g_general M r θ h_ext Idx.r Idx.θ a b
```

---

## Two Key Footguns to Avoid

### 1. Shape Sensitivity

When `sumIdx_add_distrib` or `sumIdx_map_sub` "does not find the pattern":
- **First reshape** using your flatten₄*/group_* helpers
- **Don't try to force** `rw` against differently parenthesized addition/subtraction tree

### 2. Simp Scope

**Prefer**:
```lean
simp only [sub_eq_add_neg, RiemannUp, sumIdx_add_distrib, sumIdx_map_sub, g_symm]
```

**Avoid**: Global `[simp]` lists that might rewrite Γ or g into unintended normal forms mid-proof

---

## Implementation Checklist

While implementing:

- ✅ Keep `classical` at top of proof
- ✅ Use `by discharge_diff` for every differentiability side-condition
- ✅ When a simp fails to match, reshape with fold/flatten lemmas, then simp
- ✅ Lean on `sumIdx_collect_comm_block_with_extras` (or two-branch variant) to separate main vs payload
- ✅ Cancel payloads with two-line `ring_nf; simp [...]` pattern
- ✅ Apply `dCoord_commute_for_g_all` for mixed partials
- ✅ Recognize each branch as `-Riemann ...` by definition

---

## File Organization

**Location**: `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean`
- **Current line 6128**: Start of `algebraic_identity` lemma
- **Current line 6288**: `sorry` placeholder to replace
- **After pasting**: ~200-300 lines of proof (Steps 1-6)

---

**Status**: All patterns ready to paste by hand
**Expected time**: 2-4 hours to paste and wire all steps
**Expected outcome**: `algebraic_identity` fully proven, 0 errors, 11 sorries remaining (down from 14)

---

**Date**: October 23, 2025
**Source**: JP's final drop-in guidance
**Next**: Paste Steps 1A-1B first, verify build, then Steps 2-6
