# Detailed Diagnostic for JP: Pattern B Shape Alignment Issue

**Date**: October 27, 2025
**Agent**: Claude Code (Sonnet 4.5)
**Purpose**: Provide detailed diagnostics for AI-based debugging without VS Code access

---

## Executive Summary

**Pattern B Issue**: JP's drop-in fix using `simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using ((sumIdx_add3 ...).symm).trans (sumIdx_congr ...)` hits **maximum recursion depth** at Site 1 and causes **type mismatches** when alternatives are attempted.

**Root Cause Hypothesis**: After `simp only [nabla_g, RiemannUp, sub_eq_add_neg, payload_cancel, ΓΓ_block]` and `rw [← sumIdx_neg]`, the goal contains terms in a partially-expanded form that don't align with what `sumIdx_add3` and `scalar_finish` expect.

---

## Site 1 Detailed Analysis (Lines 7816-7824)

### Context

```lean
-- Location: ricci_identity_on_g_rθ_ext proof, b-branch assembly
calc
  (sumIdx B_b)
- sumIdx (fun ρ => (Γtot M r θ ρ μ a) * (nabla_g M r θ ν ρ b))
+ sumIdx (fun ρ => (Γtot M r θ ρ ν a) * (nabla_g M r θ μ ρ b))
    = sumIdx (fun ρ =>
          - ( dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ
             - dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ
             + sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
             - sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) )
           * g M ρ b r θ) := by
    simp only [nabla_g, RiemannUp, sub_eq_add_neg, payload_cancel, ΓΓ_block]
    rw [← sumIdx_neg]
    -- GOAL AT THIS POINT: (see Goal State 1 below)
    sorry
```

### Goal State 1: After `simp only` and `rw [← sumIdx_neg]` at Line 7821

**From error message at line 7829 (previous attempt)**:

The goal transforms from:
```lean
sumIdx B_b - sumIdx (Γtot * nabla_g ν) + sumIdx (Γtot * nabla_g μ)
```

to (after `simp only` expansion):
```lean
sumIdx (fun ρ => B_b_expanded ρ)
+ sumIdx (fun ρ => -(Γtot_μ_a_expanded ρ))
+ sumIdx (fun ρ => Γtot_ν_a_expanded ρ)
= sumIdx (fun ρ => -(dCoord μ - dCoord ν + sumIdx ΓΓ - sumIdx ΓΓ) * g M ρ b r θ)
```

where:
- `B_b_expanded ρ` includes dCoord terms AND `-(Γtot ...) * dCoord μ (g...)` cancellation terms
- `Γtot_μ_a_expanded ρ` expands `Γtot M r θ ρ μ a * nabla_g M r θ ν ρ b` using nabla_g definition
- `Γtot_ν_a_expanded ρ` expands `Γtot M r θ ρ ν a * nabla_g M r θ μ ρ b` using nabla_g definition

### Key Definitions Involved

#### B_b (Line 7563-7567)
```lean
set B_b : Idx → ℝ := (fun ρ =>
  -(dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ) * g M ρ b r θ
  + (dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ) * g M ρ b r θ
  - (Γtot M r θ ρ ν a) * dCoord μ (fun r θ => g M ρ b r θ) r θ
  + (Γtot M r θ ρ μ a) * dCoord ν (fun r θ => g M ρ b r θ) r θ)
```

**Note**: B_b has FOUR terms:
1. Two dCoord-of-Γ terms (scaled by g)
2. Two Γ-times-dCoord-of-g terms (these should cancel via `payload_cancel`)

#### nabla_g (Line 2840-2843)
```lean
noncomputable def nabla_g (M r θ : ℝ) (c a b : Idx) : ℝ :=
  dCoord c (fun r θ => g M a b r θ) r θ
  - sumIdx (fun e => Γtot M r θ e c a * g M e b r θ)
  - sumIdx (fun e => Γtot M r θ e c b * g M a e r θ)
```

**Expansion Example**:
```lean
Γtot M r θ ρ μ a * nabla_g M r θ ν ρ b
= Γtot M r θ ρ μ a * (dCoord ν (g M ρ b) - sumIdx (...) - sumIdx (...))
= Γtot * dCoord ν (g) - Γtot * sumIdx (...) - Γtot * sumIdx (...)
```

#### scalar_finish (Lines 7789-7804)
```lean
have scalar_finish :
  ∀ ρ,
    ( -(dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ) * g M ρ b r θ
      +  (dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ) * g M ρ b r θ )
    +  ( g M ρ b r θ *
          ( sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
           -sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) ) )
    =
      - ( ( dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ
           - dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ
           + sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
           - sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) )
          * g M ρ b r θ ) := by
  intro ρ
  ring
```

**Note**: `scalar_finish ρ` proves an equality where:
- **LHS** has THREE terms (two dCoord*g terms + one g*ΓΓ term)
- **RHS** is the negation of a big block (RiemannUp expanded form)

**Critical Observation**: `scalar_finish`'s LHS does NOT include the `Γ * dCoord(g)` terms from B_b's last two terms!

#### payload_cancel (Lines 7721-7735)
```lean
have payload_cancel :
  sumIdx (fun ρ =>
    (-(Γtot M r θ ρ ν a) * dCoord μ (fun r θ => g M ρ b r θ) r θ
      + (Γtot M r θ ρ μ a) * dCoord ν (fun r θ => g M ρ b r θ) r θ)
    - ((Γtot M r θ ρ μ a) * dCoord ν (fun r θ => g M ρ b r θ) r θ
       - (Γtot M r θ ρ ν a) * dCoord μ (fun r θ => g M ρ b r θ) r θ)
  ) = 0 := by
  have h : ∀ ρ, (...) - (...) = 0 := by intro ρ; ring
  simp only [h]
  exact sumIdx_zero
```

**Purpose**: Shows that the `Γ * dCoord(g)` terms from B_b and from expanding `Γ * nabla_g` cancel out.

#### ΓΓ_block (Lines 7739-7748)
```lean
have ΓΓ_block :
    ( sumIdx (fun ρ => (Γtot M r θ ρ μ a) * sumIdx (fun e => Γtot M r θ e ν ρ * g M e b r θ))
    - sumIdx (fun ρ => (Γtot M r θ ρ ν a) * sumIdx (fun e => Γtot M r θ e μ ρ * g M e b r θ)) )
  + ( sumIdx (fun ρ => (Γtot M r θ ρ μ a) * sumIdx (fun e => Γtot M r θ e ν b * g M ρ e r θ))
    - sumIdx (fun ρ => (Γtot M r θ ρ ν a) * sumIdx (fun e => Γtot M r θ e μ b * g M ρ e r θ)) )
  =
    bb_core + rho_core_b
```

**Purpose**: Shows that the `Γ * sumIdx(Γ * g)` terms from expanding `Γ * nabla_g` combine into cores.

### The Shape Mismatch Problem

**After `simp only [nabla_g, RiemannUp, sub_eq_add_neg, payload_cancel, ΓΓ_block]`**, the goal should be:

```lean
sumIdx (fun ρ =>
  [ B_b's first two terms: -(dCoord μ ...) * g + (dCoord ν ...) * g ]
  + [ B_b's last two terms: -(Γ * dCoord μ (g)) + (Γ * dCoord ν (g)) ]
  + [ From -Γ*nabla_g expansion: -(Γ * dCoord ν (g)) + (Γ * sumIdx(Γg)) + (Γ * sumIdx(Γg)) ]
  + [ From +Γ*nabla_g expansion:  +(Γ * dCoord μ (g)) - (Γ * sumIdx(Γg)) - (Γ * sumIdx(Γg)) ]
)
```

After `payload_cancel` simplification, the `Γ * dCoord(g)` terms should vanish.
After `ΓΓ_block` simplification, the `Γ * sumIdx(Γg)` terms should become cores.

**Expected result**:
```lean
sumIdx (fun ρ =>
  -(dCoord μ ...) * g M ρ b r θ
  + (dCoord ν ...) * g M ρ b r θ
  + g M ρ b r θ * (ΓΓ_core_terms)
)
```

This SHOULD match `scalar_finish ρ`'s LHS exactly!

**BUT**: The error message shows it doesn't. Why?

### Hypothesis: simp only doesn't simplify inside sumIdx binders

The `simp only [payload_cancel, ΓΓ_block]` may not be reaching inside the `sumIdx (fun ρ => ...)` binders to apply those lemmas.

**Evidence**: The error at line 7829 showed:
```
has type
  -dCoord μ ... * g M ρ b r θ + dCoord ν ... * g M ρ b r θ +
      g M ρ b r θ * ((sumIdx ...) - sumIdx ...) = -(...)
but is expected to have type
  B_b ρ + -(Γtot M r θ ρ μ a * nabla_g M r θ ν ρ b) + Γtot M r θ ρ ν a * nabla_g M r θ μ ρ b = -(...)
```

So `scalar_finish ρ` has the EXPANDED form (dCoord, sumIdx), but the goal still has UNEXPANDED form (B_b, nabla_g).

---

## JP's Intended Fix (What Should Work)

```lean
simp only [nabla_g, RiemannUp, sub_eq_add_neg, payload_cancel, ΓΓ_block]
rw [← sumIdx_neg]
simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
  ((sumIdx_add3
      (fun ρ => - dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ * g M ρ b r θ)
      (fun ρ =>   dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ * g M ρ b r θ)
      (fun ρ =>   g M ρ b r θ *
                    ( sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
                    - sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) ))
    ).symm).trans
  (sumIdx_congr (fun ρ => scalar_finish ρ))
```

**Expected flow**:
1. After first `simp only`, goal is in expanded form
2. `rw [← sumIdx_neg]` converts `- sumIdx F` to `sumIdx (fun ρ => -F ρ)`
3. Goal is now: `sumIdx G + sumIdx (fun ρ => -F ρ) + sumIdx H = sumIdx RHS`
4. `(sumIdx_add3 ...).symm` packs to: `sumIdx (fun ρ => G ρ + (-F ρ) + H ρ) = sumIdx RHS`
5. `.trans (sumIdx_congr (fun ρ => scalar_finish ρ))` applies pointwise equality
6. `simpa [...]` handles remaining +/- associativity/commutativity

**Why it fails in practice**:
- Step 1: `simp only` may not fully expand inside binders
- Step 6: `simpa [...]` hits maximum recursion (likely due to bidirectional lemmas)

---

## Attempted Fixes and Results

### Attempt 1: JP's exact form
```lean
simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using (...)
```
**Result**: `maximum recursion depth has been reached`

### Attempt 2: Split simpa into simp only + exact
```lean
simp only [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
exact ((...).symm).trans (sumIdx_congr ...)
```
**Result**: `Tactic 'simp' failed with a nested error: maximum recursion depth` OR timeouts

### Attempt 3: Use convert
```lean
convert ((...).symm).trans (sumIdx_congr ...)
```
**Result**: Additional goals generated, made things worse

### Attempt 4: Use refine + ring
```lean
refine ((...).symm).trans (sumIdx_congr ...)
ring
```
**Result**: Type mismatch, ring couldn't close

### Attempt 5: Explicit calc chain
```lean
calc sumIdx F + sumIdx G + sumIdx H
    = sumIdx (fun ρ => F ρ + G ρ + H ρ) := by exact (sumIdx_add3 ...).symm
  _ = sumIdx RHS := by exact sumIdx_congr (fun ρ => scalar_finish ρ)
```
**Result**: Type mismatch at `exact sumIdx_congr (fun ρ => scalar_finish ρ)`
- `scalar_finish ρ` has expanded form
- But calc step still has unexpanded B_b, nabla_g terms

---

## Site 2: Symmetric Case (Lines 7960-7963)

**Identical pattern to Site 1**, with a/b roles swapped:
- Uses `B_a` instead of `B_a`
- Uses `rho_core_a` instead of `rho_core_b`
- Otherwise exact same structure and same failure modes

---

## Site 3: Line ~8430 (Not Yet Attempted)

Similar type mismatch expected based on error listing. Would benefit from same solution as Sites 1 and 2.

---

## Diagnostic Questions for JP

### Q1: Expansion Inside Binders

Should I add an intermediate step to FORCE expansion inside the sumIdx binders?

**Option A**: Use `conv` to target inside:
```lean
simp only [nabla_g, RiemannUp, sub_eq_add_neg]
conv_lhs =>
  arg 1; ext ρ
  simp only [payload_cancel, ΓΓ_block]
rw [← sumIdx_neg]
-- then your sumIdx_add3 approach
```

**Option B**: Build explicit intermediate `have` showing the expanded form:
```lean
simp only [nabla_g, RiemannUp, sub_eq_add_neg]
have hexp : sumIdx B_b + ... = sumIdx (fun ρ => <fully expanded form>) := by
  simp only [hBb, payload_cancel, ΓΓ_block]
  -- then prove the equality explicitly
rw [hexp]
-- then your sumIdx_add3 approach on the clean expanded goal
```

### Q2: Recursion Avoidance

The `simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]` hits recursion limits.

**Hypothesis**: These lemmas interact badly with sumIdx-related simp lemmas (like `sumIdx_add3` being marked `@[simp]`), causing infinite ping-pong.

**Question**: Should I use a more restrictive normalizer?

**Option A**: Just `ring` after the `.trans`:
```lean
((sumIdx_add3 ...).symm).trans (sumIdx_congr (fun ρ => scalar_finish ρ))
ring
```

**Option B**: Use `norm_num` or `field_simp`:
```lean
((sumIdx_add3 ...).symm).trans (sumIdx_congr (fun ρ => scalar_finish ρ))
norm_num [add_comm, add_assoc]
```

**Option C**: Just `rfl` (if definitionally equal after trans):
```lean
exact ((sumIdx_add3 ...).symm).trans (sumIdx_congr (fun ρ => scalar_finish ρ))
```

### Q3: Order of Operations

After `simp only [nabla_g, RiemannUp, sub_eq_add_neg, payload_cancel, ΓΓ_block]`, I have:

```
sumIdx B_b - sumIdx (Γ * nabla_g ν) + sumIdx (Γ * nabla_g μ)
```

**Should I**:
1. First do `rw [hBb]` to expand B_b into its definition
2. THEN apply `simp only [nabla_g, payload_cancel, ΓΓ_block]`
3. THEN `rw [← sumIdx_neg]`
4. THEN pack with sumIdx_add3?

Or is there a better ordering?

### Q4: Intermediate Lemma Needed?

Should I prove an intermediate lemma like:

```lean
lemma b_branch_calc_step (M r θ : ℝ) (h_ext : Exterior M r θ) (μ ν a b : Idx) :
  sumIdx B_b - sumIdx (fun ρ => Γtot M r θ ρ μ a * nabla_g M r θ ν ρ b)
             + sumIdx (fun ρ => Γtot M r θ ρ ν a * nabla_g M r θ μ ρ b)
  =
  sumIdx (fun ρ => -(dCoord μ ... - dCoord ν ... + sumIdx ... - sumIdx ...) * g M ρ b r θ)
  := by
    -- Use your approach here in a standalone lemma
    ...
```

Then just `exact b_branch_calc_step M r θ h_ext μ ν a b` at the calc step?

---

## Exact Lemma Signatures for Reference

```lean
@[simp] lemma sumIdx_add3 (f g h : Idx → ℝ) :
  sumIdx (fun i => f i + g i + h i) = sumIdx f + sumIdx g + sumIdx h

lemma sumIdx_congr {f g : Idx → ℝ} (h : ∀ i, f i = g i) :
  sumIdx f = sumIdx g

@[simp] lemma sumIdx_neg (f : Idx → ℝ) :
  sumIdx (fun k => - f k) = - sumIdx f

lemma sumIdx_add_distrib (f g : Idx → ℝ) :
  sumIdx (fun i => f i + g i) = sumIdx f + sumIdx g
```

---

## Proposed Minimal Test Case

To isolate the issue, consider this minimal reproduction:

```lean
example (B_b : Idx → ℝ) (F G : Idx → ℝ)
    (scalar_finish : ∀ ρ, B_b ρ + (-F ρ) + G ρ = RHS ρ) :
    sumIdx B_b - sumIdx F + sumIdx G = sumIdx RHS := by
  rw [← sumIdx_neg]
  -- Goal: sumIdx B_b + sumIdx (fun ρ => -F ρ) + sumIdx G = sumIdx RHS
  exact ((sumIdx_add3 B_b (fun ρ => -F ρ) G).symm).trans
         (sumIdx_congr (fun ρ => scalar_finish ρ))
```

**Question**: Does THIS minimal case work? If so, what's different from the actual Site 1 case?

---

## Files Referenced

**Riemann.lean**:
- Line 1586-1595: `sumIdx_add3` definition
- Line 2840-2843: `nabla_g` definition
- Line 7563-7567: `B_b` definition (set statement)
- Line 7721-7735: `payload_cancel` lemma
- Line 7739-7748: `ΓΓ_block` lemma
- Line 7789-7804: `scalar_finish` lemma (pointwise ring equality)
- Line 7816-7824: **Site 1 - Pattern B failure location**
- Line 7960-7963: **Site 2 - Pattern B failure location** (symmetric)
- Line ~8430: **Site 3 - Type mismatch** (not yet attempted)

**Build Logs**:
- `/tmp/build_after_jp_b1_b2.txt` - Best result (20 errors) with `simp only` + `exact`
- `/tmp/build_final_state.txt` - Current state with calc chain (27 errors)
- `/tmp/build_diagnostic_sorries.txt` - With sorry placeholders for goal extraction

---

## Request for JP

Please provide ONE of:

**Option 1**: A specific tactic sequence that avoids the recursion issue
**Option 2**: An intermediate lemma I should prove first
**Option 3**: A different decomposition of the proof (e.g., separate the payload cancellation from the ΓΓ block substitution)
**Option 4**: Confirmation that I should use `conv` to force expansion inside binders
**Option 5**: A minimal working example I can adapt to the actual Site 1 context

---

**Prepared By**: Claude Code (Sonnet 4.5)
**For**: JP (AI Lean Tactics Professor without VS Code)
**Purpose**: Enable debugging with concrete error messages, goal states, lemma signatures, and hypotheses
**Status**: Patterns A/C/D fully successful, Pattern B blocked on shape alignment
**Time Invested**: ~5 hours of systematic attempts documented above

