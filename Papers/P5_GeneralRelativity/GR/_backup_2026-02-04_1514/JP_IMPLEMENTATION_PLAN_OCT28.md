# JP's Implementation Plan: Path to Zero Errors

**Date**: October 28, 2025
**From**: JP (Junior Professor / Tactic Professor)
**Status**: 🎯 **ACTIONABLE** - Clear step-by-step roadmap

---

## Executive Summary

**Current state**: 21 errors from 21 sorries after calc-hardening success

**JP's diagnosis**: "You've killed the recursion; what's left are missing facts (the sorries) and a handful of brittle tactics (assumption, broad simp)."

**Expected outcome**:
- After Phase 1A + 1B: **Single-digit errors**
- After Phase 2A: **Zero errors** ("white on build")

---

## Direct Answers to Questions

### Q1: Priority - Main Theorem Chain FIRST ✅

Do **Main theorem chain** first (ricci_identity_on_g_ext_v2 → nabla_nabla_g_zero_ext → Riemann_swap_a_b).

**Rationale**: "That chain collapses the majority of cascades; Phase‑2A then slots in cleanly and you won't be fighting ghosts created by missing commutator infrastructure."

### Q2: Alternative Contraction Paths - REMOVE ✅

**Remove** lines 2213-2305 (index contraction explorations).

**Rationale**: "Pure distraction now that the reindex/Fubini route is working. If you later want them for pedagogy, resurrect them in a separate Scratch/ file."

### Q3: Edge Cases - EXPLICIT AND TRIVIAL ✅

Add `by_cases h_ext : Exterior M r θ` and dispatch non-exterior branch with one-liner.

**Rationale**: "Most lemmas are stated 'on Exterior' anyway. For poles, carry sin θ ≠ 0 via an off-axis hypothesis. No apology is needed—this is standard local computation on an open chart."

---

## Immediate Action: Domain Bundle (DO THIS FIRST)

**Impact**: Will fix ~5 "assumption failed" errors immediately

**Location**: Near `Exterior` section in Riemann.lean

**Code to paste** (drop-in ready):

```lean
structure OffAxis (θ : ℝ) : Prop := (hθ : Real.sin θ ≠ 0)

structure ChartDomain (M r θ : ℝ) : Prop :=
  (ext : Exterior M r θ)
  (off : OffAxis θ)

namespace ChartDomain
  lemma r_ne_zero  (h : ChartDomain M r θ) : r ≠ 0 := Exterior.r_ne_zero h.ext
  lemma f_ne_zero  (h : ChartDomain M r θ) : f M r ≠ 0 := Exterior.f_ne_zero h.ext
  lemma sin_ne_zero (h : ChartDomain M r θ) : Real.sin θ ≠ 0 := h.off.hθ
  lemma g_diag_ne_zero (h : ChartDomain M r θ) :
    ∀ β : Idx, g M β β r θ ≠ 0 :=
  g_diag_ne_zero_of_exterior_offaxis M r θ h.ext h.off.hθ
end ChartDomain
```

**Usage**: Replace bare `assumption` calls with:

```lean
-- Old (brittle):
have hr0 : r ≠ 0 := by assumption  -- FAILS

-- New (deterministic):
have hr0 := ChartDomain.r_ne_zero h
have hf0 := ChartDomain.f_ne_zero h
have hs0 := ChartDomain.sin_ne_zero h
```

---

## Phase 1A: Main Theorem Chain (HIGHEST LEVERAGE)

### 1. ricci_identity_on_g_ext_v2 (line ~8979)

**Status**: Has commented-out rewrite chain

**Action**: Uncomment and use collectors (no global simp)

**Pattern**:
```lean
have Hpayload := payload_cancel_all M r θ h_ext μ ν a b
have Hmatch   := dGamma_match M r θ h_ext μ ν a b
have Hmain    := main_to_commutator M r θ h_ext μ ν a b
have Hcross   := cross_block_zero M r θ h_ext μ ν a b

calc
  _ = _ := Hpayload
  _ = _ := Hmatch
  _ = _ := by
          -- convert four Σ-pairs to two core-4 Σs deterministically
          rw [collect_four_pairs_to_two_sums]
          -- pull common metric factor with sumIdx_add_same_left/sumIdx_sub_same_right
          -- finish with scalar_pack4/group_add_sub
  _ = _ := Hcross
```

**Key rule**: "When you have (Σ A·G − Σ B·G) + (Σ G·C − Σ G·D), always call sumIdx_collect_comm_block to land directly at Σ G · ((A − B) + (C − D)). This avoids binder-level ring or simp."

**Estimated impact**: May fix 4-5 cascading errors

---

### 2. nabla_nabla_g_zero_ext (line ~9093)

**Action**: Unfold nabla twice, push dCoord, cancel ∂g payloads, reindex ΓΓ

**Pattern**:
```lean
-- Unfold nabla twice
unfold nabla nabla_g

-- Push dCoord across sums/products with localized differentiability
rw [dCoord_add_of_diff, dCoord_sub_of_diff, dCoord_mul_of_diff]
-- (with side conditions handled by discharge_diff)

-- Cancel ∂g payloads with metric-compatibility
rw [dCoord_g_via_compat_ext]

-- Reindex ΓΓ pieces with your eight lemmas:
rw [ΓΓ_main_reindex_a_μ, ΓΓ_main_reindex_a_ν]
rw [ΓΓ_main_reindex_b_μ, ΓΓ_main_reindex_b_ν]
rw [ΓΓ_cross_collapse_a_μ, ΓΓ_cross_collapse_a_ν]
rw [ΓΓ_cross_collapse_b_μ, ΓΓ_cross_collapse_b_ν]

-- Use collectors to line up shape
rw [flatten₄₁, flatten₄₂, group_add_sub, scalar_pack4]

-- Finish with RiemannUp definition
rw [RiemannUp]
```

**Tactics to use**:
- `dCoord_add_of_diff`, `dCoord_sub_of_diff`, `dCoord_mul_of_diff`
- `sumIdx_sub_same_right`, `sumIdx_add_same_left`
- `group_add_sub`, `flatten₄₁`, `flatten₄₂`, `scalar_pack4`

**Critical**: "Do not try to be clever; use your own collectors to line up the shape"

**Estimated impact**: May fix 3-4 cascading errors

---

### 3. Riemann_swap_a_b (line ~9159)

**Action**: Prove upstairs antisymmetry first, then contract

**Step 1**: Prove mixed-index antisymmetry:
```lean
lemma RiemannUp_swap_ρσ
  (M r θ : ℝ) (ρ σ μ ν : Idx) :
  RiemannUp M r θ ρ σ μ ν = - RiemannUp M r θ σ ρ μ ν := by
  -- expand; use torsion-free Γ (lower-index symmetry) + metric-compatibility
  -- reindex inner sums with sumIdx_swap_args explicitly (change+exact)
  -- binder-safe collection; no global simp
  -- the two ΓΓ commutator terms change sign by swapping ρ/σ
  -- the ∂Γ terms cancel via symmetry
  -- finish with ring on scalars (outside binders)
```

**Step 2**: Contract:
```lean
calc
  Riemann M r θ b a c d
      = g M b b r θ * RiemannUp M r θ b a c d := by
          simpa using Riemann_contract_first M r θ b a c d
  _   = g M b b r θ * ( - RiemannUp M r θ a b c d) := by
          simpa using RiemannUp_swap_ρσ M r θ b a c d
  _   = - Riemann M r θ a b c d := by
          -- expand definition; use Riemann_contract_first on a
          -- and simp on this one line only (no binders)
          simp [Riemann, Riemann_contract_first, mul_comm]
```

**Key**: "No diagonality beyond what Riemann_contract_first already uses."

**Estimated impact**: Completes main theorem chain, may fix 2-3 cascading errors

---

## Phase 1B: Kill Forward-Declared Sorries (lines 2115, 2593)

**Problem**: "These two are the only 'unavoidable' sorries the linter reports."

**Options** (pick one):

### Option 1: Move proved version up (cleanest)
Move `dCoord_g_via_compat_ext` (line ~3072) above its call-sites

### Option 2: Prove early versions directly
```lean
-- Sketch: no axioms
unfold nabla_g at *
-- nabla_g = 0 ⇒ solve for ∂g
-- use dCoord_add_of_diff and dCoord_mul_of_diff with localized side-conditions
-- finish with sumIdx_mul, fold_add_left, fold_sub_right
```

**Impact**: "Once these two are gone, several 'assumption failed' errors also disappear because callers stop leaning on ghosts."

**Estimated impact**: May fix 2-3 errors

---

## Tactical Fixes for Current Error Classes

### A) "Tactic assumption failed" (lines 7327, 7368, 7397, 7612, 7647)

**Problem**: "Trying to conjure r ≠ 0, f M r ≠ 0, or sin θ ≠ 0 from thin air."

**Solution**: Use domain bundle accessors

```lean
-- Old (brittle):
assumption  -- FAILS

-- New (deterministic):
have hr0 := ChartDomain.r_ne_zero (show ChartDomain M r θ from h)
have hf0 := ChartDomain.f_ne_zero (show ChartDomain M r θ from h)
have hs0 := ChartDomain.sin_ne_zero (show ChartDomain M r θ from h)

-- Or if still carrying h_ext : Exterior explicitly:
have hr0 := Exterior.r_ne_zero h_ext
have hf0 := Exterior.f_ne_zero h_ext

-- If goal itself is the inequality:
exact hr0  -- or hf0, hs0
```

**Feed them to precise lemmas**:
```lean
inv_ne_zero hf0
pow_ne_zero 2 hr0
```

**Estimated fixes**: 5 errors

---

### B) "simp failed/made no progress" (lines 7912, 7984, 8091, 8162)

**Problem**: Still using `simpa` under binders at reindex lemmas

**Solution**: Apply same change+exact pattern already used for hswap

```lean
-- Old (brittle):
have hpull := by simpa [mul_sumIdx] using mul_sumIdx_lemma

-- New (deterministic):
have hpull : [explicit type] := by
  calc
    _ = _ := by
        apply sumIdx_congr; intro ρ
        ring  -- pointwise commute
    _ = _ := by exact sumIdx_mul
```

**Estimated fixes**: 4 errors

---

### C) Syntax error (line 8201)

**Problem**: "Mismatched calc or by after edits"

**Culprits**:
- Trailing `:= by` with no body after a `set ... with h` block
- Extra `_` placeholder in calc chain

**Action**: Search backwards from 8201 for previous `have ... := by` or `calc` and ensure each step has a proof term.

**Estimated fixes**: 1 error

---

### D) Type mismatch (line 9073)

**Problem**: "Expected pure equality, got a disjunction" because proof still calls old ΓΓ splitter

**Action**:
```bash
grep -n "ΓΓ_quartet_split_" Riemann.lean
```

Replace any stray calls with reindex + collapse lemmas, or delete if dead code.

**Estimated fixes**: 1 error

---

## Phase 2A: Interchange ∂ with Σ (lines 11754-11830)

**Goal**: Fill 6 sorries for differentiability + symmetry

### Step 1: Build product differentiability pointwise

```lean
have h_diff_r : ∀ k, DifferentiableAt ℝ
  (fun p => Γtot M p.1 p.2 k Idx.θ a * g M k b p.1 p.2) (r, θ) := by
  intro k
  -- product rule on ℝ×ℝ
  apply DifferentiableAt.mul
  · -- Γtot differentiability
    apply differentiableAt_Γtot_all_r M r θ h_ext k Idx.θ a
  · -- g differentiability
    apply differentiableAt_g_all_r M r θ h_ext k b
```

### Step 2: Convert to slices

```lean
-- Use differentiableAt_slice_r/_θ to turn product-form into curried slices
have h_slice_r : ∀ k, DifferentiableAt_r
  (fun r θ => Γtot M r θ k Idx.θ a * g M k b r θ) r θ := by
  intro k
  apply differentiableAt_to_slice_r
  exact h_diff_r k
```

### Step 3: Apply dCoord_sumIdx with localized conditions

```lean
rw [dCoord_sumIdx]
· -- main goal proceeds
· -- side condition: ∀ i, DifferentiableAt_r ... ∨ μ ≠ Idx.r
  intro i; left
  exact h_slice_r i
```

### Step 4: Symmetry steps (line 11787)

```lean
have torsion_free :
  Γtot M r' θ' k Idx.θ a = Γtot M r' θ' k a Idx.θ := by
  simpa using (Γtot_symmetry M r' θ' k Idx.θ a)

have g_sym :
  g M k b r' θ' = g M b k r' θ' := by
  simpa [g]  -- definition is symmetric

-- Apply to sum
apply sumIdx_congr; intro k
rw [torsion_free, g_sym]

-- Swap index order if needed
change _ = _
exact sumIdx_swap_args ...
```

### Step 5: Main calc (line 11830)

```lean
calc
  sumIdx (fun k => ∂_r(Γ·g) - ∂_θ(Γ·g))
  _ = sumIdx (fun k => ∂_r(Γ₁) - ∂_θ(Γ₁)) := by
      -- use product rule + collectors
      rw [sum_k_prod_rule_to_Γ₁]
  _ = sumIdx (fun k => Riemann * g) := by
      -- use Riemann_via_Γ₁
      rw [Riemann_via_Γ₁.symm]
```

**Estimated fixes**: 5-6 errors

---

## Replace Last Pockets of Fragility

### 1. No [simp] on bidirectional rewrites ✅
Already done: `sumIdx_swap_args` not marked @[simp]

**Policy**: Keep this for all bidirectional lemmas

### 2. No simpa under binders ✅
Use hardened patterns:
- `change + exact`
- `calc` with `sumIdx_congr` + `sumIdx_mul`

### 3. Kill naked assumption ✅
**Macro fallback fix** (drop-in):

```lean
-- In discharge_diff macro, change last two branches to:
| { simp [DifferentiableAt_r, DifferentiableAt_θ, differentiableAt_const] }
```

This removes brittle `assumption` and gives bounded, deterministic close.

---

## Expected Outcomes After Each Phase

| Phase | Sorries Filled | Expected Error Count | Status |
|-------|----------------|---------------------|--------|
| **Current** | 0/21 | 21 | ✅ Recursion errors eliminated |
| **Domain Bundle** | 0/21 | ~16 | Fix assumption failures |
| **Phase 1A** (3) | 3/21 | 5-8 | Main theorem chain complete |
| **Phase 1B** (2) | 5/21 | 3-5 | Forward declarations gone |
| **Tactical Fixes** | 5/21 | 1-3 | Clean up brittle tactics |
| **Phase 2A** (6) | 11/21 | 0 | **White on build** ✅ |
| **Cleanup** (10) | 21/21 | 0 | All sorries filled |

---

## Implementation Order (Prioritized)

### Week 1 (High ROI):

1. ✅ **Add domain bundle** (30 minutes)
   - Paste structure near Exterior
   - Add accessor lemmas
   - Test compile

2. ✅ **Fix assumption failures** (1-2 hours)
   - Replace bare `assumption` with accessors
   - Lines: 7327, 7368, 7397, 7612, 7647

3. ✅ **Fix discharge_diff macro** (15 minutes)
   - Replace last branch with bounded simp

4. ✅ **Remove alternative contraction paths** (30 minutes)
   - Delete lines 2213-2305
   - May break some callers - fix with sorry temporarily

5. 🎯 **Phase 1A: Main theorem chain** (3-5 days)
   - Line 8979: ricci_identity_on_g_ext_v2
   - Line 9093: nabla_nabla_g_zero_ext
   - Line 9159: Riemann_swap_a_b

6. 🎯 **Phase 1B: Forward declarations** (1-2 hours)
   - Lines 2115, 2593: Prove or move

### Week 2:

7. 🎯 **Tactical fixes** (1-2 days)
   - Fix remaining "simp failed" (lines 7912, 7984, 8091, 8162)
   - Fix syntax error (line 8201)
   - Fix type mismatch (line 9073)

8. 🎯 **Phase 2A: Interchange ∂ with Σ** (3-4 days)
   - Lines 11754-11830: 6 sorries
   - Product differentiability → slice conversions

### Week 3 (Cleanup):

9. ⏸️ **Low-priority sorries** (optional)
   - Edge cases (lines 9165, 9166)
   - Expansion structure (lines 6252, 6258)
   - C²-lite lemmas (lines 6282, 6293)

10. ⏸️ **Polish** (optional)
    - Linter warnings
    - Dead code removal
    - Documentation

---

## Minimal Code Snippets (Copy-Paste Ready)

### 1. Domain Bundle

```lean
structure OffAxis (θ : ℝ) : Prop := (hθ : Real.sin θ ≠ 0)

structure ChartDomain (M r θ : ℝ) : Prop :=
  (ext : Exterior M r θ)
  (off : OffAxis θ)

namespace ChartDomain
  lemma r_ne_zero  (h : ChartDomain M r θ) : r ≠ 0 := Exterior.r_ne_zero h.ext
  lemma f_ne_zero  (h : ChartDomain M r θ) : f M r ≠ 0 := Exterior.f_ne_zero h.ext
  lemma sin_ne_zero (h : ChartDomain M r θ) : Real.sin θ ≠ 0 := h.off.hθ
  lemma g_diag_ne_zero (h : ChartDomain M r θ) :
    ∀ β : Idx, g M β β r θ ≠ 0 :=
  g_diag_ne_zero_of_exterior_offaxis M r θ h.ext h.off.hθ
end ChartDomain
```

### 2. Macro Fallback Fix

```lean
-- In discharge_diff macro, replace last branch:
| { simp [DifferentiableAt_r, DifferentiableAt_θ, differentiableAt_const] }
```

### 3. Assumption Fix Pattern

```lean
-- Old:
have hr0 : r ≠ 0 := by assumption

-- New:
have hr0 := ChartDomain.r_ne_zero h
-- or if using h_ext:
have hr0 := Exterior.r_ne_zero h_ext
```

### 4. Simpa Fix Pattern

```lean
-- Old:
have hpull := by simpa [mul_sumIdx] using base_lemma

-- New:
have hpull : [type] := by
  calc
    _ = _ := by apply sumIdx_congr; intro ρ; ring
    _ = _ := by exact base_lemma
```

---

## Key Principles (JP's Rules)

1. **Never use simpa under binders** ✅
   - Use `change + exact` or `calc` chains

2. **No @[simp] on bidirectional lemmas** ✅
   - Keep `sumIdx_swap_args` explicit-use only

3. **Kill naked assumption** ✅
   - Use domain bundle accessors or named lemmas

4. **Bounded tactics only** ✅
   - `simp only [specific_lemma]` not global `simp`
   - `ring` on scalars (outside binders) only

5. **Keep proofs local and explicit** ✅
   - If touching a Σ, use `sumIdx_congr` + pointwise proof
   - Then single algebraic lemma

6. **Use your collectors** ✅
   - `flatten₄₁`, `flatten₄₂`, `group_add_sub`, `scalar_pack4`
   - `sumIdx_add_same_left`, `sumIdx_sub_same_right`
   - `sumIdx_collect_comm_block`

---

## Success Metrics

### After Phase 1 (1-2 weeks):
- ✅ Domain bundle integrated
- ✅ Main theorem chain complete (3 sorries)
- ✅ Forward declarations resolved (2 sorries)
- ✅ Error count: **< 10**

### After Phase 2 (2-3 weeks):
- ✅ Phase 2A complete (6 sorries)
- ✅ All high-priority sorries filled (11/21)
- ✅ Error count: **0** ("white on build")

### After Cleanup (3-4 weeks):
- ✅ All 21 sorries filled
- ✅ Linter warnings cleaned
- ✅ Documentation complete

---

## Next Steps

**Immediate** (today):
1. Add domain bundle structure
2. Fix discharge_diff macro
3. Test compile

**This week**:
4. Fix assumption failures (5 errors)
5. Remove alternative contraction paths
6. Start Phase 1A (main theorem chain)

**If stuck**: "Ping JP with the three concrete contexts around ~7327/7368/7397 if any survive after the domain-bundle accessor pass; I'll give you the exact one-liners to drop in."

---

**END OF IMPLEMENTATION PLAN**

**Prepared by**: JP + Claude Code
**Date**: October 28, 2025
**Status**: Ready for implementation
