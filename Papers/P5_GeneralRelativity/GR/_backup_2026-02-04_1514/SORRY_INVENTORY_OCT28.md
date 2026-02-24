# Sorry Inventory for Riemann.lean

**Date**: October 28, 2025
**File**: `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean`
**Total sorries**: 21 (not 2!)

**Note**: The linter only warns about 2 sorries (lines 2115 and 2593), but there are actually **21 sorry statements** in the file.

---

## Category A: Forward Declarations (2 sorries)

These are explicitly marked as temporary, to be proven later in the file.

### 1. Line 2115-2121: `dCoord_g_expand`
**Purpose**: Metric compatibility rearranged to solve for ∂g
**Status**: Forward declaration
**Comment**: "Uses sorry temporarily because nabla_g_zero_ext is defined later in the file. Will be proven after reorganizing helpers."
```lean
lemma dCoord_g_expand
    (M r θ : ℝ) (h_ext : Exterior M r θ) (μ a b : Idx) :
  dCoord μ (fun r θ => g M a b r θ) r θ
    = sumIdx (fun e => Γtot M r θ e μ a * g M e b r θ)
    + sumIdx (fun e => Γtot M r θ e μ b * g M a e r θ) := by
  sorry
```

### 2. Line 2593-2597: `dCoord_g_via_compat_ext_temp`
**Purpose**: Forward declaration of metric compatibility
**Status**: "Proven later at line 3072 as dCoord_g_via_compat_ext"
**Comment**: "This forward declaration uses sorry to avoid axiom in CI."
```lean
lemma dCoord_g_via_compat_ext_temp (M r θ : ℝ) (h_ext : Exterior M r θ) (x a b : Idx) :
  dCoord x (fun r θ => g M a b r θ) r θ =
    sumIdx (fun k => Γtot M r θ k x a * g M k b r θ) +
    sumIdx (fun k => Γtot M r θ k x b * g M a k r θ) := by
  sorry
```

---

## Category B: Index Contraction Gaps (4 sorries)

These require understanding metric contraction and index renaming/reordering.

### 3. Line 2213: Riemann via ΓΓg (r-branch, term h₂)
**Context**: Inside `riemann_via_gamma_Gamma_g_r`
**Issue**: "This requires index renaming and reordering - needs interactive Lean"
```lean
-- Final step: show sumIdx (Γ_d * Γ_e,d) = sumIdx (Γ_ρ,lam * Γ_lam,a)
sorry
```

### 4. Line 2225: Riemann via ΓΓg (r-branch, term h₃)
**Context**: Inside `riemann_via_gamma_Gamma_g_r`
**Issue**: "For the moment, use sorry as this requires understanding the metric contraction"
```lean
-- The key insight: g M d e r θ only contributes when we contract properly
-- After distribution and swapping, the d-index in g should align with the d in Γ
sorry
```

### 5. Line 2296: Riemann via ΓΓg (θ-branch, term h₂)
**Context**: Inside `riemann_via_gamma_Gamma_g_theta`
**Issue**: Same as line 2213 (index renaming)
```lean
-- This requires index renaming and reordering - needs interactive Lean
sorry
```

### 6. Line 2305: Riemann via ΓΓg (θ-branch, term h₃)
**Context**: Inside `riemann_via_gamma_Gamma_g_theta`
**Issue**: "Same index contraction issue as h₃ in r-branch"
```lean
sorry
```

---

## Category C: Expansion Structure Gaps (2 sorries)

High-level structure lemmas that outline the proof but don't fill in details.

### 7. Line 6252: `algebraic_identity_expanded`
**Purpose**: Show expanded form of (∂Γ)g + ΓΓg + Γ∂g structure
**Status**: TODO with outline
```lean
-- TODO: Fill in expanded form showing (∂Γ)g + ΓΓg + Γ∂g structure
sorry := by
  unfold P_terms C_terms_a C_terms_b
  unfold nabla_g
```

### 8. Line 6258: `algebraic_identity_expanded` (continuation)
**Purpose**: Push dCoord through sumIdx/products
**Issue**: "need differentiability, product rule, discharge DifferentiableAt_* side conditions"
```lean
-- Push dCoord through sumIdx (need differentiability)
-- Push dCoord through products (product rule)
sorry
```

---

## Category D: Differentiability Gaps (2 sorries)

C²-lite lemmas for metric derivatives.

### 9. Line 6282: `dCoord_g_differentiable_r_ext`
**Purpose**: r-slice differentiability of ν-partial of metric
**Status**: TODO
```lean
lemma dCoord_g_differentiable_r_ext
    (M r θ : ℝ) (h_ext : Exterior M r θ) (ν a b : Idx) :
  DifferentiableAt_r (fun r θ => dCoord ν (fun r θ => g M a b r θ) r θ) r θ := by
  sorry
```

### 10. Line 6293: `dCoord_g_differentiable_θ_ext`
**Purpose**: θ-slice differentiability of ν-partial of metric
**Status**: TODO
```lean
lemma dCoord_g_differentiable_θ_ext
    (M r θ : ℝ) (h_ext : Exterior M r θ) (ν a b : Idx) :
  DifferentiableAt_θ (fun r θ => dCoord ν (fun r θ => g M a b r θ) r θ) r θ := by
  sorry
```

---

## Category E: Main Theorem Gaps (3 sorries)

Top-level results that depend on upstream proofs.

### 11. Line 8979: `ricci_identity_on_g_ext_v2`
**Purpose**: Ricci identity via commutator structure
**Status**: Disabled (commented out steps)
**Comment**: Has commented-out rewrite chain
```lean
-- rw [payload_cancel_all M r θ h_ext μ ν a b]
-- rw [dGamma_match M r θ h_ext μ ν a b]
-- rw [main_to_commutator M r θ h_ext μ ν a b]
-- rw [cross_block_zero M r θ h_ext μ ν a b]
sorry
```

### 12. Line 9093: `nabla_nabla_g_zero_ext`
**Purpose**: Ricci identity for metric (∇_c ∇_d g - ∇_d ∇_c g = -R)
**Status**: TODO
```lean
lemma nabla_nabla_g_zero_ext
    (M r θ : ℝ) (h_ext : Exterior M r θ) (a b c d : Idx) :
  nabla (fun M r θ a b => nabla_g M r θ d a b) M r θ c a b
  - nabla (fun M r θ a b => nabla_g M r θ c a b) M r θ d a b
  = - Riemann M r θ b a c d - Riemann M r θ a b c d := by
  sorry
```

### 13. Line 9159: `Riemann_swap_a_b`
**Purpose**: First-pair antisymmetry (R_{ba,μν} = -R_{ab,μν})
**Status**: "TODO: Full proof requires completing ricci_identity_on_g and nabla_nabla_g_zero_ext"
**Comment**: "Standard textbook result: MTW Box 8.5, Wald Appendix B"
```lean
lemma Riemann_swap_a_b (M r θ : ℝ) (a b c d : Idx) :
  Riemann M r θ b a c d = - Riemann M r θ a b c d := by
  sorry
```

---

## Category F: Edge Case Gaps (2 sorries)

Handling non-exterior region cases.

### 14. Line 9165: `Riemann_swap_a_b` (r ≤ 2M case)
**Purpose**: Antisymmetry when r ≤ 2M
**Status**: TODO
```lean
· sorry -- r ≤ 2M case
```

### 15. Line 9166: `Riemann_swap_a_b` (M ≤ 0 case)
**Purpose**: Antisymmetry when M ≤ 0
**Status**: TODO
```lean
· sorry -- M ≤ 0 case
```

---

## Category G: Phase 2A Gaps (6 sorries)

These are in the "ricci_identity_on_g_rθ_ext" proof and need differentiability lemmas to interchange ∂ and Σ.

### 16. Line 11754: Differentiability for r-slice
**Purpose**: Show Γtot and g are differentiable in r
**Status**: "TODO: Requires Γtot and g differentiability lemmas"
```lean
have h_diff_r : ∀ k, DifferentiableAt ℝ (fun p => Γtot M p.1 p.2 k Idx.θ a * g M k b p.1 p.2) (r, θ) := by
  sorry
```

### 17. Line 11756: Differentiability for θ-slice
**Purpose**: Show Γtot and g are differentiable in θ
**Status**: "TODO: Requires Γtot and g differentiability lemmas"
```lean
have h_diff_θ : ∀ k, DifferentiableAt ℝ (fun p => Γtot M p.1 p.2 k Idx.r a * g M k b p.1 p.2) (r, θ) := by
  sorry
```

### 18. Line 11771: Convert differentiability formats
**Purpose**: Convert h_diff_r/h_diff_θ to DifferentiableAt_r/DifferentiableAt_θ format
**Status**: TODO
```lean
-- TODO: Need to convert h_diff_r/h_diff_θ to DifferentiableAt_r/DifferentiableAt_θ format
sorry
```

### 19. Line 11787: Symmetry lemmas
**Purpose**: Apply Γtot symmetry (torsion-free) and metric symmetry
**Status**: "TODO: Need explicit symmetry lemmas"
```lean
-- TODO: Need explicit symmetry lemmas:
-- Γtot M r' θ' k Idx.θ a = Γtot M r' θ' k a Idx.θ
-- g M k b r' θ' = g M b k r' θ'
sorry
```

### 20. Line 11800: Index algebra
**Purpose**: Show sumIdx (fun k => Γtot ... * g ...) = sumIdx (fun ρ => g ... * Γtot ...)
**Status**: "TODO: Should be straightforward algebra"
```lean
-- TODO: Should be straightforward algebra
-- sumIdx (fun k => Γtot ... * g ...) = sumIdx (fun ρ => g ... * Γtot ...)
sorry
```

### 21. Line 11830: Main calc chain
**Purpose**: Complete the main calc chain for ricci_identity_on_g_rθ_ext
**Status**: TODO with outline
```lean
-- The structure should be:
-- calc
--   sumIdx (fun k => ∂_r(Γ·g) - ∂_θ(Γ·g))
--   _ = sumIdx (fun k => ∂_r(Γ₁) - ∂_θ(Γ₁))  := sum_k_prod_rule_to_Γ₁
--   _ = sumIdx (fun k => Riemann * g)          := Riemann_via_Γ₁.symm
sorry
```

---

## Summary by Category

| Category | Count | Description |
|----------|-------|-------------|
| A. Forward declarations | 2 | Temporary placeholders, to be proven later |
| B. Index contraction gaps | 4 | Require metric contraction understanding |
| C. Expansion structure gaps | 2 | High-level outline, need details |
| D. Differentiability gaps | 2 | C²-lite lemmas for metric derivatives |
| E. Main theorem gaps | 3 | Top-level results (Ricci identity, antisymmetry) |
| F. Edge case gaps | 2 | Non-exterior region handling |
| G. Phase 2A gaps | 6 | Differentiability + symmetry for Γtot and g |
| **Total** | **21** | |

---

## Why Linter Only Shows 2 Warnings

The Lean linter specifically flags only lines 2115 and 2593 with:
```
warning: Papers/P5_GeneralRelativity/GR/Riemann.lean:2115:6: declaration uses 'sorry'
warning: Papers/P5_GeneralRelativity/GR/Riemann.lean:2593:6: declaration uses 'sorry'
```

**Reason**: These are the only two sorries in **top-level lemma declarations** that are actually referenced elsewhere in the code. The other 19 sorries are:
- Inside proof blocks (not top-level declarations)
- In commented-out code
- In disabled/deprecated sections
- In lemmas that are not currently used

---

## Priority Assessment

### High Priority (Blocking Main Proof)
- Lines 8979, 9093, 9159: Main theorem chain
- Lines 11754, 11756, 11771, 11787, 11800, 11830: Phase 2A proof

### Medium Priority (Infrastructure)
- Lines 2115, 2597: Forward declarations (should be proven)
- Lines 6282, 6293: Differentiability lemmas

### Low Priority (Can Be Deferred)
- Lines 2213, 2225, 2296, 2305: Alternative proof paths
- Lines 6252, 6258: Expansion structure (outline exists)
- Lines 9165, 9166: Edge cases (M ≤ 0, r ≤ 2M)

---

## Relation to 21 Errors

**Key insight**: Many of the 21 errors reported by the build are likely **caused by** these 21 sorries!

The errors include:
- "Tactic `assumption` failed" (5 errors) - likely due to missing sorry'd lemmas
- "unsolved goals" (6 errors) - likely due to gaps in proof chain
- "Tactic `simp` failed" (4 errors) - likely cascading from sorries

**Hypothesis**: If we fill in the high-priority sorries (main theorem chain + Phase 2A), many of the 21 errors may resolve.

---

## Recommendations

1. **Immediate**: Investigate lines 7000-9000 to see which errors are directly caused by which sorries
2. **Short-term**: Focus on Category E (main theorem gaps) and Category G (Phase 2A gaps)
3. **Medium-term**: Prove Category A (forward declarations) and Category D (differentiability)
4. **Long-term**: Clean up Category B (index contraction) and Category F (edge cases)

---

**END OF SORRY INVENTORY**
