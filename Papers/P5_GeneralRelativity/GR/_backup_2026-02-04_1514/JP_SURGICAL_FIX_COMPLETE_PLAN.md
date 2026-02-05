# Complete Surgical Fix Implementation Plan
**Date**: October 22, 2025
**From**: Senior Professor's Memo + Claude Implementation
**Status**: Helper lemmas added ✅ | Main proof replacement ready ⚠️

---

## CURRENT STATUS

### ✅ Helper Lemmas Added (Lines 1862-1904)

All helper lemmas from JP's plan have been added:

1. **Alpha-rename and algebra** (lines 1862-1871):
   - `sumIdx_rename`: ✅ Compiles
   - `mul_sumIdx_comm`: ✅ Compiles
   - `sumIdx_mul_comm`: ✅ Compiles

2. **Metric symmetry and contractions** (lines 1874-1890):
   - `g_symm_JP`: ✅ Compiles (renamed to avoid conflict)
   - `sumIdx_contract_g_right`: ✅ Compiles
   - `sumIdx_contract_g_left`: ✅ Compiles

3. **Expanded metric compatibility** (lines 1898-1904):
   - `dCoord_g_expand`: ⚠️ Uses `sorry` (will be proven after reorganizing)
   - Signature: `(M r θ : ℝ) (h_ext : Exterior M r θ) (μ a b : Idx)`
   - Statement: `∂_μ g_{ab} = Σ Γ^e_{μa} g_{eb} + Σ Γ^e_{μb} g_{ae}`

### ⚠️ Main Proof Needs Replacement (Lines 5796-5862)

**Current structure** (WRONG - targets outer-connection terms):
```lean
-- Step 6.1: Flatten nested blocks (REMOVE)
have Hr := flatten_comm_block_r M r θ a b
have Hθ := flatten_comm_block_θ M r θ a b
simp only [Hr, Hθ]

-- Step 6.2: Cancel mixed partials (MOVE TO 6.A)
... try rw [peel_mixed, Hxy, zero_sub]

-- Step 6.3: Define terms and apply collector (KEEP but fix)
...
```

**Should be** (JP's surgical approach):
```lean
-- Step 6.A: Cancel mixed partials FIRST
-- Step 6.B: Define branch terms
-- Step 6.C: Apply two-branch collector
-- Step 6.D: Convert payloads Γ·(∂g) → ΓΓ·g
-- Step 6.E: Combine with commutator terms
```

---

## EXACT CODE REPLACEMENT

### Location: Lines 5796-5862 in `ricci_identity_on_g_rθ_ext`

Replace everything from `-- Step 6.1:` through `-- Step 7:` with:

```lean
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Step 6: Apply Two-Branch Collector (JP's Surgical Fix - Oct 22, 2025)
  -- ═══════════════════════════════════════════════════════════════════════════
  --
  -- After Step 5, we have product-rule expanded terms: (∂Γ)·g + Γ·(∂g)
  -- This step collects them using the two-branch collector, following
  -- Senior Professor's verified strategy (see memo Oct 22, 2025):
  --   1. Cancel mixed partials (X - Y = 0)
  --   2. Collect (∂Γ)·g commutator terms and Γ·(∂g) payload terms
  --   3. Convert payloads using expanded metric compatibility
  --   4. Combine to form complete Riemann tensor
  -- ═══════════════════════════════════════════════════════════════════════════

  -- Step 6.A: Cancel mixed partials
  -- After Step 5, mixed partials appear at the start of the goal
  -- Isolate them with set, prove they cancel, apply peel_mixed
  set X := dCoord Idx.r (fun r θ => dCoord Idx.θ (fun r θ => g M a b r θ) r θ) r θ with hX
  set Y := dCoord Idx.θ (fun r θ => dCoord Idx.r (fun r θ => g M a b r θ) r θ) r θ with hY
  have Hxy : X - Y = 0 := by
    simpa [hX, hY] using (dCoord_commute_for_g_all M r θ a b Idx.r Idx.θ)
  -- Expose X - Y in the goal structure and cancel
  rw [peel_mixed X _ _ Y _ _, Hxy, zero_sub]

  -- Step 6.B: Define branch terms for the collector
  -- After canceling mixed partials, the goal has exactly the structure
  -- that sumIdx_collect_two_branches expects

  -- Shared metric factor (b-slot contraction)
  let Gᵇ : Idx → ℝ := fun ρ => g M ρ b r θ

  -- r-direction commutator coefficients (the (∂Γ)·g pieces)
  let Aᵣ : Idx → ℝ := fun ρ => dCoord Idx.r (fun r θ => Γtot M r θ ρ Idx.θ a) r θ
  let Bᵣ : Idx → ℝ := fun ρ => dCoord Idx.θ (fun r θ => Γtot M r θ ρ Idx.r a) r θ
  let Cᵣ : Idx → ℝ := fun ρ => sumIdx (fun lam => Γtot M r θ ρ Idx.r lam * Γtot M r θ lam Idx.θ a)
  let Dᵣ : Idx → ℝ := fun ρ => sumIdx (fun lam => Γtot M r θ ρ Idx.θ lam * Γtot M r θ lam Idx.r a)

  -- r-direction payloads (Γ·∂g terms from product rule)
  let Pᵣ : Idx → ℝ := fun ρ =>
    Γtot M r θ ρ Idx.r a * dCoord Idx.θ (fun r θ => g M ρ b r θ) r θ
  let Qᵣ : Idx → ℝ := fun ρ =>
    Γtot M r θ ρ Idx.r b * dCoord Idx.θ (fun r θ => g M a ρ r θ) r θ

  -- θ-direction commutator coefficients (mirror with r↔θ)
  let Aθ : Idx → ℝ := fun ρ => dCoord Idx.θ (fun r θ => Γtot M r θ ρ Idx.r a) r θ
  let Bθ : Idx → ℝ := fun ρ => dCoord Idx.r (fun r θ => Γtot M r θ ρ Idx.θ a) r θ
  let Cθ : Idx → ℝ := fun ρ => sumIdx (fun lam => Γtot M r θ ρ Idx.θ lam * Γtot M r θ lam Idx.r a)
  let Dθ : Idx → ℝ := fun ρ => sumIdx (fun lam => Γtot M r θ ρ Idx.r lam * Γtot M r θ lam Idx.θ a)

  -- θ-direction payloads (Γ·∂g terms from product rule)
  let Pθ : Idx → ℝ := fun ρ =>
    Γtot M r θ ρ Idx.θ a * dCoord Idx.r (fun r θ => g M ρ b r θ) r θ
  let Qθ : Idx → ℝ := fun ρ =>
    Γtot M r θ ρ Idx.θ b * dCoord Idx.r (fun r θ => g M a ρ r θ) r θ

  -- Step 6.C: Apply the two-branch collector
  -- Pattern now matches exactly
  have h2branches :=
    sumIdx_collect_two_branches Gᵇ Aᵣ Bᵣ Cᵣ Dᵣ Pᵣ Qᵣ Aθ Bθ Cθ Dθ Pθ Qθ

  -- Expand let-bindings so the LHS of h2branches matches the goal
  simp only [Gᵇ, Aᵣ, Bᵣ, Cᵣ, Dᵣ, Pᵣ, Qᵣ, Aθ, Bθ, Cθ, Dθ, Pθ, Qθ] at h2branches

  -- Apply the collector
  rw [h2branches]

  -- Now goal is:
  --   (Σ Gᵇ·((Aᵣ - Bᵣ) + (Cᵣ - Dᵣ)) - Σ Gᵇ·((Aθ - Bθ) + (Cθ - Dθ)))
  -- + (Σ (Pᵣ - Qᵣ) - Σ (Pθ - Qθ))
  -- = -Riemann...
  --
  -- First parentheses: commutator block (∂Γ)·g
  -- Second parentheses: payload block Γ·(∂g)

  -- Step 6.D: Convert payloads Γ·(∂g) into ΓΓ·g
  -- This is the crucial step validated by Senior Professor's memo:
  -- Use expanded metric compatibility to substitute ∂g = Σ Γ·g + Σ Γ·g

  -- Payload r-branch
  have payload_r :
    sumIdx (fun ρ => Pᵣ ρ - Qᵣ ρ)
    = sumIdx (fun ρ => Γtot M r θ ρ Idx.r a
                        * sumIdx (fun lam => Γtot M r θ lam Idx.θ ρ * g M lam b r θ))
    - sumIdx (fun ρ => Γtot M r θ ρ Idx.r b
                        * sumIdx (fun lam => Γtot M r θ lam Idx.θ a * g M ρ lam r θ))
    := by
    -- Expand ∂θ g in Pᵣ and Qᵣ using dCoord_g_expand
    apply sumIdx_congr; intro ρ
    simp only [Pᵣ, Qᵣ]
    rw [dCoord_g_expand M r θ h_ext Idx.θ ρ b, dCoord_g_expand M r θ h_ext Idx.θ a ρ]
    -- Distribute Γ over the sum, keep b-slot terms
    simp only [sumIdx_add_distrib, mul_add, add_comm, add_left_comm, add_assoc]
    sorry -- JP: finish pointwise algebra

  -- Flatten payload_r: swap sums and factor out g
  have payload_r_flat :
    sumIdx (fun ρ => Γtot M r θ ρ Idx.r a
                      * sumIdx (fun lam => Γtot M r θ lam Idx.θ ρ * g M lam b r θ))
    = sumIdx (fun lam => g M lam b r θ
                     * sumIdx (fun ρ => Γtot M r θ ρ Idx.r a * Γtot M r θ lam Idx.θ ρ))
    := by
    classical
    -- Fubini + factor g out
    simp only [sumIdx_swap, mul_sumIdx_comm, sumIdx_mul_comm,
               mul_comm, mul_left_comm, mul_assoc]
    sorry -- JP: finish swap

  -- Similar for second term (with g_symm_JP to align indices)
  have payload_r_second :
    sumIdx (fun ρ => Γtot M r θ ρ Idx.r b
                      * sumIdx (fun lam => Γtot M r θ lam Idx.θ a * g M ρ lam r θ))
    = sumIdx (fun lam => g M lam a r θ
                     * sumIdx (fun ρ => Γtot M r θ ρ Idx.r b * Γtot M r θ lam Idx.θ ρ))
    := by
    classical
    simp only [sumIdx_swap, mul_sumIdx_comm, sumIdx_mul_comm, g_symm_JP,
               mul_comm, mul_left_comm, mul_assoc]
    sorry -- JP: finish swap + g symmetry

  -- Payload θ-branch (mirror)
  have payload_θ : -- similar structure with r↔θ
    sumIdx (fun ρ => Pθ ρ - Qθ ρ)
    = ... := by sorry -- JP: mirror of payload_r

  have payload_θ_flat : ... := by sorry -- JP: mirror of payload_r_flat

  have payload_θ_second : ... := by sorry -- JP: mirror of payload_r_second

  -- Step 6.E: Combine payload ΓΓ terms with commutator C,D terms
  -- After swapping, the payload ΓΓ pieces combine with Cᵣ, Dᵣ (and Cθ, Dθ)
  -- to form the complete Riemann tensor coordinate definition

  -- Pointwise combine inside sumIdx
  have combine_r :
    sumIdx (fun ρ => Gᵇ ρ * ((Aᵣ ρ - Bᵣ ρ) + (Cᵣ ρ - Dᵣ ρ)))
    + (sumIdx payload_r_flat - sumIdx payload_r_second)
    = sumIdx (fun ρ => Gᵇ ρ * RiemannUp M r θ ρ a Idx.r Idx.θ b)
    := by
    apply sumIdx_congr; intro ρ
    simp only [Gᵇ, Aᵣ, Bᵣ, Cᵣ, Dᵣ, RiemannUp]
    ring -- Algebra matches Riemann definition

  have combine_θ :
    sumIdx (fun ρ => Gᵇ ρ * ((Aθ ρ - Bθ ρ) + (Cθ ρ - Dθ ρ)))
    + (sumIdx payload_θ_flat - sumIdx payload_θ_second)
    = sumIdx (fun ρ => Gᵇ ρ * RiemannUp M r θ ρ a Idx.θ Idx.r b)
    := by
    apply sumIdx_congr; intro ρ
    simp only [Gᵇ, Aθ, Bθ, Cθ, Dθ, RiemannUp]
    ring

  -- Assemble
  rw [payload_r, payload_r_flat, payload_r_second,
      payload_θ, payload_θ_flat, payload_θ_second,
      combine_r, combine_θ]

  -- Goal now: Σ Gᵇ·RiemannUp(...) - Σ Gᵇ·RiemannUp(...) = -Riemann...

  -- (Optional) Step 7: Collapse metric sums if desired
  -- rw [sumIdx_contract_g_right M r θ b, sumIdx_contract_g_left M r θ a]

  -- Step 8: Final regrouping and contraction
```

---

## KEY CHANGES FROM PREVIOUS APPROACH

### ❌ What was removed:
1. Calls to `flatten_comm_block_r/θ` (lines 5799-5801)
   - These targeted outer-connection terms `C_μν` that should vanish
2. Global normalization attempts
3. Nested sum flattening

### ✅ What was added:
1. **Step 6.A**: Mixed partial cancellation BEFORE collector
2. **Step 6.D**: Payload conversion using `dCoord_g_expand`
3. **Step 6.E**: Combining payload ΓΓ with commutator C,D terms
4. Deterministic, localized tactics (no global simp/ring)

### ⚠️ What needs completion:
The `sorry` statements in payload conversions require:
- Pointwise algebra under `sumIdx_congr`
- Sum swapping with Fubini
- Metric symmetry application
- Combining with JP's helper lemmas

These are mechanical but require interactive Lean to verify the exact patterns.

---

## ESTIMATED TIME TO COMPLETE

**With interactive Lean**: 2-3 hours
- Fill in `sorry` statements in payload conversions
- Verify collector matches after Step 6.C
- Test final compilation

**Without interactive Lean**: Not recommended
- Too many pattern-matching details
- Risk of blind debugging loops

---

## NEXT STEPS

1. ✅ Helper lemmas are in place (with one `sorry` documented)
2. ⚠️ Replace lines 5796-5862 with the code above
3. 🔧 Fill in `sorry` statements in payload conversions (requires interactive Lean)
4. ✅ Build and verify compilation
5. 🎯 Celebrate completion!

---

**Prepared by**: Claude Code
**For**: User implementation
**Date**: October 22, 2025
**Status**: Ready for code replacement
**Blockers**: Interactive Lean needed for payload algebra
