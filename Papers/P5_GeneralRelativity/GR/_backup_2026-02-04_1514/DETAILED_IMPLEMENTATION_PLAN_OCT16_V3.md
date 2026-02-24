# Detailed Implementation Plan V3: Phase 3 Steps 4-8
## Date: October 16, 2025
## Based on: SP Tactical Guidance Memo (October 16, 2025)

---

## Executive Summary

This plan provides a step-by-step implementation guide for completing Phase 3 of the `Riemann_via_Γ₁` proof, based on Senior Professor's tactical guidance memo.

**Approach**: Sequential/Conservative (Option A)
- Complete infrastructure first
- Implement Steps 4-7 with explicit breakdowns
- Prove Step 8 lemmas (8A-8D) independently
- Assemble Step 8 in main proof

**Estimated Total Time**: 5-7 hours (with guidance)

**Status**:
- Steps 1-3: ✅ COMPLETE (fully proven)
- Steps 4-7: ⏳ TO IMPLEMENT (following SP guidance)
- Step 8: ⏳ TO IMPLEMENT (4 lemmas + assembly)

---

## Part I: Infrastructure Prerequisites

### Task 1.1: Reorganize `sumIdx` Lemmas

**Problem**: `sumIdx_map_sub` is defined at line 1451, but needed at line 1400

**Solution**: Move all fundamental `sumIdx` lemmas earlier in the file

**Action Items**:
1. Identify all fundamental `sumIdx` lemmas to move:
   - `sumIdx_map_sub` (line 1451)
   - `sumIdx_add_distrib` (check if exists)
   - `mul_sumIdx` (line 1680)
   - `sumIdx_swap_comm` (check if this is same as `sumIdx_swap` at line 1704)

2. Create a new section early in file (around line 1200):
   ```lean
   /-! ### Fundamental sumIdx Infrastructure -/
   ```

3. Move the lemmas to this section in logical order:
   - Addition/subtraction distributivity
   - Multiplication distributivity
   - Fubini (swap)

4. Verify no circular dependencies

5. Ensure all downstream uses still work

**Estimated Time**: 30 minutes

**Dependencies**: None

**Output**: Clean `sumIdx` infrastructure section before `Riemann_via_Γ₁`

---

### Task 1.2: Add Symmetry Lemmas

**Problem**: `g_symm` and `Γtot_symm` are required for Step 8 lemmas

**Solution**: Add explicit symmetry lemmas if they don't exist

**Action Items**:

1. **Check existence**: Search codebase for:
   ```bash
   grep -n "lemma g_symm\|lemma Γtot_symm" Riemann.lean
   ```

2. **If missing, add `g_symm`**:
   ```lean
   /-- Symmetry of the metric tensor: g_{ab} = g_{ba}. -/
   @[simp] lemma g_symm (M r θ : ℝ) (a b : Idx) :
     g M a b r θ = g M b a r θ := by
     -- Proved by case analysis based on the definition of g in Schwarzschild.lean.
     cases a <;> cases b <;> simp [g]
   ```

   **Location**: After metric definition section, with other metric lemmas

   **Proof Strategy**:
   - Use `cases a <;> cases b` to enumerate all 16 combinations
   - Each case reduces to `simp [g]` using definitional equality
   - Schwarzschild metric is diagonal, so g_{ab} = g_{ba} by definition

   **Expected Length**: 3-5 lines

3. **If missing, add `Γtot_symm`**:
   ```lean
   /-- Symmetry of the Christoffel symbols (Torsion-free): Γ^k_{ab} = Γ^k_{ba}. -/
   @[simp] lemma Γtot_symm (M r θ : ℝ) (k a b : Idx) :
     Γtot M r θ k a b = Γtot M r θ k b a := by
     -- Proved by case exhaustion based on the definition of Γtot.
     cases k <;> cases a <;> cases b <;> simp [Γtot]
   ```

   **Location**: After Christoffel definition section

   **Proof Strategy**:
   - Use triple `cases` to enumerate all 64 combinations (4×4×4)
   - Each case reduces to `simp [Γtot]` using torsion-free property
   - Levi-Civita connection has Γ^k_{ab} = Γ^k_{ba} by construction

   **Expected Length**: 3-5 lines

4. **If they exist**, verify they have `@[simp]` attribute and correct statement

**Estimated Time**: 20 minutes (if implementing from scratch), 5 minutes (if verifying)

**Dependencies**: None

**Output**: Two symmetry lemmas available and marked `@[simp]`

**Notes**:
- These lemmas are fundamental mathematical properties
- They must work for general metrics (not just Schwarzschild diagonal)
- For Schwarzschild, the proofs are trivial by `cases` enumeration
- Mark as `@[simp]` so they apply automatically in Step 8 lemmas

---

### Task 1.3: Verify Metric Compatibility Lemma

**Problem**: SP memo references `dCoord_g_via_compat_ext`

**Solution**: Locate and verify this lemma exists with correct statement

**Action Items**:

1. **Search for the lemma**:
   ```bash
   grep -n "dCoord_g_via_compat\|metric.*compat" Riemann.lean Schwarzschild.lean
   ```

2. **Verify statement** should be:
   ```lean
   lemma dCoord_g_via_compat_ext (M r θ : ℝ) (h_ext : Exterior M r θ) (α β μ : Idx) :
     dCoord μ (fun r θ => g M α β r θ) r θ
     = sumIdx (fun σ => Γtot M r θ σ μ α * g M σ β r θ)
     + sumIdx (fun σ => Γtot M r θ σ μ β * g M α σ r θ)
   ```

   **Mathematical Content**: ∂_μ g_{αβ} = Σ_σ (Γ^σ_{μα} g_{σβ} + Γ^σ_{μβ} g_{ασ})

3. **If missing**, note this as a critical blocker:
   - This lemma is fundamental for Step 7
   - Without it, we cannot expand ∂g terms
   - May need to request from SP or implement separately

4. **If found**, verify:
   - It's marked for easy use (perhaps `@[simp]` or easily accessible)
   - Statement matches SP's description
   - Proof is complete (no `sorry`)

**Estimated Time**: 10 minutes

**Dependencies**: None

**Output**: Confirmation that `dCoord_g_via_compat_ext` exists and is usable

**Contingency**: If missing, this is a blocker. Must be implemented before Step 7.

---

### Infrastructure Summary

**Total Time**: 60 minutes

**Deliverables**:
1. ✅ `sumIdx` lemmas reorganized and accessible
2. ✅ `g_symm` available and marked `@[simp]`
3. ✅ `Γtot_symm` available and marked `@[simp]`
4. ✅ `dCoord_g_via_compat_ext` verified to exist

**Build Verification**:
After completing infrastructure, run:
```bash
lake build Papers.P5_GeneralRelativity.GR.Riemann
```
Must pass with 0 errors before proceeding to Steps 4-7.

---

## Part II: Helper Lemma for Step 5

### Task 2.1: Implement `prod_rule_backwards_sum`

**Purpose**: This lemma transforms `Σ_ρ g_{βρ} · ∂_μ Γ^ρ_{aμ}` into `∂_μ(Σ_ρ g_{βρ} Γ^ρ_{aμ}) - Σ_ρ (∂_μ g_{βρ}) Γ^ρ_{aμ}` (product rule backwards, then interchange ∂ and Σ).

**Location**: Define before `Riemann_via_Γ₁`, in a dedicated section

**Statement**:
```lean
/-- Helper Lemma: Product Rule Backwards for summed terms.

    This transforms Σ_ρ (g_{βρ} · ∂_μ Γ^ρ_{aμ}) into ∂_μ(Γ₁_{βaμ}) - Σ_ρ (∂_μ g_{βρ}) · Γ^ρ_{aμ}.

    The proof uses:
    1. Pointwise product rule (dCoord_mul_of_diff)
    2. Interchange of ∂ and Σ (dCoord_r/θ_sumIdx from Phase 2A)
    3. Differentiability discharge via h_ext
-/
lemma prod_rule_backwards_sum (M r θ : ℝ) (h_ext : Exterior M r θ) (β a μ : Idx) :
  sumIdx (fun ρ => g M β ρ r θ * dCoord μ (fun r θ => Γtot M r θ ρ a μ) r θ)
  = dCoord μ (fun r θ => sumIdx (fun ρ => g M β ρ r θ * Γtot M r θ ρ a μ)) r θ
  - sumIdx (fun ρ => dCoord μ (fun r θ => g M β ρ r θ) r θ * Γtot M r θ ρ a μ)
```

**Mathematical Content**:

Starting from LHS:
```
Σ_ρ (g_{βρ} · ∂_μ Γ^ρ_{aμ})
```

Apply product rule to each term (backwards):
```
Σ_ρ [∂_μ(g_{βρ} · Γ^ρ_{aμ}) - (∂_μ g_{βρ}) · Γ^ρ_{aμ}]
```

Distribute sum:
```
Σ_ρ ∂_μ(g_{βρ} · Γ^ρ_{aμ}) - Σ_ρ (∂_μ g_{βρ}) · Γ^ρ_{aμ}
```

Interchange ∂ and Σ on first term:
```
∂_μ [Σ_ρ (g_{βρ} · Γ^ρ_{aμ})] - Σ_ρ (∂_μ g_{βρ}) · Γ^ρ_{aμ}
```

This is the RHS.

**Proof Structure**:

```lean
lemma prod_rule_backwards_sum (M r θ : ℝ) (h_ext : Exterior M r θ) (β a μ : Idx) :
  sumIdx (fun ρ => g M β ρ r θ * dCoord μ (fun r θ => Γtot M r θ ρ a μ) r θ)
  = dCoord μ (fun r θ => sumIdx (fun ρ => g M β ρ r θ * Γtot M r θ ρ a μ)) r θ
  - sumIdx (fun ρ => dCoord μ (fun r θ => g M β ρ r θ) r θ * Γtot M r θ ρ a μ)
  := by
  classical

  -- Step 1: Apply product rule pointwise to each term in the sum
  have h_prod : ∀ ρ, g M β ρ r θ * dCoord μ (fun r θ => Γtot M r θ ρ a μ) r θ
                    = dCoord μ (fun r θ => g M β ρ r θ * Γtot M r θ ρ a μ) r θ
                    - dCoord μ (fun r θ => g M β ρ r θ) r θ * Γtot M r θ ρ a μ := by
    intro ρ
    rw [dCoord_mul_of_diff]
    · ring  -- Normalize the algebraic structure
    · -- Discharge differentiability of g M β ρ
      sorry  -- Use differentiability lemmas for g in Exterior region
    · -- Discharge differentiability of Γtot M r θ ρ a μ
      sorry  -- Use existing Γtot differentiability lemmas

  -- Step 2: Apply h_prod inside the sum
  conv_lhs => arg 1; ext ρ; rw [h_prod ρ]

  -- Step 3: Distribute sum over subtraction
  rw [sumIdx_map_sub]

  -- Step 4: Interchange ∂ and Σ on the first term
  congr 1  -- Focus on the first term
  rw [← dCoord_r_sumIdx]  -- (or dCoord_θ_sumIdx depending on μ)
  · -- Discharge differentiability of the summed function
    intro ρ
    apply DifferentiableAt.mul
    · sorry  -- g differentiability
    · sorry  -- Γtot differentiability
```

**Challenges**:

1. **Differentiability discharge**: Need to prove `g M β ρ` and `Γtot M r θ ρ a μ` are differentiable in Exterior region
   - Should follow from existing lemmas
   - May need to add specific lemmas if missing

2. **Coordinate-specific application**: The lemma statement uses `μ : Idx`, but in the proof we need separate applications for `μ = Idx.r` and `μ = Idx.θ`
   - May need to state two versions (one for r, one for θ)
   - Or use dependent types carefully

3. **Conv tactic**: The `conv_lhs` tactic navigates into the sum structure to apply the rewrite

**Alternative Approach** (if conv is problematic):

```lean
  -- Alternative Step 2: Use congr and funext
  congr 1
  funext ρ
  exact h_prod ρ
```

**Estimated Time**: 45-60 minutes

**Dependencies**:
- `dCoord_mul_of_diff` (product rule for dCoord)
- `dCoord_r_sumIdx`, `dCoord_θ_sumIdx` (Phase 2A lemmas)
- Differentiability lemmas for `g` and `Γtot` in Exterior region

**Testing**: Create a simple test case to verify the lemma works:
```lean
example (M r θ : ℝ) (h_ext : Exterior M r θ) :
  sumIdx (fun ρ => g M Idx.t ρ r θ * dCoord Idx.r (fun r θ => Γtot M r θ ρ Idx.r Idx.θ) r θ)
  = dCoord Idx.r (fun r θ => sumIdx (fun ρ => g M Idx.t ρ r θ * Γtot M r θ ρ Idx.r Idx.θ)) r θ
  - sumIdx (fun ρ => dCoord Idx.r (fun r θ => g M Idx.t ρ r θ) r θ * Γtot M r θ ρ Idx.r Idx.θ) := by
  exact prod_rule_backwards_sum M r θ h_ext Idx.t Idx.r Idx.r
```

**Output**: Proven helper lemma `prod_rule_backwards_sum` ready for use in Step 5

---

## Part III: Steps 4-7 Detailed Implementation

### Current State (After Step 3)

**Expression**:
```lean
sumIdx (fun ρ =>
      g M β ρ r θ * dCoord Idx.r (fun r θ => Γtot M r θ ρ Idx.θ a) r θ
    - g M β ρ r θ * dCoord Idx.θ (fun r θ => Γtot M r θ ρ Idx.r a) r θ
    + g M β ρ r θ * sumIdx (fun lam =>
        Γtot M r θ ρ Idx.r lam * Γtot M r θ lam Idx.θ a
      - Γtot M r θ ρ Idx.θ lam * Γtot M r θ lam Idx.r a))
```

**Structure**: Single sum over ρ containing three parts

**Mathematical Meaning**: Σ_ρ [ g_{βρ} (∂_r Γ^ρ_{θa} - ∂_θ Γ^ρ_{ra} + M^ρ) ]

where M^ρ = Σ_λ (Γ^ρ_{rλ}Γ^λ_{θa} - Γ^ρ_{θλ}Γ^λ_{ra})

---

### Step 4: Split the Sums

**Goal**: Separate the three parts into distinct sums

**Target Expression**:
```lean
  sumIdx (fun ρ => g M β ρ r θ * dCoord Idx.r (fun r θ => Γtot M r θ ρ Idx.θ a) r θ)
- sumIdx (fun ρ => g M β ρ r θ * dCoord Idx.θ (fun r θ => Γtot M r θ ρ Idx.r a) r θ)
+ sumIdx (fun ρ => g M β ρ r θ * sumIdx (fun lam =>
      Γtot M r θ ρ Idx.r lam * Γtot M r θ lam Idx.θ a
    - Γtot M r θ ρ Idx.θ lam * Γtot M r θ lam Idx.r a))
```

**Mathematical Meaning**: Separated into T₁ - T₂ + T₃ where:
- T₁ = Σ_ρ g_{βρ} · ∂_r Γ^ρ_{θa} (∂Γ_r terms)
- T₂ = Σ_ρ g_{βρ} · ∂_θ Γ^ρ_{ra} (∂Γ_θ terms)
- T₃ = Σ_ρ g_{βρ} · M^ρ (ΓΓ terms)

**Proof Tactics**:

```lean
    -- Step 4: Split the main sum using distribution laws.
    _ = sumIdx (fun ρ => g M β ρ r θ * dCoord Idx.r (fun r θ => Γtot M r θ ρ Idx.θ a) r θ)
      - sumIdx (fun ρ => g M β ρ r θ * dCoord Idx.θ (fun r θ => Γtot M r θ ρ Idx.r a) r θ)
      + sumIdx (fun ρ => g M β ρ r θ * sumIdx (fun lam =>
            Γtot M r θ ρ Idx.r lam * Γtot M r θ lam Idx.θ a
          - Γtot M r θ ρ Idx.θ lam * Γtot M r θ lam Idx.r a)) := by
      -- The sum currently has structure: Σ(A - B + C)
      -- We want: Σ(A) - Σ(B) + Σ(C)

      -- First, rewrite A - B + C as (A + C) - B
      congr 1
      funext ρ
      ring  -- Normalize to (A + C) - B structure

      -- Now distribute: Σ((A + C) - B) = Σ(A + C) - Σ(B)
      rw [sumIdx_map_sub]

      -- Finally distribute: Σ(A + C) = Σ(A) + Σ(C)
      rw [sumIdx_add_distrib]
```

**Alternative (Simpler) Approach**:

```lean
    _ = sumIdx (fun ρ => g M β ρ r θ * dCoord Idx.r (fun r θ => Γtot M r θ ρ Idx.θ a) r θ)
      - sumIdx (fun ρ => g M β ρ r θ * dCoord Idx.θ (fun r θ => Γtot M r θ ρ Idx.r a) r θ)
      + sumIdx (fun ρ => g M β ρ r θ * sumIdx (fun lam =>
            Γtot M r θ ρ Idx.r lam * Γtot M r θ lam Idx.θ a
          - Γtot M r θ ρ Idx.θ lam * Γtot M r θ lam Idx.r a)) := by
      -- Direct approach: recognize this is just algebraic rearrangement
      simp only [sumIdx_map_sub, sumIdx_add_distrib]
      -- If simp doesn't handle it, use explicit rewrites:
      -- rw [sumIdx_add_distrib]  -- Σ(A - B + C) = Σ(A + (-B + C))
      -- rw [sumIdx_map_sub]      -- = Σ(A + (-B + C)) = ...
```

**Potential Issues**:

1. **Lemma availability**: Need both `sumIdx_map_sub` and `sumIdx_add_distrib`
   - These should be available after Task 1.1

2. **Associativity**: The expression has `A - B + C` which is parsed as `(A - B) + C`
   - May need `ring` to normalize before applying lemmas

3. **Congruence**: May need `congr` to focus on specific parts

**Estimated Time**: 15 minutes

**Dependencies**: Task 1.1 (sumIdx lemmas reorganized)

**Verification**: Expression should exactly match target with three separate `sumIdx` terms

---

### Step 5: Product Rule Backwards

**Goal**: Transform T₁ and T₂ using product rule: `g(∂Γ) = ∂(gΓ) - (∂g)Γ`

**Target Expression**:
```lean
  (dCoord Idx.r (fun r θ => sumIdx (fun ρ => g M β ρ r θ * Γtot M r θ ρ Idx.θ a)) r θ
 - sumIdx (fun ρ => dCoord Idx.r (fun r θ => g M β ρ r θ) r θ * Γtot M r θ ρ Idx.θ a))
- (dCoord Idx.θ (fun r θ => sumIdx (fun ρ => g M β ρ r θ * Γtot M r θ ρ Idx.r a)) r θ
 - sumIdx (fun ρ => dCoord Idx.θ (fun r θ => g M β ρ r θ) r θ * Γtot M r θ ρ Idx.r a))
+ [T₃ unchanged]
```

**Mathematical Meaning**:
- T₁ becomes: `∂_r(Σ_ρ g_{βρ}Γ^ρ_{θa}) - Σ_ρ (∂_r g_{βρ})Γ^ρ_{θa}` = ∂_r(Γ₁_{βaθ}) - D_r
- T₂ becomes: `∂_θ(Σ_ρ g_{βρ}Γ^ρ_{ra}) - Σ_ρ (∂_θ g_{βρ})Γ^ρ_{ra}` = ∂_θ(Γ₁_{βar}) - D_θ

Where D_r and D_θ are the metric derivative terms.

**Proof Tactics**:

```lean
    -- Step 5: Apply Product Rule Backwards. Introduces D terms.
    _ = (dCoord Idx.r (fun r θ => sumIdx (fun ρ => g M β ρ r θ * Γtot M r θ ρ Idx.θ a)) r θ
       - sumIdx (fun ρ => dCoord Idx.r (fun r θ => g M β ρ r θ) r θ * Γtot M r θ ρ Idx.θ a))
      - (dCoord Idx.θ (fun r θ => sumIdx (fun ρ => g M β ρ r θ * Γtot M r θ ρ Idx.r a)) r θ
       - sumIdx (fun ρ => dCoord Idx.θ (fun r θ => g M β ρ r θ) r θ * Γtot M r θ ρ Idx.r a))
      + sumIdx (fun ρ => g M β ρ r θ * sumIdx (fun lam =>
            Γtot M r θ ρ Idx.r lam * Γtot M r θ lam Idx.θ a
          - Γtot M r θ ρ Idx.θ lam * Γtot M r θ lam Idx.r a)) := by
      -- Apply the helper lemma from Task 2.1
      rw [prod_rule_backwards_sum M r θ h_ext β a Idx.r]   -- For T₁
      rw [prod_rule_backwards_sum M r θ h_ext β a Idx.θ]   -- For T₂
      -- The third term (T₃) is unchanged
```

**Challenges**:

1. **Lemma application**: The helper lemma must match exactly
   - Need to ensure index arguments align (β, a, Idx.r vs Idx.θ)

2. **Structure preservation**: T₃ term should remain completely unchanged

3. **Sign handling**: Note the outer subtraction: (A - B) - (C - D) + E
   - Must ensure this expands correctly: A - B - C + D + E

**Verification After Step 5**:

The expression should now have:
- Leading term: `∂_r(Σ_ρ g_{βρ}Γ^ρ_{θa})`
- D_r term: `- Σ_ρ (∂_r g_{βρ})Γ^ρ_{θa}`
- Middle term: `- ∂_θ(Σ_ρ g_{βρ}Γ^ρ_{ra})`
- D_θ term: `+ Σ_ρ (∂_θ g_{βρ})Γ^ρ_{ra}` (note sign!)
- T₃ term: `+ [ΓΓ terms unchanged]`

**Estimated Time**: 20 minutes (assuming helper lemma works)

**Dependencies**: Task 2.1 (`prod_rule_backwards_sum`)

---

### Step 6: Recognize Γ₁

**Goal**: Identify `Σ_ρ g_{βρ} Γ^ρ_{aμ}` as `Γ₁_{βaμ}` by definition

**Target Expression**:
```lean
  dCoord Idx.r (fun r θ => Γ₁ M r θ β a Idx.θ) r θ
- dCoord Idx.θ (fun r θ => Γ₁ M r θ β a Idx.r) r θ
- sumIdx (fun ρ => dCoord Idx.r (fun r θ => g M β ρ r θ) r θ * Γtot M r θ ρ Idx.θ a)
+ sumIdx (fun ρ => dCoord Idx.θ (fun r θ => g M β ρ r θ) r θ * Γtot M r θ ρ Idx.r a)
+ [T₃ unchanged]
```

**Mathematical Meaning**:
- First term: `∂_r Γ₁_{βaθ}` (recognized by Γ₁ definition)
- Second term: `∂_θ Γ₁_{βar}` (recognized by Γ₁ definition)
- D_r term: `- Σ_ρ (∂_r g_{βρ})Γ^ρ_{θa}`
- D_θ term: `+ Σ_ρ (∂_θ g_{βρ})Γ^ρ_{ra}`
- M terms: `+ [ΓΓ terms]`

**Proof Tactics**:

```lean
    -- Step 6: Recognize Γ₁ in the leading derivative terms.
    _ = dCoord Idx.r (fun r θ => Γ₁ M r θ β a Idx.θ) r θ
      - dCoord Idx.θ (fun r θ => Γ₁ M r θ β a Idx.r) r θ
      - sumIdx (fun ρ => dCoord Idx.r (fun r θ => g M β ρ r θ) r θ * Γtot M r θ ρ Idx.θ a)
      + sumIdx (fun ρ => dCoord Idx.θ (fun r θ => g M β ρ r θ) r θ * Γtot M r θ ρ Idx.r a)
      + sumIdx (fun ρ => g M β ρ r θ * sumIdx (fun lam =>
            Γtot M r θ ρ Idx.r lam * Γtot M r θ lam Idx.θ a
          - Γtot M r θ ρ Idx.θ lam * Γtot M r θ lam Idx.r a)) := by
      -- Unfold Γ₁ definition to recognize the pattern
      simp only [Γ₁]
      -- After unfolding, the structures should match
      -- May need to normalize the algebraic structure
      -- Note: (A - B) - (C - D) + E = A - C - B + D + E
      abel_nf  -- Normalize associativity/commutativity of addition
```

**Alternative Approach** (if simp doesn't work):

```lean
    _ = dCoord Idx.r (fun r θ => Γ₁ M r θ β a Idx.θ) r θ
      - dCoord Idx.θ (fun r θ => Γ₁ M r θ β a Idx.r) r θ
      - sumIdx (fun ρ => dCoord Idx.r (fun r θ => g M β ρ r θ) r θ * Γtot M r θ ρ Idx.θ a)
      + sumIdx (fun ρ => dCoord Idx.θ (fun r θ => g M β ρ r θ) r θ * Γtot M r θ ρ Idx.r a)
      + sumIdx (fun ρ => g M β ρ r θ * sumIdx (fun lam =>
            Γtot M r θ ρ Idx.r lam * Γtot M r θ lam Idx.θ a
          - Γtot M r θ ρ Idx.θ lam * Γtot M r θ lam Idx.r a)) := by
      -- Explicit recognition using congruence
      congr 2  -- Focus on first two terms
      · -- First term: ∂_r(Σ g Γ) = ∂_r(Γ₁)
        unfold Γ₁
        rfl  -- Should be definitional
      · -- Second term: ∂_θ(Σ g Γ) = ∂_θ(Γ₁)
        unfold Γ₁
        rfl  -- Should be definitional
```

**Challenges**:

1. **Definitional equality**: Γ₁ is defined as `sumIdx (fun ρ => g M β ρ r θ * Γtot M r θ ρ a μ)`
   - The pattern `Σ_ρ g_{βρ} Γ^ρ_{θa}` should match exactly
   - Should be `rfl` after unfolding

2. **Sign normalization**: The expression (A - B) - (C - D) + E needs careful handling
   - `abel_nf` should handle associativity/commutativity
   - May need explicit `ring` if structure is complex

**Estimated Time**: 15 minutes

**Dependencies**: Γ₁ definition (already exists)

**Verification**: Check that first two terms are exactly `∂_r Γ₁_{βaθ}` and `∂_θ Γ₁_{βar}`

---

### Step 7: Metric Compatibility Expansion

**Goal**: Expand `∂g` terms using metric compatibility: `∂_μ g_{βρ} = Σ_σ (Γ^σ_{μβ} g_{σρ} + Γ^σ_{μρ} g_{βσ})`

**Target Expression**:
```lean
  dCoord Idx.r (fun r θ => Γ₁ M r θ β a Idx.θ) r θ
- dCoord Idx.θ (fun r θ => Γ₁ M r θ β a Idx.r) r θ
- sumIdx (fun ρ =>
    (sumIdx (fun σ => Γtot M r θ σ Idx.r β * g M σ ρ r θ)
   + sumIdx (fun σ => Γtot M r θ σ Idx.r ρ * g M β σ r θ))
    * Γtot M r θ ρ Idx.θ a)
+ sumIdx (fun ρ =>
    (sumIdx (fun σ => Γtot M r θ σ Idx.θ β * g M σ ρ r θ)
   + sumIdx (fun σ => Γtot M r θ σ Idx.θ ρ * g M β σ r θ))
    * Γtot M r θ ρ Idx.r a)
+ [T₃ unchanged]
```

**Mathematical Meaning**:
- ∂Γ₁ terms unchanged
- D_r expanded: `- Σ_ρ (∂_r g_{βρ})Γ^ρ_{θa}` becomes `- Σ_ρ [Σ_σ (Γ^σ_{rβ}g_{σρ} + Γ^σ_{rρ}g_{βσ})] Γ^ρ_{θa}`
  - This is `- Σ_ρ (D_r1 + D_r2) Γ^ρ_{θa}` where:
    - D_r1 = `Σ_σ Γ^σ_{rβ}g_{σρ}` (depends on β index)
    - D_r2 = `Σ_σ Γ^σ_{rρ}g_{βσ}` (depends on ρ index)
- D_θ expanded: similarly for θ
- M terms unchanged

**Proof Tactics**:

```lean
    -- Step 7: Expand D terms using Metric Compatibility (∇g=0).
    _ = dCoord Idx.r (fun r θ => Γ₁ M r θ β a Idx.θ) r θ
      - dCoord Idx.θ (fun r θ => Γ₁ M r θ β a Idx.r) r θ
      - sumIdx (fun ρ =>
          (sumIdx (fun σ => Γtot M r θ σ Idx.r β * g M σ ρ r θ)
         + sumIdx (fun σ => Γtot M r θ σ Idx.r ρ * g M β σ r θ))
          * Γtot M r θ ρ Idx.θ a)
      + sumIdx (fun ρ =>
          (sumIdx (fun σ => Γtot M r θ σ Idx.θ β * g M σ ρ r θ)
         + sumIdx (fun σ => Γtot M r θ σ Idx.θ ρ * g M β σ r θ))
          * Γtot M r θ ρ Idx.r a)
      + sumIdx (fun ρ => g M β ρ r θ * sumIdx (fun lam =>
            Γtot M r θ ρ Idx.r lam * Γtot M r θ lam Idx.θ a
          - Γtot M r θ ρ Idx.θ lam * Γtot M r θ lam Idx.r a)) := by
      -- Apply metric compatibility inside the D terms
      -- The D_r term has structure: Σ_ρ (∂_r g_{βρ}) Γ^ρ_{θa}
      -- We need to replace ∂_r g_{βρ} with Σ_σ (Γ^σ_{rβ}g_{σρ} + Γ^σ_{rρ}g_{βσ})

      -- Use simp_rw to apply the rewrite under binders
      simp_rw [dCoord_g_via_compat_ext M r θ h_ext]
      -- This should automatically expand both D_r and D_θ terms
```

**Alternative Approach** (more explicit):

```lean
      -- Manual approach: focus on each D term separately
      congr 3  -- Focus on the third term (D_r)
      · -- Expand D_r
        funext ρ
        rw [dCoord_g_via_compat_ext M r θ h_ext β ρ Idx.r]
        ring  -- Normalize structure

      -- Similar for D_θ (fourth term)
      congr 1  -- Move to fourth term
      funext ρ
      rw [dCoord_g_via_compat_ext M r θ h_ext β ρ Idx.θ]
      ring
```

**Challenges**:

1. **Navigating structure**: The `∂g` terms are buried inside the sum
   - `simp_rw` applies rewrites under all binders
   - May need explicit `congr` + `funext` to navigate

2. **Correct arguments**: `dCoord_g_via_compat_ext` takes arguments (M, r, θ, h_ext, α, β, μ)
   - For D_r: α=β, β=ρ, μ=Idx.r
   - For D_θ: α=β, β=ρ, μ=Idx.θ

3. **Structure matching**: After expansion, verify the nested sums match target exactly

**Verification**:

After Step 7, we should have:
- 2 terms: `∂_r Γ₁_{βaθ} - ∂_θ Γ₁_{βar}` (∂Γ₁ terms - survive to RHS)
- 4 terms from D_r expansion: `- Σ_ρ [Σ_σ (Γ^σ_{rβ}g_{σρ}·Γ^ρ_{θa}) + Σ_σ (Γ^σ_{rρ}g_{βσ}·Γ^ρ_{θa})]`
- 4 terms from D_θ expansion: `+ Σ_ρ [Σ_σ (Γ^σ_{θβ}g_{σρ}·Γ^ρ_{ra}) + Σ_σ (Γ^σ_{θρ}g_{βσ}·Γ^ρ_{ra})]`
- 4 terms from M expansion: `+ Σ_ρ g_{βρ} [Σ_λ (Γ^ρ_{rλ}Γ^λ_{θa}) - Σ_λ (Γ^ρ_{θλ}Γ^λ_{ra})]`

Total: 2 + 4 + 4 + 4 = **14 terms** before simplification

After distributing the multiplications and separating sums:
- 2 ∂Γ₁ terms
- 12 ΓΓg terms (which will undergo cancellations in Step 8)

This is the "∂Γ₁ + M - D" state mentioned by SP.

**Estimated Time**: 30 minutes

**Dependencies**: Task 1.3 (`dCoord_g_via_compat_ext`)

---

### Steps 4-7 Summary

**Total Time**: 80 minutes (~1.5 hours)

**Deliverables**:
- ✅ Step 4: Three separate sums (T₁, T₂, T₃)
- ✅ Step 5: Product rule applied, D terms introduced
- ✅ Step 6: Γ₁ recognized in ∂Γ terms
- ✅ Step 7: Metric compatibility expanded, full 12-term structure

**Current State After Step 7**:
Expression is in "∂Γ₁ + M - D" form with 2 + 12 = 14 terms total.

**Build Verification**:
After Steps 4-7, run:
```bash
lake build Papers.P5_GeneralRelativity.GR.Riemann
```
Must pass with 0 errors before proceeding to Step 8.

---

## Part IV: Step 8 Auxiliary Lemmas (8A-8D)

### Overview

Step 8 implements the "algebraic miracle": **M - D = -T2**

After Step 7, we have 12 ΓΓg terms:
- **M terms** (4): From RiemannUp double sum
  - M_r (2 terms): `Σ_ρ g_{βρ} Σ_λ Γ^ρ_{rλ}Γ^λ_{θa}`
  - M_θ (2 terms): `Σ_ρ g_{βρ} Σ_λ Γ^ρ_{θλ}Γ^λ_{ra}`

- **D terms** (8): From metric compatibility expansion
  - D_r (4 terms): From `∂_r g_{βρ}` expansion
    - D_r1 (2 terms): `Σ_ρ Σ_σ Γ^σ_{rβ}g_{σρ}·Γ^ρ_{θa}`
    - D_r2 (2 terms): `Σ_ρ Σ_σ Γ^σ_{rρ}g_{βσ}·Γ^ρ_{θa}`
  - D_θ (4 terms): From `∂_θ g_{βρ}` expansion
    - D_θ1 (2 terms): `Σ_ρ Σ_σ Γ^σ_{θβ}g_{σρ}·Γ^ρ_{ra}`
    - D_θ2 (2 terms): `Σ_ρ Σ_σ Γ^σ_{θρ}g_{βσ}·Γ^ρ_{ra}`

The "miracle" happens through:
1. **Cancellations**: M_r = D_r2, M_θ = D_θ2 (via Fubini + relabeling)
2. **Identifications**: D_r1 = T2_r, D_θ1 = T2_θ (via Fubini + symmetries + Γ₁ recognition)

Therefore: M - D = (M_r - M_θ) - ((D_r1 + D_r2) - (D_θ1 + D_θ2))
                 = (M_r - D_r2) - D_r1 - (M_θ - D_θ2) + D_θ1
                 = 0 - T2_r - 0 + T2_θ
                 = -T2

---

### Lemma 8A: Cancellation M_r = D_r2

**Purpose**: Prove that M_r term equals D_r2 term via Fubini and index relabeling

**Mathematical Content**:

M_r: `Σ_ρ g_{βρ} Σ_λ (Γ^ρ_{rλ}Γ^λ_{θa})`

After distributing g_{βρ} inside:
`Σ_ρ Σ_λ (g_{βρ}·Γ^ρ_{rλ}·Γ^λ_{θa})`

Apply Fubini (swap ρ,λ):
`Σ_λ Σ_ρ (g_{βρ}·Γ^ρ_{rλ}·Γ^λ_{θa})`

Relabel indices (λ→σ, ρ→ρ):
`Σ_σ Σ_ρ (g_{βρ}·Γ^ρ_{rσ}·Γ^σ_{θa})`

Rearrange factors using commutativity:
`Σ_σ Σ_ρ (Γ^σ_{rρ}·g_{βσ}... wait, this doesn't match`

Actually, let me reconsider. D_r2 is:
`Σ_ρ Σ_σ (Γ^σ_{rρ}·g_{βσ}·Γ^ρ_{θa})`

Apply Fubini to D_r2 (swap ρ,σ):
`Σ_σ Σ_ρ (Γ^σ_{rρ}·g_{βσ}·Γ^ρ_{θa})`

For M_r after distributing and swapping:
`Σ_λ Σ_ρ (g_{βρ}·Γ^ρ_{rλ}·Γ^λ_{θa})`

Relabel M_r (λ→σ, ρ→ρ):
`Σ_σ Σ_ρ (g_{βρ}·Γ^ρ_{rσ}·Γ^σ_{θa})`

Hmm, still not matching. Let me check SP's guidance more carefully.

**From SP Memo**:
- M_r: Σρ gᵦρ Σλ (Γ^ρ_{rλ} Γ^λ_{θa})
- D_r₂: Σρ (Σσ Γ^σ_{rρ} gᵦσ) Γ^ρ_{θa}

Let me expand both carefully:

M_r = Σρ gᵦρ Σλ (Γ^ρ_{rλ} Γ^λ_{θa})
    = Σρ Σλ (gᵦρ · Γ^ρ_{rλ} · Γ^λ_{θa})  [distribute]

D_r₂ = Σρ (Σσ Γ^σ_{rρ} gᵦσ) Γ^ρ_{θa}
     = Σρ Σσ ((Γ^σ_{rρ} · gᵦσ) · Γ^ρ_{θa})  [distribute]

To see they're equal:
1. Apply Fubini to M_r: Σρ Σλ → Σλ Σρ
   M_r = Σλ Σρ (gᵦρ · Γ^ρ_{rλ} · Γ^λ_{θa})

2. Rename λ→σ in M_r:
   M_r = Σσ Σρ (gᵦρ · Γ^ρ_{rσ} · Γ^σ_{θa})

3. Apply Fubini to D_r₂: Σρ Σσ → Σσ Σρ
   D_r₂ = Σσ Σρ (Γ^σ_{rρ} · gᵦσ · Γ^ρ_{θa})

4. Compare (both are Σσ Σρ):
   M_r:  gᵦρ · Γ^ρ_{rσ} · Γ^σ_{θa}
   D_r₂: Γ^σ_{rρ} · gᵦσ · Γ^ρ_{θa}

These don't look equal... unless there's some relationship I'm missing.

Wait - let me recheck the metric compatibility expansion. From Step 7:
∂_r g_{βρ} = Σ_σ (Γ^σ_{rβ}g_{σρ} + Γ^σ_{rρ}g_{βσ})

So D_r has two parts:
- D_r1: Σρ Σσ (Γ^σ_{rβ} · g_{σρ}) · Γ^ρ_{θa}
- D_r2: Σρ Σσ (Γ^σ_{rρ} · g_{βσ}) · Γ^ρ_{θa}

Ah! So D_r2 has g_{βσ} not g_{βρ}.

Let me redo:
M_r = Σρ Σλ (g_{βρ} · Γ^ρ_{rλ} · Γ^λ_{θa})

Rename ρ→σ:
M_r = Σσ Σλ (g_{βσ} · Γ^σ_{rλ} · Γ^λ_{θa})

Rename λ→ρ:
M_r = Σσ Σρ (g_{βσ} · Γ^σ_{rρ} · Γ^ρ_{θa})

D_r2 = Σρ Σσ (Γ^σ_{rρ} · g_{βσ} · Γ^ρ_{θa})

Apply Fubini to D_r2 (swap ρ,σ):
D_r2 = Σσ Σρ (Γ^σ_{rρ} · g_{βσ} · Γ^ρ_{θa})

Now compare (both Σσ Σρ):
M_r:  g_{βσ} · Γ^σ_{rρ} · Γ^ρ_{θa}
D_r2: Γ^σ_{rρ} · g_{βσ} · Γ^ρ_{θa}

These are equal by commutativity of multiplication! ✓

**Statement**:

```lean
/-- Step 8A: Cancellation Mᵣ = Dᵣ₂. (General metric)

    This shows that the "mixed" ΓΓ terms from RiemannUp (M_r) exactly cancel
    with one component of the metric derivative terms (D_r2).

    The proof uses:
    1. Fubini theorem (sumIdx_swap) to reorder nested sums
    2. Alpha-equivalence (index relabeling)
    3. Commutativity of multiplication
-/
lemma Riemann_via_Γ₁_Cancel_r (M r θ : ℝ) (β a : Idx) :
  -- Mᵣ: Σρ gᵦρ Σλ (Γ^ρ_{rλ} Γ^λ_{θa})
  sumIdx (fun ρ => g M β ρ r θ * sumIdx (fun λ =>
      Γtot M r θ ρ Idx.r λ * Γtot M r θ λ Idx.θ a))
  =
  -- Dᵣ₂: Σρ (Σσ Γ^σ_{rρ} gᵦσ) Γ^ρ_{θa}
  sumIdx (fun ρ => sumIdx (fun σ =>
    Γtot M r θ σ Idx.r ρ * g M β σ r θ)
    * Γtot M r θ ρ Idx.θ a)
```

**Proof**:

```lean
lemma Riemann_via_Γ₁_Cancel_r (M r θ : ℝ) (β a : Idx) :
  sumIdx (fun ρ => g M β ρ r θ * sumIdx (fun λ =>
      Γtot M r θ ρ Idx.r λ * Γtot M r θ λ Idx.θ a))
  =
  sumIdx (fun ρ => sumIdx (fun σ =>
    Γtot M r θ σ Idx.r ρ * g M β σ r θ)
    * Γtot M r θ ρ Idx.θ a) := by
  classical

  -- LHS: Mᵣ = Σρ gᵦρ Σλ (Γ^ρ_{rλ} Γ^λ_{θa})

  -- Step 1: Distribute g_{βρ} inside the inner sum
  simp_rw [← mul_sumIdx]  -- Pulls g_{βρ} inside
  -- Now: Σρ Σλ (g_{βρ} · Γ^ρ_{rλ} · Γ^λ_{θa})

  -- Step 2: Apply Fubini (swap ρ, λ)
  rw [sumIdx_swap]
  -- Now: Σλ Σρ (g_{βρ} · Γ^ρ_{rλ} · Γ^λ_{θa})

  -- Step 3: Relabel indices (λ→σ, ρ→ρ is just α-equivalence)
  -- After relabeling: Σσ Σρ (g_{βρ} · Γ^ρ_{rσ} · Γ^σ_{θa})
  -- But we want ρ→λ relabeling
  -- Let me reconsider the relabeling...

  -- Actually, we want: λ→σ, then ρ→new ρ
  -- Σλ Σρ (g_{βρ} · Γ^ρ_{rλ} · Γ^λ_{θa})
  -- Rename λ to σ: Σσ Σρ (g_{βρ} · Γ^ρ_{rσ} · Γ^σ_{θa})

  -- But we want g_{βσ} not g_{βρ}. So we need to rename ρ→σ first, THEN λ→ρ.

  -- Let me restart with correct relabeling:
  -- LHS after Step 2: Σλ Σρ (g_{βρ} · Γ^ρ_{rλ} · Γ^λ_{θa})

  -- Relabel: ρ→σ, λ→ρ
  -- Becomes: Σρ Σσ (g_{βσ} · Γ^σ_{rρ} · Γ^ρ_{θa})

  -- But sumIdx doesn't care about variable names, so this is automatic.
  -- Actually, we need to explicitly show the correspondence.

  -- Alternative: just show the inner sums match pointwise
  apply sumIdx_congr; intro i
  apply sumIdx_congr; intro j
  -- After relabeling, need to show:
  -- g_{βρ} · Γ^ρ_{rλ} · Γ^λ_{θa} = Γ^σ_{rρ} · g_{βσ} · Γ^ρ_{θa}
  -- where we've swapped ρ↔λ and renamed
  ring  -- Commutativity of multiplication
```

**Simpler Proof** (Using SP's suggested approach):

```lean
lemma Riemann_via_Γ₁_Cancel_r (M r θ : ℝ) (β a : Idx) :
  sumIdx (fun ρ => g M β ρ r θ * sumIdx (fun λ =>
      Γtot M r θ ρ Idx.r λ * Γtot M r θ λ Idx.θ a))
  =
  sumIdx (fun ρ => sumIdx (fun σ =>
    Γtot M r θ σ Idx.r ρ * g M β σ r θ)
    * Γtot M r θ ρ Idx.θ a) := by
  classical

  -- Step 1: Normalize Mᵣ. Distribute gᵦρ inside.
  simp_rw [mul_sumIdx]
  -- Now: Σρ Σλ (gᵦρ · Γ^ρ_{rλ} · Γ^λ_{θa})

  -- Step 2: Apply Fubini to Mᵣ: ΣρΣλ → ΣλΣρ
  rw [sumIdx_swap]
  -- Now: Σλ Σρ (gᵦρ · Γ^ρ_{rλ} · Γ^λ_{θa})

  -- Step 3: Normalize Dᵣ₂. Distribute Γ^ρ_{θa} inside.
  conv_rhs => {
    arg 1; ext ρ
    rw [sumIdx_mul]
  }
  -- Now RHS: Σρ Σσ (Γ^σ_{rρ} · gᵦσ · Γ^ρ_{θa})

  -- Step 4: Apply Fubini to Dᵣ₂: ΣρΣσ → ΣσΣρ
  conv_rhs => rw [sumIdx_swap]
  -- Now RHS: Σσ Σρ (Γ^σ_{rρ} · gᵦσ · Γ^ρ_{θa})

  -- Step 5: Compare. The terms are identical up to renaming (λ↔σ) and commutativity.
  apply sumIdx_congr; intro i
  apply sumIdx_congr; intro j
  ring  -- Handles variable renaming and commutativity
```

**Estimated Time**: 30 minutes

**Dependencies**:
- `sumIdx_swap` (Fubini)
- `mul_sumIdx` (distribution)
- `sumIdx_mul` (another distribution form)

---

### Lemma 8B: Cancellation M_θ = D_θ2

**Purpose**: Identical to 8A, but for θ coordinate

**Statement**:

```lean
/-- Step 8B: Cancellation M_θ = D_θ2. (General metric) -/
lemma Riemann_via_Γ₁_Cancel_θ (M r θ : ℝ) (β a : Idx) :
  -- M_θ: Σρ gᵦρ Σλ (Γ^ρ_{θλ} Γ^λ_{ra})
  sumIdx (fun ρ => g M β ρ r θ * sumIdx (fun λ =>
      Γtot M r θ ρ Idx.θ λ * Γtot M r θ λ Idx.r a))
  =
  -- D_θ2: Σρ (Σσ Γ^σ_{θρ} gᵦσ) Γ^ρ_{ra}
  sumIdx (fun ρ => sumIdx (fun σ =>
    Γtot M r θ σ Idx.θ ρ * g M β σ r θ)
    * Γtot M r θ ρ Idx.r a)
```

**Proof**: Identical to 8A, just replace Idx.r → Idx.θ and Idx.θ → Idx.r

**Estimated Time**: 15 minutes (copy and adapt from 8A)

---

### Lemma 8C: Identification D_r1 = T2_r

**Purpose**: Show that D_r1 equals T2_r via Fubini, symmetries, and Γ₁ recognition

**Mathematical Content**:

D_r1: `Σρ Σσ (Γ^σ_{rβ} · g_{σρ} · Γ^ρ_{θa})`

Apply Fubini (swap ρ,σ):
`Σσ Σρ (Γ^σ_{rβ} · g_{σρ} · Γ^ρ_{θa})`

Apply symmetries:
- Γ^σ_{rβ} = Γ^σ_{βr} (torsion-free)
- Γ^ρ_{θa} = Γ^ρ_{aθ} (torsion-free)
- g_{σρ} = g_{ρσ} (metric symmetric)

Becomes:
`Σσ Σρ (Γ^σ_{βr} · g_{ρσ} · Γ^ρ_{aθ})`

Rearrange:
`Σσ Σρ (g_{ρσ} · Γ^ρ_{aθ} · Γ^σ_{βr})`

Recognize Γ₁: `Σρ g_{ρσ} · Γ^ρ_{aθ} = Γ₁_{σaθ}`

Becomes:
`Σσ (Γ₁_{σaθ} · Γ^σ_{βr})`

Relabel σ→λ:
`Σλ (Γ₁_{λaθ} · Γ^λ_{βr})` = T2_r ✓

**Statement**:

```lean
/-- Step 8C: Identification Dᵣ₁ = T2ᵣ. (General metric)

    This shows that one component of the metric derivative terms (D_r1)
    equals the T2_r term (part of the covariant ΓΓ commutator).

    The proof uses:
    1. Fubini theorem to reorder sums
    2. Symmetries (Γtot_symm, g_symm)
    3. Recognition of Γ₁ definition
-/
lemma Riemann_via_Γ₁_Identify_r (M r θ : ℝ) (β a : Idx) :
  -- Dᵣ₁: Σρ (Σσ Γ^σ_{rβ} gσρ) Γ^ρ_{θa}
  sumIdx (fun ρ => sumIdx (fun σ =>
      Γtot M r θ σ Idx.r β * g M σ ρ r θ)
    * Γtot M r θ ρ Idx.θ a)
  =
  -- T2ᵣ: Σλ (Γ_{λaθ} Γ^λ_{βr})
  sumIdx (fun λ =>
      Γ₁ M r θ λ a Idx.θ * Γtot M r θ λ β Idx.r)
```

**Proof**:

```lean
lemma Riemann_via_Γ₁_Identify_r (M r θ : ℝ) (β a : Idx) :
  sumIdx (fun ρ => sumIdx (fun σ =>
      Γtot M r θ σ Idx.r β * g M σ ρ r θ)
    * Γtot M r θ ρ Idx.θ a)
  =
  sumIdx (fun λ =>
      Γ₁ M r θ λ a Idx.θ * Γtot M r θ λ β Idx.r) := by
  classical
  unfold Γ₁  -- Expand RHS to see the sum structure

  -- LHS: Σρ (Σσ Γ^σ_{rβ} · gσρ) · Γ^ρ_{θa}

  -- Step 1: Normalize Dᵣ₁. Distribute Γ^ρ_{θa} inside.
  simp_rw [sumIdx_mul]
  -- Now: Σρ Σσ (Γ^σ_{rβ} · gσρ · Γ^ρ_{θa})

  -- Step 2: Apply Fubini to Dᵣ₁: ΣρΣσ → ΣσΣρ
  rw [sumIdx_swap]
  -- Now: Σσ Σρ (Γ^σ_{rβ} · gσρ · Γ^ρ_{θa})

  -- Step 3: Apply Symmetries
  simp_rw [Γtot_symm M r θ]  -- Γ^σ_{rβ}=Γ^σ_{βr}, Γ^ρ_{θa}=Γ^ρ_{aθ}
  simp_rw [g_symm M]          -- gσρ = gρσ
  -- Now: Σσ Σρ (Γ^σ_{βr} · gρσ · Γ^ρ_{aθ})

  -- Step 4: Rearrange factors (commutativity)
  conv_lhs => {
    arg 1; ext σ
    arg 1; ext ρ
    rw [mul_comm (Γtot M r θ σ β Idx.r), mul_assoc, mul_comm (Γtot M r θ ρ a Idx.θ)]
  }
  -- Now: Σσ Σρ (gρσ · Γ^ρ_{aθ} · Γ^σ_{βr})

  -- Step 5: Pull Γ^σ_{βr} out of inner sum (it doesn't depend on ρ)
  simp_rw [← mul_sumIdx]
  -- Now: Σσ [(Σρ gρσ · Γ^ρ_{aθ}) · Γ^σ_{βr}]

  -- Step 6: The inner sum Σρ gρσ · Γ^ρ_{aθ} is exactly Γ₁_{σaθ} by definition
  -- But RHS has Γ₁ M r θ λ a Idx.θ = Σρ g M λ ρ r θ * Γtot M r θ ρ a Idx.θ
  -- We have:      Σρ g M ρ σ r θ * Γtot M r θ ρ a Idx.θ
  -- These match after applying g_symm: g M ρ σ = g M σ ρ = g M λ ρ (when σ=λ)

  -- Actually, let me use the unfolded definition:
  -- RHS (after unfold Γ₁): Σλ (Σρ g M λ ρ r θ * Γtot M r θ ρ a Idx.θ) * Γtot M r θ λ β Idx.r

  -- Compare with LHS: Σσ (Σρ g M ρ σ r θ * Γtot M r θ ρ a Idx.θ) * Γtot M r θ σ β Idx.r

  -- Need to show: g M ρ σ = g M λ ρ when σ=λ
  -- Apply g_symm: g M ρ σ = g M σ ρ = g M λ ρ ✓

  -- Step 7: Apply sumIdx_congr to compare structures
  apply sumIdx_congr; intro i
  congr 1
  apply sumIdx_congr; intro j
  ring  -- g M j i = g M i j by g_symm, already applied via simp_rw
```

**Simplified Proof** (using SP's approach):

```lean
lemma Riemann_via_Γ₁_Identify_r (M r θ : ℝ) (β a : Idx) :
  sumIdx (fun ρ => sumIdx (fun σ =>
      Γtot M r θ σ Idx.r β * g M σ ρ r θ)
    * Γtot M r θ ρ Idx.θ a)
  =
  sumIdx (fun λ =>
      Γ₁ M r θ λ a Idx.θ * Γtot M r θ λ β Idx.r) := by
  classical
  unfold Γ₁

  -- Step 1: Normalize Dᵣ₁. Distribute Γ^ρ_{θa} inside.
  simp_rw [sumIdx_mul]

  -- Step 2: Apply Fubini to Dᵣ₁: ΣρΣσ → ΣσΣρ
  rw [sumIdx_swap]

  -- Step 3: Apply Symmetries
  simp_rw [Γtot_symm M r θ, g_symm M]

  -- Step 4: Normalize T2ᵣ. Distribute Γ^λ_{βr} inside.
  conv_rhs => {
    arg 1; ext λ
    rw [mul_sumIdx]
  }

  -- Step 5: Compare. Structures match after renaming (λ↔σ) and reorganization.
  apply sumIdx_congr; intro i
  apply sumIdx_congr; intro j
  ring
```

**Estimated Time**: 45 minutes

**Dependencies**:
- `Γtot_symm` (Task 1.2)
- `g_symm` (Task 1.2)
- `sumIdx_swap` (Fubini)
- `mul_sumIdx`, `sumIdx_mul` (distribution)

---

### Lemma 8D: Identification D_θ1 = T2_θ

**Purpose**: Identical to 8C, but for θ coordinate

**Statement**:

```lean
/-- Step 8D: Identification D_θ1 = T2_θ. (General metric) -/
lemma Riemann_via_Γ₁_Identify_θ (M r θ : ℝ) (β a : Idx) :
  -- D_θ1: Σρ (Σσ Γ^σ_{θβ} gσρ) Γ^ρ_{ra}
  sumIdx (fun ρ => sumIdx (fun σ =>
      Γtot M r θ σ Idx.θ β * g M σ ρ r θ)
    * Γtot M r θ ρ Idx.r a)
  =
  -- T2_θ: Σλ (Γ_{λar} Γ^λ_{βθ})
  sumIdx (fun λ =>
      Γ₁ M r θ λ a Idx.r * Γtot M r θ λ β Idx.θ)
```

**Proof**: Identical to 8C, just replace Idx.r → Idx.θ and Idx.θ → Idx.r

**Estimated Time**: 20 minutes (copy and adapt from 8C)

---

### Step 8 Lemmas Summary

**Total Time**: 110 minutes (~2 hours)

**Deliverables**:
- ✅ Lemma 8A: M_r = D_r2 (proven)
- ✅ Lemma 8B: M_θ = D_θ2 (proven)
- ✅ Lemma 8C: D_r1 = T2_r (proven)
- ✅ Lemma 8D: D_θ1 = T2_θ (proven)

**Location**: Define these before `Riemann_via_Γ₁` in a dedicated section:
```lean
/-! ### Step 8 Auxiliary Lemmas: The Algebraic Miracle -/
```

**Build Verification**:
After proving 8A-8D, run:
```bash
lake build Papers.P5_GeneralRelativity.GR.Riemann
```
Must pass with 0 errors before proceeding to Step 8 assembly.

---

## Part V: Step 8 Assembly

### Goal

Integrate lemmas 8A-8D into the main `calc` proof to complete Step 8.

### Current State (After Step 7)

Expression has structure:
```
∂Γ₁_r - ∂Γ₁_θ - D_r + D_θ + M
```

Where:
- D_r = D_r1 + D_r2
- D_θ = D_θ1 + D_θ2
- M = M_r - M_θ

Expanding:
```
∂Γ₁_r - ∂Γ₁_θ - (D_r1 + D_r2) + (D_θ1 + D_θ2) + (M_r - M_θ)
```

### Target (After Step 8)

```lean
  dCoord Idx.r (fun r θ => Γ₁ M r θ β a Idx.θ) r θ
- dCoord Idx.θ (fun r θ => Γ₁ M r θ β a Idx.r) r θ
+ sumIdx (fun λ =>
    Γ₁ M r θ λ a Idx.r * Γtot M r θ λ β Idx.θ)   -- +T2_θ
- sumIdx (fun λ =>
    Γ₁ M r θ λ a Idx.θ * Γtot M r θ λ β Idx.r)   -- -T2_r
```

### Mathematical Transformation

We need to show:
```
- (D_r1 + D_r2) + (D_θ1 + D_θ2) + (M_r - M_θ) = +T2_θ - T2_r
```

Apply lemmas:
- M_r = D_r2 (Lemma 8A)
- M_θ = D_θ2 (Lemma 8B)
- D_r1 = T2_r (Lemma 8C)
- D_θ1 = T2_θ (Lemma 8D)

Substitute:
```
- (D_r1 + D_r2) + (D_θ1 + D_θ2) + (M_r - M_θ)
= - D_r1 - D_r2 + D_θ1 + D_θ2 + M_r - M_θ
= - D_r1 - M_r + D_θ1 + M_θ + M_r - M_θ   [using D_r2=M_r, D_θ2=M_θ]
= - D_r1 + D_θ1                             [M_r cancels, M_θ cancels]
= - T2_r + T2_θ                             [using D_r1=T2_r, D_θ1=T2_θ]
```

Perfect! ✓

### Proof Structure

**Option 1: Direct Application** (if expression structure matches lemmas exactly)

```lean
    -- Step 8: The Algebraic Miracle (M - D = -T2).
    _ = dCoord Idx.r (fun r θ => Γ₁ M r θ β a Idx.θ) r θ
      - dCoord Idx.θ (fun r θ => Γ₁ M r θ β a Idx.r) r θ
      + sumIdx (fun λ => Γ₁ M r θ λ a Idx.r * Γtot M r θ λ β Idx.θ)   -- +T2_θ
      - sumIdx (fun λ => Γ₁ M r θ λ a Idx.θ * Γtot M r θ λ β Idx.r)   -- -T2_r
      := by
      -- The expression from Step 7 has:
      -- ∂Γ₁_r - ∂Γ₁_θ - (D_r1 + D_r2) + (D_θ1 + D_θ2) + (M_r - M_θ)

      -- Step 8.1: Apply Cancellations (M = D2)
      rw [Riemann_via_Γ₁_Cancel_r M r θ β a]   -- Replaces M_r with D_r2
      rw [Riemann_via_Γ₁_Cancel_θ M r θ β a]   -- Replaces M_θ with D_θ2

      -- After cancellations: ∂Γ₁_r - ∂Γ₁_θ - D_r1 + D_θ1
      -- (The D_r2 and M_r cancel, D_θ2 and M_θ cancel)

      -- Step 8.2: Apply Identifications (D1 = T2)
      rw [Riemann_via_Γ₁_Identify_r M r θ β a]   -- Replaces D_r1 with T2_r
      rw [Riemann_via_Γ₁_Identify_θ M r θ β a]   -- Replaces D_θ1 with T2_θ

      -- After identifications: ∂Γ₁_r - ∂Γ₁_θ - T2_r + T2_θ

      -- Step 8.3: Normalize
      ring_nf  -- or abel_nf if needed
```

**Option 2: Explicit Intermediate States** (if navigation is needed)

```lean
    -- Step 8: The Algebraic Miracle.
    _ = dCoord Idx.r (fun r θ => Γ₁ M r θ β a Idx.θ) r θ
      - dCoord Idx.θ (fun r θ => Γ₁ M r θ β a Idx.r) r θ
      + sumIdx (fun λ => Γ₁ M r θ λ a Idx.r * Γtot M r θ λ β Idx.θ)
      - sumIdx (fun λ => Γ₁ M r θ λ a Idx.θ * Γtot M r θ λ β Idx.r)
      := by
      -- Current state after Step 7:
      -- ∂Γ₁_r - ∂Γ₁_θ - Σρ[(Σσ Γ^σ_{rβ}g_{σρ})·Γ^ρ_{θa} + (Σσ Γ^σ_{rρ}g_{βσ})·Γ^ρ_{θa}]
      --                + Σρ[(Σσ Γ^σ_{θβ}g_{σρ})·Γ^ρ_{ra} + (Σσ Γ^σ_{θρ}g_{βσ})·Γ^ρ_{ra}]
      --                + Σρ g_{βρ}[Σλ Γ^ρ_{rλ}Γ^λ_{θa} - Σλ Γ^ρ_{θλ}Γ^λ_{ra}]

      -- Let me denote:
      -- A₁ = Σρ(Σσ Γ^σ_{rβ}g_{σρ})·Γ^ρ_{θa}  (D_r1)
      -- A₂ = Σρ(Σσ Γ^σ_{rρ}g_{βσ})·Γ^ρ_{θa}  (D_r2)
      -- B₁ = Σρ(Σσ Γ^σ_{θβ}g_{σρ})·Γ^ρ_{ra}  (D_θ1)
      -- B₂ = Σρ(Σσ Γ^σ_{θρ}g_{βσ})·Γ^ρ_{ra}  (D_θ2)
      -- C₁ = Σρ g_{βρ} Σλ Γ^ρ_{rλ}Γ^λ_{θa}   (M_r)
      -- C₂ = Σρ g_{βρ} Σλ Γ^ρ_{θλ}Γ^λ_{ra}   (M_θ)

      -- Current: ∂Γ₁_r - ∂Γ₁_θ - A₁ - A₂ + B₁ + B₂ + C₁ - C₂

      -- Step 8A: Apply Riemann_via_Γ₁_Cancel_r (C₁ = A₂)
      have h8A : C₁ = A₂ := Riemann_via_Γ₁_Cancel_r M r θ β a

      -- Step 8B: Apply Riemann_via_Γ₁_Cancel_θ (C₂ = B₂)
      have h8B : C₂ = B₂ := Riemann_via_Γ₁_Cancel_θ M r θ β a

      -- Step 8C: Apply Riemann_via_Γ₁_Identify_r (A₁ = T2_r)
      have h8C : A₁ = sumIdx (fun λ => Γ₁ M r θ λ a Idx.θ * Γtot M r θ λ β Idx.r)
        := Riemann_via_Γ₁_Identify_r M r θ β a

      -- Step 8D: Apply Riemann_via_Γ₁_Identify_θ (B₁ = T2_θ)
      have h8D : B₁ = sumIdx (fun λ => Γ₁ M r θ λ a Idx.r * Γtot M r θ λ β Idx.θ)
        := Riemann_via_Γ₁_Identify_θ M r θ β a

      -- Substitute and simplify
      rw [h8A, h8B, h8C, h8D]
      -- After substitution:
      -- ∂Γ₁_r - ∂Γ₁_θ - T2_r - A₂ + T2_θ + B₂ + A₂ - B₂
      -- = ∂Γ₁_r - ∂Γ₁_θ - T2_r + T2_θ  (A₂ cancels, B₂ cancels)

      ring_nf  -- Normalize to final form
```

### Challenges

1. **Expression Matching**: The expression from Step 7 must exactly match the patterns in lemmas 8A-8D
   - May need to massage the expression first using `congr`, `funext`, etc.
   - May need to explicitly separate D_r into D_r1 + D_r2 (if not already done)

2. **Navigation**: The terms may be buried in complex algebraic structure
   - Option 1 (`rw` directly) is simpler if it works
   - Option 2 (`have` statements) is more explicit and debuggable

3. **Normalization**: After substitutions, need to simplify
   - `ring_nf` handles polynomial ring expressions
   - `abel_nf` handles abelian group expressions (addition/subtraction)
   - May need both

### Recommended Approach

**Start with Option 1** (direct `rw`):
- If it works, it's the cleanest
- If Lean can't find the pattern, fall back to Option 2

**Use Option 2 if**:
- Expressions don't match exactly
- Need to debug which lemma isn't applying
- Want explicit documentation of each transformation

### Estimated Time

- **Best case** (Option 1 works): 20 minutes
- **Typical case** (need some massage): 40 minutes
- **Worst case** (need Option 2): 60 minutes

**Average**: 40 minutes

### Dependencies

- All four lemmas 8A-8D proven
- Expression from Step 7 in correct form

### Build Verification

After Step 8:
```bash
lake build Papers.P5_GeneralRelativity.GR.Riemann
```

Should now have only ONE sorry remaining: the overall `Riemann_via_Γ₁` proof is complete except for any infrastructure sorries in Steps 4-7!

---

## Part VI: Final Assembly and Testing

### Task 6.1: Complete Remaining Infrastructure Sorries

**If Steps 4-7 have sorries** (from Part III), complete them:

1. **Differentiability discharge** in `prod_rule_backwards_sum`
   - Use existing `g_differentiable_*` and `Γtot_differentiable_*` lemmas
   - May need to add specific lemmas for product differentiability

2. **Any other tactical sorries** in Steps 4-7
   - Should be straightforward algebra/rewrites

**Estimated Time**: 30-60 minutes

### Task 6.2: Build Verification

Run full build:
```bash
lake build Papers.P5_GeneralRelativity.GR.Riemann
```

**Expected Result**: ✅ 0 errors

**If errors occur**:
- Check that all infrastructure lemmas are available
- Verify no typos in lemma applications
- Check that index arguments align correctly

### Task 6.3: Update Phase 4 for Sign Correction

**Reminder from SP Memo**: Phase 4 needs updating for the sign correction.

**File**: `Papers/P5_GeneralRelativity/GR/Riemann.lean`

**Lemma**: `regroup_right_sum_to_Riemann_CORRECT` (or similar)

**Change Required**:
Old (incorrect):
```lean
+ sumIdx (fun λ =>
    Γ₁ M r θ λ a Idx.θ * Γtot M r θ λ b Idx.r   -- T2_r
  - Γ₁ M r θ λ a Idx.r * Γtot M r θ λ b Idx.θ)  -- -T2_θ
```

New (correct):
```lean
+ sumIdx (fun λ =>
    Γ₁ M r θ λ a Idx.r * Γtot M r θ λ b Idx.θ   -- T2_θ
  - Γ₁ M r θ λ a Idx.θ * Γtot M r θ λ b Idx.r)  -- -T2_r
```

**Estimated Time**: 10-15 minutes

### Task 6.4: Smoke Test

Create a simple test to verify the proof works:

```lean
/-- Smoke test: Verify Riemann_via_Γ₁ compiles and has correct structure -/
example (M r θ : ℝ) (h_ext : Exterior M r θ) :
  Riemann M r θ Idx.t Idx.r Idx.r Idx.θ
  = dCoord Idx.r (fun r θ => Γ₁ M r θ Idx.t Idx.r Idx.θ) r θ
  - dCoord Idx.θ (fun r θ => Γ₁ M r θ Idx.t Idx.r Idx.r) r θ
  + sumIdx (fun λ =>
      Γ₁ M r θ λ Idx.r Idx.r * Γtot M r θ λ Idx.t Idx.θ
    - Γ₁ M r θ λ Idx.r Idx.θ * Γtot M r θ λ Idx.t Idx.r) := by
  exact Riemann_via_Γ₁ M r θ h_ext Idx.t Idx.r
```

**Estimated Time**: 5 minutes

---

## Part VII: Timeline Summary

### Session 1: Infrastructure (1 hour)
- Task 1.1: Reorganize sumIdx lemmas (30 min)
- Task 1.2: Add symmetry lemmas (20 min)
- Task 1.3: Verify metric compatibility (10 min)
- **Build checkpoint**

### Session 2: Helper Lemma + Steps 4-7 (2.5 hours)
- Task 2.1: Implement `prod_rule_backwards_sum` (60 min)
- Step 4: Split sums (15 min)
- Step 5: Product rule backwards (20 min)
- Step 6: Recognize Γ₁ (15 min)
- Step 7: Metric compatibility (30 min)
- **Build checkpoint**

### Session 3: Step 8 Lemmas (2 hours)
- Lemma 8A: M_r = D_r2 (30 min)
- Lemma 8B: M_θ = D_θ2 (15 min)
- Lemma 8C: D_r1 = T2_r (45 min)
- Lemma 8D: D_θ1 = T2_θ (20 min)
- **Build checkpoint**

### Session 4: Assembly + Testing (1.5 hours)
- Step 8 Assembly (40 min)
- Complete infrastructure sorries (30 min)
- Update Phase 4 (10 min)
- Smoke test (5 min)
- **Final build verification**

**Total Estimated Time**: 7 hours

---

## Part VIII: Risk Assessment and Contingencies

### High-Risk Items

1. **Step 7 Metric Compatibility**
   - Risk: `dCoord_g_via_compat_ext` may not exist or have wrong form
   - Contingency: Request lemma from SP or implement from metric compatibility axioms
   - Impact: 1-2 hour delay if missing

2. **Step 8 Lemma Matching**
   - Risk: Expression from Step 7 may not match lemma patterns exactly
   - Contingency: Add massage/navigation tactics, or create intermediate helper lemmas
   - Impact: 30-60 minute delay per mismatch

3. **Differentiability Discharge**
   - Risk: Missing differentiability lemmas for g or Γtot in Exterior region
   - Contingency: Add axioms temporarily or prove missing lemmas
   - Impact: 30-60 minute delay

### Medium-Risk Items

1. **sumIdx Lemma Reorganization**
   - Risk: Moving lemmas may break downstream dependencies
   - Contingency: Check all uses before moving, or duplicate temporarily
   - Impact: 15-30 minute delay

2. **Tactical Issues in Steps 4-7**
   - Risk: `simp_rw`, `conv`, or `congr` may not work as expected
   - Contingency: Use explicit rewrites and `have` statements
   - Impact: 20-40 minute delay per step

### Low-Risk Items

1. **Symmetry Lemmas**: Standard case enumeration, should work
2. **Lemmas 8A-8D**: SP provided clear tactical guidance
3. **Step 8 Assembly**: Straightforward application once lemmas proven

---

## Part IX: Success Criteria

### Phase 3 Complete When:

- ✅ Infrastructure in place (Tasks 1.1-1.3, 2.1)
- ✅ Steps 1-7 proven (0 sorries)
- ✅ Lemmas 8A-8D proven (0 sorries)
- ✅ Step 8 assembled
- ✅ Build passes with 0 errors
- ✅ Phase 4 updated for sign correction
- ✅ Smoke test passes

### Code Quality Criteria:

- ✅ Clear `calc` structure throughout
- ✅ Explicit step documentation
- ✅ Lemmas in logical sections
- ✅ No tactical timeouts
- ✅ Follows SP's tactical guidance

### Mathematical Correctness:

- ✅ Proof works for general metrics (not just Schwarzschild diagonal)
- ✅ Correct sign on ΓΓ commutator terms (-T2)
- ✅ Correct starting point (R_{βarθ})
- ✅ All index manipulations valid

---

## Part X: Implementation Checklist

Use this checklist to track progress:

### Infrastructure
- [ ] Task 1.1: Reorganize sumIdx lemmas
- [ ] Task 1.2: Add g_symm (if missing)
- [ ] Task 1.2: Add Γtot_symm (if missing)
- [ ] Task 1.3: Verify dCoord_g_via_compat_ext exists
- [ ] Build checkpoint: Infrastructure

### Helper Lemma
- [ ] Task 2.1: Implement prod_rule_backwards_sum
- [ ] Build checkpoint: Helper lemma

### Steps 4-7
- [ ] Step 4: Split sums
- [ ] Step 5: Product rule backwards
- [ ] Step 6: Recognize Γ₁
- [ ] Step 7: Metric compatibility
- [ ] Build checkpoint: Steps 4-7

### Step 8 Lemmas
- [ ] Lemma 8A: M_r = D_r2
- [ ] Lemma 8B: M_θ = D_θ2
- [ ] Lemma 8C: D_r1 = T2_r
- [ ] Lemma 8D: D_θ1 = T2_θ
- [ ] Build checkpoint: Step 8 lemmas

### Assembly
- [ ] Step 8: Assemble in main proof
- [ ] Complete infrastructure sorries
- [ ] Update Phase 4 sign correction
- [ ] Smoke test
- [ ] Build checkpoint: Final

### Documentation
- [ ] Update PROGRESS_REPORT with completion status
- [ ] Document any deviations from plan
- [ ] Note any additional lemmas created

---

**Prepared by**: Research Team + Claude (AI Assistant)
**Date**: October 16, 2025
**Based on**: SP Tactical Guidance Memo (October 16, 2025)
**Status**: Ready for implementation
**Estimated Total Time**: 7 hours
**Next Action**: Begin with Part I (Infrastructure Prerequisites)
