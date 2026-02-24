# Level 3 Tactical Implementation Guide
# Quick Reference for Developers

**Companion to:** ROADMAP_LEVEL3.md
**Purpose:** Copy-paste code templates and implementation patterns

---

## Priority 1: Topology Implementation

### File Location
**Add to:** `Papers/P5_GeneralRelativity/GR/Riemann.lean`
**After line:** ~60 (in topological infrastructure section)

### Template 1: General Helper Lemma

```lean
-- ============================================================================
-- PRIORITY 1.1: General topology helper for locally constant derivatives
-- ============================================================================

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Basic
open Filter Topology

/-- If a function f equals zero on an open set U containing x,
    then its derivative at x is zero.

    This is the key lemma for eliminating AX_nabla_g_zero. -/
lemma deriv_zero_of_locally_zero {f : ℝ → ℝ} {x : ℝ} {U : Set ℝ}
    (hU_open : IsOpen U) (hx : x ∈ U) (hf_zero : ∀ y ∈ U, f y = 0) :
    deriv f x = 0 := by
  -- Step 1: U is a neighborhood of x
  have h_nhds : U ∈ 𝓝 x := hU_open.mem_nhds hx

  -- Step 2: f is eventually equal to the zero function near x
  have h_eventually_eq_zero : f =ᶠ[𝓝 x] (fun _ => 0) := by
    apply eventually_of_mem h_nhds
    intro y hy
    simp [hf_zero y hy]

  -- Step 3: The derivative of f equals the derivative of the zero function
  rw [deriv_congr h_eventually_eq_zero]

  -- Step 4: The derivative of a constant is zero
  simp [deriv_const]
```

**Success check:**
```bash
lake build Papers.P5_GeneralRelativity.GR.Riemann
# Should build with no errors on this lemma
```

---

### Template 2: Apply to nabla_g

```lean
-- ============================================================================
-- PRIORITY 1.2-1.4: Derivative of nabla_g is zero on Exterior
-- ============================================================================

/-- The coordinate derivative of nabla_g is zero on the Exterior domain.

    This eliminates the need for AX_nabla_g_zero by using:
    - nabla_g_zero_ext: nabla_g = 0 on Exterior
    - isOpen_exterior_set: Exterior is an open set
    - deriv_zero_of_locally_zero: derivative of locally constant function is zero
-/
lemma dCoord_nabla_g_zero_ext (M r θ : ℝ) (h_ext : Exterior M r θ)
    (μ c a b : Idx) :
    dCoord μ (fun r θ => nabla_g M r θ c a b) r θ = 0 := by
  cases μ

  -- ===== Case: μ = t (trivial) =====
  case t =>
    simp [dCoord_t]

  -- ===== Case: μ = φ (trivial) =====
  case φ =>
    simp [dCoord_φ]

  -- ===== Case: μ = r (requires topology) =====
  case r =>
    simp only [dCoord_r]
    -- Goal: deriv (fun r' => nabla_g M r' θ c a b) r = 0

    -- Define the open set U = {r' : ℝ | 2 * M < r'}
    let U := {r' : ℝ | 2 * M < r'}

    -- U is open (it's the open interval (2M, ∞))
    have hU_open : IsOpen U := isOpen_Ioi (2 * M)

    -- (r, θ) ∈ Exterior means r ∈ U
    have hx : r ∈ U := h_ext.hr_ex

    -- Apply the general lemma
    apply deriv_zero_of_locally_zero hU_open hx

    -- Prove that nabla_g is zero on U
    intro r' hr'_ex
    -- For any r' > 2M, we can construct Exterior M r' θ
    have hM_pos := h_ext.hM
    have h_ext' : Exterior M r' θ := { hM := hM_pos, hr_ex := hr'_ex }
    -- nabla_g_zero_ext tells us nabla_g = 0 on Exterior
    exact nabla_g_zero_ext M r' θ h_ext' c a b

  -- ===== Case: μ = θ (requires topology) =====
  case θ =>
    simp only [dCoord_θ]
    -- Goal: deriv (fun θ' => nabla_g M r θ' c a b) θ = 0

    -- The Exterior condition is independent of θ (only depends on r > 2M)
    -- So nabla_g = 0 for ALL θ, which means U = ℝ (the universal set)
    let U := Set.univ

    -- The universal set is always open
    have hU_open : IsOpen U := isOpen_univ

    -- θ is in the universal set
    have hx : θ ∈ U := Set.mem_univ θ

    -- Apply the general lemma
    apply deriv_zero_of_locally_zero hU_open hx

    -- Prove that nabla_g is zero on U (for all θ')
    intro θ' _
    -- The Exterior hypothesis for (r, θ') is the same as for (r, θ)
    -- because it only depends on r > 2M and M > 0
    exact nabla_g_zero_ext M r θ' h_ext c a b
```

**Success check:**
```bash
# Check it type-checks
lake build Papers.P5_GeneralRelativity.GR.Riemann
# Should build successfully
```

---

### Template 3: Refactor Riemann_swap_a_b

**Find and replace:**

```lean
-- OLD VERSION (uses axiom):
lemma Riemann_swap_a_b (M r θ : ℝ) (a b c d : Idx) :
  Riemann M r θ a b c d = Riemann M r θ a b d c := by
  -- ... uses AX_nabla_g_zero ...
  sorry
```

**Replace with:**

```lean
-- NEW VERSION (uses Exterior hypothesis):
lemma Riemann_swap_a_b_ext (M r θ : ℝ) (h_ext : Exterior M r θ) (a b c d : Idx) :
  Riemann M r θ a b c d = Riemann M r θ a b d c := by
  -- Unfold Riemann definition
  simp only [Riemann]

  -- The key step that previously used AX_nabla_g_zero
  -- Now uses dCoord_nabla_g_zero_ext with explicit Exterior hypothesis
  have h1 : dCoord c (fun r θ => nabla_g M r θ d a b) r θ = 0 :=
    dCoord_nabla_g_zero_ext M r θ h_ext c d a b

  have h2 : dCoord d (fun r θ => nabla_g M r θ c a b) r θ = 0 :=
    dCoord_nabla_g_zero_ext M r θ h_ext d c a b

  -- Continue with the rest of the proof using h1 and h2
  sorry -- COMPLETE THE REST OF THE PROOF
```

**Success check:**
```bash
# Ensure no more uses of AX_nabla_g_zero in this lemma
grep -n "AX_nabla_g_zero" Papers/P5_GeneralRelativity/GR/Riemann.lean
```

---

### Template 4: Refactor dCoord_g_via_compat

```lean
-- OLD VERSION (uses axiom):
lemma dCoord_g_via_compat (M r θ : ℝ) (μ a b : Idx) :
  dCoord μ (fun r θ => g M a b r θ) r θ = ... := by
  -- ... uses AX_nabla_g_zero ...
  sorry

-- NEW VERSION (uses Exterior hypothesis):
lemma dCoord_g_via_compat_ext (M r θ : ℝ) (h_ext : Exterior M r θ) (μ a b : Idx) :
  dCoord μ (fun r θ => g M a b r θ) r θ = ... := by
  -- Use dCoord_nabla_g_zero_ext h_ext instead of AX_nabla_g_zero
  sorry -- IMPLEMENT
```

---

### Template 5: Update All Call Sites

**Pattern to search for:**

```bash
# Find all uses of Riemann_swap_a_b
grep -n "Riemann_swap_a_b[^_]" Papers/P5_GeneralRelativity/GR/Riemann.lean
```

**For each call site, add Exterior hypothesis:**

```lean
-- OLD:
rw [Riemann_swap_a_b M r θ a b c d]

-- NEW (if Exterior already in scope):
rw [Riemann_swap_a_b_ext M r θ h_ext a b c d]

-- NEW (if need to assume Exterior):
intro h_ext  -- or: have h_ext : Exterior M r θ := ...
rw [Riemann_swap_a_b_ext M r θ h_ext a b c d]
```

---

### Template 6: Delete the Axiom

**After all refactoring complete:**

```lean
-- DELETE THIS BLOCK:
/-- QUARANTINED AXIOM - Metric compatibility (global version)
    ... documentation ...
-/
lemma AX_nabla_g_zero (M r θ : ℝ) (c a b : Idx) :
  nabla_g M r θ c a b = 0 := by
  sorry -- QUARANTINED AXIOM
```

**Verification:**

```bash
# Should return 0 matches (except comments)
grep "AX_nabla_g_zero" Papers/P5_GeneralRelativity/GR/Riemann.lean | grep -v "^[[:space:]]*--"

# Should show only AX_differentiable_hack remaining
grep "^lemma AX_" Papers/P5_GeneralRelativity/GR/Riemann.lean
```

---

## Priority 2: Differentiability Grind

### Automated Hypothesis Discharge Tactic

**Add to Riemann.lean (early in file):**

```lean
-- ============================================================================
-- PRIORITY 2.1: Automated tactic for discharging differentiability hypotheses
-- ============================================================================

/-- Tactic to automatically discharge differentiability hypotheses.

    Tries two strategies:
    1. Prove differentiability using concrete lemmas and combinators
    2. Prove direction mismatch (e.g., μ ≠ Idx.r)
-/
syntax "discharge_diff" : tactic

macro_rules
  | `(tactic| discharge_diff) => `(tactic| (
      first
      | -- Strategy 1: Prove differentiability
        simp only [DifferentiableAt_r, DifferentiableAt_θ,
                   -- Metric components
                   differentiableAt_g_tt_r, differentiableAt_g_rr_r,
                   differentiableAt_g_θθ_r, differentiableAt_g_φφ_r,
                   differentiableAt_g_tt_θ, differentiableAt_g_rr_θ,
                   differentiableAt_g_θθ_θ, differentiableAt_g_φφ_θ,
                   -- Differentiability combinators
                   DifferentiableAt.add, DifferentiableAt.sub,
                   DifferentiableAt.mul, DifferentiableAt.div,
                   DifferentiableAt.comp, DifferentiableAt.const_mul,
                   -- Standard functions
                   differentiableAt_sin, differentiableAt_cos,
                   differentiableAt_const, differentiableAt_id]
      | -- Strategy 2: Prove direction mismatch
        simp [Idx.r, Idx.θ, Idx.t, Idx.φ]
    ))
```

**Usage:**

```lean
apply dCoord_add_of_diff c (fun r θ => g M μ a r θ) (fun r θ => g M μ b r θ) r θ
all_goals { discharge_diff }
```

---

### Refactoring Pattern Template

**Search pattern:**

```bash
# Find uses of dCoord_add
grep -n "dCoord_add[^_]" Papers/P5_GeneralRelativity/GR/Riemann.lean
```

**Before:**

```lean
calc dCoord c (fun r θ => f r θ + g r θ) r θ
   = dCoord c f r θ + dCoord c g r θ := by rw [dCoord_add]
   _ = ...
```

**After:**

```lean
calc dCoord c (fun r θ => f r θ + g r θ) r θ
   = dCoord c f r θ + dCoord c g r θ := by
     apply dCoord_add_of_diff
     all_goals { discharge_diff }
   _ = ...
```

---

### Batch Refactoring Checklist

**Batch 1: Stage-1 LHS (~20 uses)**
- [ ] Lines 1200-1400: Stage1_LHS_c_split
- [ ] Lines 1400-1500: Stage1_LHS_d_split
- [ ] Test: `lake build` after batch

**Batch 2: Stage-1 RHS (~20 uses)**
- [ ] Lines 2600-2700: Stage1_RHS_c_first
- [ ] Lines 2700-2800: Stage1_RHS_d_first
- [ ] Test: `lake build` after batch

**Batch 3: Riemann computation (~20 uses)**
- [ ] Lines 3000-3500: Riemann tensor computation
- [ ] Test: `lake build` after batch

**Batch 4: Infrastructure (~16 uses)**
- [ ] Lines 800-1200: Helper infrastructure
- [ ] Test: `lake build` after batch

---

### Delete Axiom-Dependent Lemmas

**After all refactoring:**

```lean
-- DELETE THESE BLOCKS:

lemma dCoord_add (μ : Idx) (f g : ℝ → ℝ → ℝ) (r θ : ℝ) :
  ... := by sorry  -- DELETE

lemma dCoord_sub (μ : Idx) (f g : ℝ → ℝ → ℝ) (r θ : ℝ) :
  ... := by sorry  -- DELETE

lemma dCoord_mul (μ : Idx) (f g : ℝ → ℝ → ℝ) (r θ : ℝ) :
  ... := by sorry  -- DELETE

lemma AX_differentiable_hack (f : ℝ → ℝ) (x : ℝ) :
  DifferentiableAt ℝ f x := by sorry  -- DELETE
```

**Verification:**

```bash
# Should return 0 matches
grep "^lemma AX_" Papers/P5_GeneralRelativity/GR/Riemann.lean
grep "AX_differentiable_hack" Papers/P5_GeneralRelativity/GR/Riemann.lean
grep "dCoord_add[^_]" Papers/P5_GeneralRelativity/GR/Riemann.lean | grep "^lemma"
```

---

## Priority 3: Axiom Audit

### Command Template

```bash
# In Lean REPL or as test file:
lake env lean

# Then in Lean:
import Papers.P5_GeneralRelativity.GR.Schwarzschild

#print axioms Ricci_tt_vanishes
#print axioms Ricci_rr_vanishes
#print axioms Ricci_θθ_vanishes
#print axioms Ricci_φφ_vanishes
#print axioms Ricci_scalar_vanishes
```

**Expected output (TRUE LEVEL 3):**

```
-- Should show ONLY Mathlib axioms, NO project-specific axioms

Ricci_tt_vanishes : ...
-- Axioms:
-- propext : ...
-- Quot.sound : ...
-- Classical.choice : ...
```

**If you see:**

```
-- AX_nabla_g_zero : ...
-- AX_differentiable_hack : ...
```

**Then:** Level 3 NOT achieved, go back and eliminate these!

---

### Audit Documentation Template

**Create:** `LEVEL_4_AXIOM_AUDIT.md`

```markdown
# Level 4 Axiom Audit
# Mathlib Foundational Dependencies

**Date:** [DATE]
**Status:** ✅ True Level 3 Achieved (0 project axioms)

## Vacuum Solution Axiom Dependencies

### Ricci_tt_vanishes

\`\`\`lean
#print axioms Ricci_tt_vanishes
\`\`\`

**Output:**
\`\`\`
propext : ...
funext : ...
Quot.sound : ...
Classical.choice : ...
\`\`\`

**Analysis:**
- `propext`: Propositional extensionality (P ↔ Q → P = Q)
- `funext`: Function extensionality (∀x, f x = g x → f = g)
- `Quot.sound`: Quotient soundness (equivalence → equality in quotient)
- `Classical.choice`: Axiom of Choice (classical logic)

[Repeat for all 5 theorems]

## Dependency Graph

[Visualization or table showing which Mathlib axioms are used]

## Classification

**Base theory:** Classical mathematics
- LEM: Yes (via Classical.choice)
- AC: Yes (Classical.choice)
- Impredicativity: Yes (Prop)

**Strength:** ZFC (Zermelo-Fraenkel Set Theory + Choice)

## Reverse Mathematics (if applicable)

[Optional: Classify in terms of subsystems of second-order arithmetic]
```

---

## Verification Checklists

### After Priority 1 (1 axiom eliminated)

```bash
# ✅ Only AX_differentiable_hack should remain
grep "^lemma AX_" Papers/P5_GeneralRelativity/GR/Riemann.lean
# Expected output: Only AX_differentiable_hack

# ✅ AX_nabla_g_zero should be gone
grep "AX_nabla_g_zero" Papers/P5_GeneralRelativity/GR/Riemann.lean
# Expected: Only comment references

# ✅ Build succeeds
lake build Papers.P5_GeneralRelativity.GR.Riemann
# Expected: Success

# ✅ Critical path still clean
grep -i "sorry\|axiom" Papers/P5_GeneralRelativity/GR/Schwarzschild.lean
# Expected: 0 matches
```

---

### After Priority 2 (TRUE LEVEL 3)

```bash
# ✅ ZERO project axioms
grep "^lemma AX_\|^axiom" Papers/P5_GeneralRelativity/GR/Riemann.lean
# Expected: 0 matches

# ✅ No axiom uses
grep "AX_differentiable_hack\|AX_nabla_g_zero" Papers/P5_GeneralRelativity/GR/Riemann.lean | grep -v "^[[:space:]]*--"
# Expected: 0 matches (only comments OK)

# ✅ Build succeeds
lake build Papers.P5_GeneralRelativity.GR.Riemann
# Expected: Success

# ✅ Critical path still clean
grep -i "sorry\|axiom" Papers/P5_GeneralRelativity/GR/Schwarzschild.lean
# Expected: 0 matches

# ✅ Axiom audit shows only Mathlib
# (See Priority 3 commands above)
```

---

### After Priority 3 (LEVEL 4 COMPLETE)

```bash
# ✅ Audit document exists
ls Papers/P5_GeneralRelativity/GR/LEVEL_4_AXIOM_AUDIT.md
# Expected: File exists

# ✅ All 5 theorems audited
grep "#print axioms" Papers/P5_GeneralRelativity/GR/LEVEL_4_AXIOM_AUDIT.md | wc -l
# Expected: 5 (one for each Ricci theorem)

# ✅ No project axioms in audit
grep "AX_" Papers/P5_GeneralRelativity/GR/LEVEL_4_AXIOM_AUDIT.md
# Expected: 0 matches (or only in "eliminated" context)
```

---

## Troubleshooting

### Issue: deriv_zero_of_locally_zero won't prove

**Symptoms:**
```
tactic 'apply' failed, failed to unify
  deriv f x = 0
with
  ?f =ᶠ[𝓝 ?x] ?g → deriv ?f ?x = deriv ?g ?x
```

**Solution:**
Check Mathlib imports. You need:
```lean
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Basic
```

**Alternative:** Search Mathlib for existing lemma:
```bash
# In Mathlib source
grep -r "deriv.*eventually" Mathlib/Analysis/Calculus/Deriv/
```

---

### Issue: discharge_diff tactic fails

**Symptoms:**
```
discharge_diff failed to prove goal
  DifferentiableAt_r (fun r θ => ...) r θ ∨ μ ≠ Idx.r
```

**Solution 1:** Add missing differentiability lemma to tactic
```lean
-- If you have a new function type, add its diff lemma:
differentiableAt_my_function_r,  -- ADD THIS
```

**Solution 2:** Prove manually
```lean
-- Instead of: all_goals { discharge_diff }
-- Do:
· left; exact differentiableAt_my_function_r M r θ  -- Prove LHS
· left; exact differentiableAt_my_function_r M r θ  -- Prove LHS
· right; simp  -- Prove RHS (direction mismatch)
· right; simp
```

---

### Issue: Refactoring causes downstream breakage

**Symptoms:**
```
error: unknown identifier 'Riemann_swap_a_b'
note: did you mean 'Riemann_swap_a_b_ext'?
```

**Solution:** Search-and-replace with Exterior hypothesis:
```bash
# Find all call sites
grep -n "Riemann_swap_a_b[^_]" Papers/P5_GeneralRelativity/GR/Riemann.lean

# For each, add h_ext:
# Before: Riemann_swap_a_b M r θ a b c d
# After:  Riemann_swap_a_b_ext M r θ h_ext a b c d
```

---

### Issue: Can't prove Exterior hypothesis

**Symptoms:**
```
error: failed to synthesize instance
  Exterior M r θ
```

**Solution:** Propagate from caller or add as lemma hypothesis:
```lean
-- Option 1: Propagate from caller
lemma my_lemma_ext (M r θ : ℝ) (h_ext : Exterior M r θ) : ... := by
  -- Now can use h_ext
  rw [Riemann_swap_a_b_ext M r θ h_ext ...]

-- Option 2: Construct manually
have h_ext : Exterior M r θ := {
  hM := sorry,      -- Prove M > 0
  hr_ex := sorry    -- Prove r > 2*M
}
```

---

## Quick Reference: Theorem Locations

| Theorem | File | Line (approx) | Purpose |
|---------|------|---------------|---------|
| `isOpen_exterior_set` | Riemann.lean | ~50 | Exterior is open |
| `nabla_g_zero_ext` | Riemann.lean | ~1050 | nabla_g = 0 on Exterior |
| `differentiableAt_g_tt_r` | Riemann.lean | ~236 | g_tt diff in r |
| `differentiableAt_g_rr_r` | Riemann.lean | ~242 | g_rr diff in r |
| `dCoord_add_of_diff` | Riemann.lean | ~272 | Addition with hypotheses |
| `Riemann_swap_a_b` | Riemann.lean | ~3093 | TO BE REFACTORED |

---

**Status:** ✅ TACTICAL GUIDE READY
**Use:** Copy templates as needed during implementation
**Companion:** ROADMAP_LEVEL3.md (strategic plan)
