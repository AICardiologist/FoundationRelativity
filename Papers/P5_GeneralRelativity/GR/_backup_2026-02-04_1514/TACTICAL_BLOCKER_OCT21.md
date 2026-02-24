# Tactical Blocker Report: dCoord Reduction Issue
**Date**: October 21, 2025
**Status**: ⚠️ **BLOCKED** - Cannot expand nabla/nabla_g without reducing dCoord to deriv

---

## EXECUTIVE SUMMARY

The main proof `ricci_identity_on_g_rθ_ext` is blocked at Step 2 due to a fundamental tactical issue:
- **Helper lemmas** expect `dCoord` syntax in the goal
- **All expansion tactics** (`simp only`, `delta`, `unfold`, `rw`, `show...from rfl`) reduce `dCoord` to its underlying `deriv` implementation
- **Pattern matching fails** because helper lemmas look for `dCoord` patterns but find `deriv` patterns

---

## THE PROBLEM

### Helper Lemma Pattern (Lines 5235-5244)

The helper lemma `dCoord_r_push_through_nabla_g_θ_ext` expects to rewrite:
```lean
dCoord Idx.r (fun r θ =>
  dCoord Idx.θ (fun r θ => g M a b r θ) r θ
  - sumIdx (fun e => Γtot M r θ e Idx.θ a * g M e b r θ)
  - sumIdx (fun e => Γtot M r θ e Idx.θ b * g M a e r θ)) r θ
```

### Goal After Expansion

After expanding `nabla` and `nabla_g` with ANY tactic, the goal contains:
```lean
deriv (fun s => deriv (fun t => (match a, b with ...) s t) θ) r
```

### Why They Don't Match

- Helper lemma: `dCoord Idx.r (fun r θ => sumIdx ...)`
- Actual goal: `deriv (fun s => sumIdx ...)`
- **Pattern match fails**: `dCoord` ≠ `deriv` syntactically

---

## TACTICS ATTEMPTED

### Attempt 1: `simp only [nabla, nabla_g]`
**Error**: Line 5410 - `Tactic 'rewrite' failed: Did not find an occurrence of the pattern`
**Reason**: `simp only` simplifies `dCoord` to `deriv`

### Attempt 2: `delta nabla nabla_g`
**Error**: Line 5411 - Same pattern matching failure
**Reason**: `delta` does definitional reduction, which reduces `dCoord` to `deriv`

### Attempt 3: `unfold nabla nabla_g`
**Error**: Same pattern matching failure
**Reason**: `unfold` also reduces `dCoord` definitionally

### Attempt 4: `show ... from rfl`
**Error**: Line 5432 - Same pattern matching failure
**Reason**: `rfl` proves definitional equality, forcing full reduction including `dCoord` → `deriv`

### Attempt 5: `rw [nabla, nabla_g]`
**Error**: Line 5391 - `Failed to rewrite using equation theorems for nabla_g`
**Reason**: `rw` cannot find suitable equation lemmas, and when it tries, it still reduces `dCoord`

---

## ROOT CAUSE

The fundamental issue is that `dCoord` is **defined** in terms of `deriv`:
```lean
noncomputable def dCoord (x : Idx) (f : ℝ → ℝ → ℝ) (r θ : ℝ) : ℝ := ...deriv...
```

Any tactic that expands definitions (whether via simplification, delta reduction, unfolding, or definitional equality) will reduce `dCoord` to its implementation `deriv`.

The helper lemmas are stated using `dCoord` syntax on both sides, so they expect the goal to also use `dCoord` syntax. But after expanding `nabla` and `nabla_g`, the goal uses `deriv` syntax.

---

## USER'S FINISHING KIT

The user provided a finishing kit with this instruction:
```lean
-- Step 1: expand nabla and nabla_g definitions (but keep dCoord structure)
simp only [nabla, nabla_g]
```

**This does not work in the current environment** - `simp only [nabla, nabla_g]` reduces `dCoord` to `deriv`.

Possible explanations:
1. **Different simp configuration**: User's environment may have different simp lemmas or attributes
2. **Missing context**: There may be additional setup or lemmas needed
3. **dCoord definition difference**: The definition of `dCoord` may be different in user's version
4. **Alternative interpretation**: The user may have intended a different tactical approach

---

## POSSIBLE SOLUTIONS

### Solution 1: Bridge Lemmas
Create intermediate lemmas that connect `nabla`/`nabla_g` forms directly to the helper lemma conclusions, without expanding to show `dCoord` structure:

```lean
lemma nabla_push_helper_r :
  ∀ M r θ a b, (h_ext : Exterior M r θ),
  nabla (fun M r θ a b => nabla_g M r θ Idx.θ a b) M r θ Idx.r a b
  = [RHS with distributed dCoord] := sorry
```

**Pros**: Avoids the expansion issue entirely
**Cons**: Requires proving new lemmas, may duplicate work

### Solution 2: Rewrite Helper Lemmas in Terms of deriv
Restate the helper lemmas using `deriv` instead of `dCoord`:

```lean
lemma dCoord_r_push_through_nabla_g_θ_ext_deriv :
  deriv (fun s => ...) r = deriv (fun s => ...) r - ...
```

**Pros**: Matches the actual goal structure
**Cons**: Breaks from the `dCoord` abstraction used elsewhere, requires reproving

### Solution 3: Use conv with Surgical Precision
Use `conv` mode to very selectively unfold only the outermost `nabla`/`nabla_g` layer without touching inner `dCoord`:

```lean
conv_lhs =>
  unfold nabla  -- only at top level?
```

**Pros**: Might preserve `dCoord` structure if done carefully
**Cons**: `conv` is fragile and may still reduce `dCoord`; requires interactive Lean for goal inspection

### Solution 4: Ask User for Clarification
Report the issue to the user and ask:
- Does `simp only [nabla, nabla_g]` work in their environment?
- Is there additional setup needed?
- Should helper lemmas be applied differently?

**Pros**: Gets authoritative answer
**Cons**: Requires user input

---

## CURRENT STATE

### What Works ✅
1. ✅ Collector lemma `sumIdx_collect_comm_block` - fixed with explicit `calc` chain (lines 1660-1714)
2. ✅ Helper lemmas - fully proven with explicit differentiability witnesses (lines 5235-5367)
3. ✅ All prerequisite infrastructure lemmas are proven
4. ✅ Build compiles successfully (3078 jobs, 0 errors) except for main proof

### What's Blocked ⚠️
1. ⚠️ Main proof Step 2 - cannot apply helper lemmas due to `dCoord` vs `deriv` mismatch
2. ⚠️ Remaining 6 steps - blocked waiting for Step 2

---

## BRIDGE LEMMA UPDATE (Latest Attempt)

### Attempt 6: Bridge Lemmas (Partial Success ✓/⚠️)

**Implementation**: Created bridge lemmas (lines 5379-5400) that directly state the result of expanding `nabla(...nabla_g...)` and applying helper lemmas:

```lean
private lemma nabla_r_of_nabla_g_θ_combined (M r θ : ℝ) (h_ext : Exterior M r θ) (a b : Idx) :
  nabla (fun M r θ a b => nabla_g M r θ Idx.θ a b) M r θ Idx.r a b
  =
  dCoord Idx.r (fun r θ => dCoord Idx.θ (fun r θ => g M a b r θ) r θ) r θ
  - dCoord Idx.r (fun r θ => sumIdx (fun e => Γtot M r θ e Idx.θ a * g M e b r θ)) r θ
  - dCoord Idx.r (fun r θ => sumIdx (fun e => Γtot M r θ e Idx.θ b * g M a e r θ)) r θ
  - sumIdx (fun d => Γtot M r θ d a Idx.r * nabla_g M r θ Idx.θ d b)
  - sumIdx (fun d => Γtot M r θ d b Idx.r * nabla_g M r θ Idx.θ a d)
:= by sorry
```

**Result**:
- ✅ **Steps 1-2 bypassed**: Bridge lemmas successfully applied, avoiding the expansion issue
- ⚠️ **Step 3 (`ring`) causes new issue**: After `ring` simplifies the goal, `dCoord` is reduced to `deriv` again
- ❌ **Step 5 blocked**: Product rule lemmas (`dCoord_r_sumIdx_Γθ_g_left_ext`, etc.) fail to match because goal has `deriv` instead of `dCoord`

**Error**: Line 5433 - `Tactic 'rewrite' failed: Did not find an occurrence of the pattern dCoord Idx.r (...)`
- Goal after `ring`: Contains `deriv (fun s => ...)` instead of `dCoord Idx.r (...)`
- Product rule lemmas expect: `dCoord Idx.r (fun r θ => sumIdx ...)`
- **Root cause**: `ring` tactic performs arithmetic simplification that reduces `dCoord` to `deriv`

**Conclusion**: Bridge lemmas are a viable approach for Steps 1-2, but the `ring` tactic at Step 3 introduces a new instance of the same fundamental problem (dCoord reduction).

---

## RECOMMENDATION

**Immediate next step**:

1. **Mark `dCoord` as irreducible** to prevent `ring` from reducing it:
   ```lean
   attribute [irreducible] dCoord
   ```
   - **Pros**: Would preserve `dCoord` syntax throughout the proof
   - **Cons**: May break other parts of the codebase that rely on `dCoord` being reducible; needs testing

2. **Replace `ring` with more conservative tactic** like `ac_rfl` or manual arithmetic rewrites
   - **Pros**: Avoid the reduction issue at Step 3
   - **Cons**: May not handle the arithmetic complexity; requires trial and error

3. **Create even more comprehensive bridge lemmas** that combine Steps 1-5 entirely
   - **Pros**: Bypass all the reduction issues in one go
   - **Cons**: Very complex bridge lemmas, essentially duplicates the entire proof structure

4. **Report to user** that the finishing kit doesn't work in this environment due to `dCoord` reduction
   - **Pros**: Gets authoritative answer about intended approach
   - **Cons**: Requires waiting for user response

---

## FILES MODIFIED

**`/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean`**
- Lines 1660-1714: ✅ Collector lemma fixed with `calc` chain
- Lines 5379-5400: ⚠️ Bridge lemmas created (admitted with `sorry`) to bypass Steps 1-2
- Lines 5415-5421: ⚠️ Main proof Steps 1-3 - bridge lemmas applied, then `ring`
- Lines 5433-5436: ❌ Step 5 (product rule lemmas) blocked - `dCoord` patterns don't match

**Build status**: ❌ Fails at line 5433 after `ring` reduces `dCoord` to `deriv`

---

## NEXT STEPS

1. **✅ DONE**: Tried bridge lemmas - successfully bypass Steps 1-2 but fail at Step 5 due to `ring` reducing `dCoord`
2. **NEXT**: Try Recommendation #1 (mark `dCoord` irreducible) or #4 (report to user)
3. **If irreducible works**: Complete Steps 4-8 and verify full proof
4. **Then**: Either prove bridge lemmas properly or investigate user's environment differences

---

**Prepared by**: Claude Code
**Date**: October 21, 2025 (Updated)
**Status**: ⚠️ **CRITICAL BLOCKER** - `dCoord` reduction occurs at multiple points (expansion AND ring)
