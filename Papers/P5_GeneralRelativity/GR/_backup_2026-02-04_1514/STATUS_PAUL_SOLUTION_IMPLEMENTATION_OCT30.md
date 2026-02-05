# Status: Paul's Surgical Extraction Solution - Implementation Needs

**Date**: October 30, 2025
**Task**: Implement Paul's drop-in solution for Step 4½ payload extraction
**Status**: ⏸️ **PARTIAL** - Need goal state inspection or JP guidance

---

## Paul's Solution (Received)

Paul provided a complete 3-part surgical extraction strategy to fix the `payload_cancel_all` pattern mismatch:

### Part A: α-Rename (`e` → `ρ`)
```lean
have hα₁ :
  (sumIdx (fun e => ...payload terms with e...))
  =
  (sumIdx (fun ρ => ...same payload terms with ρ...)) := rfl
simp only [hα₁]
```

### Part B: Collect Payload into Block `P`
```lean
set P :=
  ( sumIdx (fun ρ => ..._1) )
+ ( sumIdx (fun ρ => ..._2) )
+ ( sumIdx (fun ρ => ..._3) )
+ ( sumIdx (fun ρ => ..._4) )
  with hPdef

have h_split : _ = P + (/* rest */) := by
  simp only [flatten₄₁, flatten₄₂, group_add_sub]
  -- use collectors to group four payload Σ's
  -- simp [hPdef] to finish
```

### Part C: Cancel via `congrArg`
```lean
have hP0 : P = 0 := by
  simpa [hPdef] using payload_cancel_all M r θ h_ext μ ν a b

have : P + (/* rest */) = 0 + (/* rest */) :=
  congrArg (fun t => t + (/* rest */)) hP0

simp [h_split, this]  -- replaces P by 0, leaves rest
```

---

## What's Blocking Implementation

### Missing Information: The "Rest" Expression

Paul's solution requires knowing the exact form of the goal state after steps 1-4, specifically:
- What is the exact expression for "rest" (the ∂Γ and ΓΓ blocks)?
- How should the four payload Σ terms be extracted/regrouped from the full goal?

This requires **either**:

**Option A**: Inspect goal state in Lean's InfoView (interactive environment)
- Open Riemann.lean in VS Code with Lean extension
- Navigate to line 9147 (after initial `simp only`)
- View goal state in InfoView panel
- Copy exact expression for "rest"
- Determine sequence of collector applications

**Option B**: Have JP provide the exact expressions
- What is the full goal state after line 9147?
- What is the "rest" expression (everything except the four payload Σ's)?
- What collector sequence groups the payload terms?

---

## Current Implementation Status

### What's Been Done ✅
- Replaced Step 4½+5 block with Paul's surgical extraction framework
- Inserted initial binder-safe flattening (`simp only [flatten₄₁, ...]`)
- Added structural comments documenting the 3-part strategy
- Placeholder `sorry` inserted at line 9150

### What's Not Done ❌
- Part A: α-rename `have hα₁`  (need exact payload expression shapes)
- Part B: `set P := ...` with exact four Σ terms (need to identify them in goal)
- Part B: `have h_split` with "rest" expression (need to know what "rest" is)
- Part C: `congrArg` with "rest" (depends on Part B)

---

## Two Paths Forward

### Path 1: Interactive Development (Recommended)

**Requires**: Access to Lean 4 interactive environment (VS Code + Lean extension)

**Steps**:
1. Open Riemann.lean in VS Code with Lean extension
2. Navigate to line 9147
3. Inspect goal state in InfoView
4. Identify the four payload sumIdx terms
5. Identify the "rest" (∂Γ + ΓΓ terms)
6. Apply collectors to group payload terms
7. Complete `h_split` proof
8. Insert exact "rest" in `congrArg`

**Estimated time**: 30-60 minutes with interactive feedback

### Path 2: JP Provides Specifications

**Requires**: JP to provide goal state details

**Request to JP**:
> After line 9147 (`simp only [flatten₄₁, flatten₄₂, ...]`), what is:
> 1. The full goal state?
> 2. The exact four payload sumIdx terms (with index after α-rename)?
> 3. The "rest" expression (∂Γ + ΓΓ blocks)?
> 4. Which collector sequence groups the four payload Σ's?

**Estimated time**: 15-30 minutes once specs received

---

## Technical Notes

### Why We Can't Guess

Paul's solution is **surgically precise** - it requires:
- Exact syntactic match for α-renaming (`rfl` only works with exact forms)
- Exact identification of which terms are payload vs rest
- Exact "rest" expression for `congrArg` (must appear verbatim twice)

Guessing would likely produce:
- Type errors (if shapes don't match exactly)
- `rfl` failures (if α-rename forms aren't identical except binder name)
- `congrArg` failures (if "rest" expressions don't match syntactically)

### Why This is Low-Risk Once Implemented

Once we have the exact expressions:
- All tactics are deterministic (no AC search, no `ring_nf`)
- `rfl` for α-rename is definitionally sound
- `set P := ...` is just naming
- `congrArg` is standard equality lifting
- All subsequent steps (6-8) unchanged

---

## Alternative: Simplified Placeholder

### If Interactive Access Not Available

We could insert a simplified placeholder that:
1. Keeps the initial flattening
2. Uses `sorry` for the extraction
3. Continues with steps 6-8

```lean
-- Step 4½: Surgical payload extraction (Paul's solution, Oct 30, 2025)
simp only [flatten₄₁, flatten₄₂, group_add_sub, fold_sub_right, fold_add_left]

-- TODO: Implement Paul's 3-part extraction (A: α-rename, B: collect, C: cancel)
-- Requires goal state inspection to determine exact "rest" expression
-- See: STATUS_PAUL_SOLUTION_IMPLEMENTATION_OCT30.md
sorry  -- Placeholder for payload extraction and cancellation

-- Continue with remaining blocks on "rest"
rw [dGamma_match M r θ h_ext μ ν a b]
rw [main_to_commutator M r θ h_ext μ ν a b]
rw [cross_block_zero M r θ h_ext μ ν a b]
simp only [...]
```

This allows:
- File to compile (with 1 additional sorry)
- Documentation of what's needed
- Continuation once goal state is known

---

## Recommendation

**Immediate**: Insert simplified placeholder (above) to keep file buildable

**Next Session**: Either:
- **Option A**: Interactive development with Lean extension access
- **Option B**: Request goal state specs from JP and complete implementation

**Timeline**: Can be completed in next session once goal state is available

---

**Prepared by**: Claude Code (Lean 4 Assistant)
**Date**: October 30, 2025
**Status**: Awaiting goal state inspection or JP specifications to complete Paul's solution
**File**: Riemann.lean lines 9142-9150 (partial implementation with placeholder)
