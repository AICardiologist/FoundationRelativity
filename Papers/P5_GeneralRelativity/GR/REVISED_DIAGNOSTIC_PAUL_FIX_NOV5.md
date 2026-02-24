# REVISED DIAGNOSTIC: Understanding the δ-Insertion Failure

**Date**: November 5, 2025
**Status**: 🔍 **Investigating type mismatch mystery**

---

## Key Discovery

**User Question**: "but can you figure out why error count remain same? where is the new error?"

**Answer**: The error wasn't fixed - it just moved and changed:
- Baseline (Step 8): Error at line 9283, message "unsolved goals"
- Current (Step 9, Paul's fix): Error at line 9219, message "Tactic `assumption` failed"
- Line shift: -64 (different from typical -91 shift for other errors)

**Both errors are in the `branches_sum` proof**:
- Baseline: failing at `rw [← hb, ← ha]`
- Current: failing at `simpa [hb, ha]`

---

## The Type Mismatch Mystery

### What I Observed

**`hb`'s type signature** (lines 8746-8751):
```lean
have hb :
  (sumIdx B_b)
  - sumIdx (fun ρ => (Γtot M r θ ρ μ a) * (nabla_g M r θ ν ρ b))
  + sumIdx (fun ρ => (Γtot M r θ ρ ν a) * (nabla_g M r θ μ ρ b))
=
  - sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ)
```

**`hb`'s calc chain ending** (lines 8934-8948):
```lean
_   = - sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ)
    + rho_core_b := by
  [proof steps]
```

**The calc proves**: `LHS = RHS + rho_core_b`
**The type claims**: `LHS = RHS`

**Yet `hb` compiles without errors!** (Checked lines 8746-8960 in build_step8_final_nov4.txt)

###  Possible Explanations

**Option 1**: Lean's calc/have unification automatically simplifies `RHS + rho_core_b` to `RHS` if it can prove `rho_core_b = 0`

But `diag_cancel : rho_core_b + rho_core_a = 0` only proves the **sum** is zero, not each term individually.

**Option 2**: I'm misreading the calc chain structure - maybe there ARE more steps after line 8948

But line 8949 starts the next lemma (`ha`), so the calc definitely ends at 8948.

**Option 3**: Lean's type inference is more flexible than I understand

Maybe `have hb : A = B := by calc _ = C` allows `C` to be defeq to `B` up to normalization?

---

## Why Both Approaches Fail

### Baseline Approach (Backward Rewriting)
```lean
calc
  _ = (RHS_b + rho_core_b) + (RHS_a + rho_core_a) := by rw [← hb, ← ha]
```

**Problem**: Tries to rewrite the LHS backward to match `hb`'s LHS, expecting `hb`'s RHS to be `RHS_b + rho_core_b`. But `hb`'s declared type says its RHS is just `RHS_b` (without `+ rho_core_b`).

**Error**: "unsolved goals" - Lean can't complete the rewrite because the types don't match.

### Paul's Approach (Forward Application)
```lean
have hcollapse :
  (grouped LHS_b) + (grouped LHS_a)
  =
  RHS_b + RHS_a := by
  simpa [hb, ha]
```

**Problem**: `simpa` tries to simplify using `hb` and `ha` in the forward direction. But the goal expects `RHS_b + RHS_a` (without rho_core terms), while applying `hb` and `ha` forward would give `(RHS_b + rho_core_b) + (RHS_a + rho_core_a)`.

**Error**: "Tactic `assumption` failed" - After simplification, `simpa` can't close the proof because there's still a mismatch.

---

## What Actually Needs to Happen

The `branches_sum` proof needs to:
1. Apply `hb` to get `LHS_b = RHS_b + rho_core_b`
2. Apply `ha` to get `LHS_a = RHS_a + rho_core_a`
3. Add them: `LHS_b + LHS_a = (RHS_b + rho_core_b) + (RHS_a + rho_core_a)`
4. Rearrange: `= RHS_b + RHS_a + (rho_core_b + rho_core_a)`
5. Apply `diag_cancel`: `rho_core_b + rho_core_a = 0`
6. Simplify: `= RHS_b + RHS_a`

**But**:
- Step 1 fails with backward rewriting because `hb`'s type doesn't include `+ rho_core_b`
- Step 1-2 fail with forward application because `simpa` doesn't know how to handle the intermediate rho_core forms

---

## Potential Solutions

### Solution A: Fix `hb` and `ha` Type Signatures

Change them to explicitly prove the "with rho_core" forms:

```lean
have hb_with_rho :
  LHS_b = RHS_b + rho_core_b := by
  [existing calc chain from hb]

have hb : LHS_b = RHS_b := by
  rw [hb_with_rho, diag_cancel_b_standalone]  -- if rho_core_b = 0 individually
  ring
```

**Problem**: We don't know if `rho_core_b = 0` individually (only the sum is zero).

### Solution B: Inline the Proof

Don't use `hb` and `ha` in `branches_sum` - instead, manually prove the equality with its own calc chain that includes the δ-insertion and cancellation steps.

**Problem**: Duplicates ~200 lines of proof logic.

### Solution C: Use Conv Mode or Explicit Transitivity

Manually construct the proof using explicit transitivity and `diag_cancel`:

```lean
calc
  LHS_b + LHS_a
      = RHS_b + rho_core_b + (RHS_a + rho_core_a) := by
    rw [hb_calc_step, ha_calc_step]  -- use specific calc steps, not final lemmas
  _   = RHS_b + RHS_a + (rho_core_b + rho_core_a) := by ring
  _   = RHS_b + RHS_a := by rw [diag_cancel]; ring
```

**Problem**: Need to identify which specific calc steps from `hb`/`ha` to use.

---

## Next Steps

1. **Investigate how `hb` typechecks**: Use `#check hb` or examine the elaborated term to see if Lean is automatically applying simplification.

2. **Try Solution C**: Extract the relevant calc steps from `hb` and `ha` that produce the "with rho_core" forms, and use those directly in `branches_sum`.

3. **Consult Paul/JP**: This might be an architectural issue where the lemma decomposition isn't quite right for the intended usage pattern.

---

**Status**: Paul's forward-direction approach doesn't work as expected. Need to either fix the architecture or find an alternative proof strategy.
