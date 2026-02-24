# SCOPING ISSUE: Strategy A Implementation Blocked

**Date**: November 6, 2025
**Status**: 🚧 **Implementation blocked by scoping issue - need guidance**

---

## Problem Summary

Implemented Paul's Strategy A patch exactly as specified, but build fails with:
- **Error count**: Still 18 (not reduced to 17)
- **New errors**:
  - Line 9189: `Unknown identifier 'ΓΓ_block'`
  - Line 9194: `Unknown identifier 'ΓΓ_block'`

**Root cause**: `ΓΓ_block` is defined as a local `have` statement inside the `hb` and `ha` proofs, so it's not accessible at the outer scope where the helper lemmas try to reference it.

---

## Current Code Structure

### `hb` calc chain (lines 8746-8948)
```lean
have hb :
  (sumIdx B_b) - sumIdx ... + sumIdx ...
  =
  - sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ) := by
  classical
  simp only [nabla_g, RiemannUp, sub_eq_add_neg]  -- doesn't use hb_pack

  have payload_cancel : ... := by ...

  have ΓΓ_block :  -- LOCAL to hb's proof, line 8777
      ( sumIdx (fun ρ => (Γtot M r θ ρ μ a) * sumIdx ...)
      - sumIdx (fun ρ => (Γtot M r θ ρ ν a) * sumIdx ...) )
    + ( sumIdx (fun ρ => (Γtot M r θ ρ μ a) * sumIdx ...)
      - sumIdx (fun ρ => (Γtot M r θ ρ ν a) * sumIdx ...) )
    =
      bb_core + rho_core_b := by
    [~75 lines of proof]

  [rest of calc chain using ΓΓ_block...]
```

### `hb_pack` (lines 8735-8744)
```lean
have hb_pack :
  (sumIdx B_b) - Cμa + Cνa
    = sumIdx (fun ρ =>
        B_b ρ
      - (Γtot M r θ ρ μ a) * (nabla_g M r θ ν ρ b)
      + (Γtot M r θ ρ ν a) * (nabla_g M r θ μ ρ b)) := by
  rw [hCμa, hCνa]
  rw [← sumIdx_map_sub B_b (fun ρ => (Γtot M r θ ρ μ a) * (nabla_g M r θ ν ρ b))]
  rw [← sumIdx_add_distrib]
```

**Note**: `hb_pack` is NOT used in the original `hb` calc chain (which starts with `simp only [nabla_g, ...]`).

### Paul's helper lemma (lines 9186-9189) - FAILS
```lean
have hb_plus :
    (sumIdx B_b) - Cμa + Cνa = bb_core + rho_core_b := by
  rw [hb_pack]
  exact ΓΓ_block  -- ERROR: Unknown identifier 'ΓΓ_block'
```

---

## The Mismatch Issue

**`hb_pack` RHS** (packed sumIdx form):
```lean
sumIdx (fun ρ =>
  B_b ρ
  - (Γtot M r θ ρ μ a) * (nabla_g M r θ ν ρ b)
  + (Γtot M r θ ρ ν a) * (nabla_g M r θ μ ρ b))
```

**`ΓΓ_block` LHS** (expanded ΓΓ·g quartet form):
```lean
( sumIdx (fun ρ => (Γtot M r θ ρ μ a) * sumIdx (fun e => Γtot M r θ e ν ρ * g M e b r θ))
- sumIdx (fun ρ => (Γtot M r θ ρ ν a) * sumIdx (fun e => Γtot M r θ e μ ρ * g M e b r θ)) )
+ ( sumIdx (fun ρ => (Γtot M r θ ρ μ a) * sumIdx (fun e => Γtot M r θ e ν b * g M ρ e r θ))
- sumIdx (fun ρ => (Γtot M r θ ρ ν a) * sumIdx (fun e => Γtot M r θ e μ b * g M ρ e r θ)) )
```

These don't match directly. There's a transformation in between that expands `nabla_g` and `B_b` and does payload cancellation.

---

## Possible Solutions

### Option 1: Extract `ΓΓ_block` as Standalone Lemmas

**Approach**:
1. Copy the b-branch `ΓΓ_block` (lines 8777-8850) to a standalone lemma `ΓΓ_block_b` right after `hb_pack` (after line 8744)
2. Copy the a-branch `ΓΓ_block` (lines 8991-9064) to a standalone lemma `ΓΓ_block_a` right after `ha_pack` (after line 8959)
3. Update `hb` and `ha` to reference the extracted lemmas (change `have ΓΓ_block` to just use the standalone version)
4. Update helper lemmas to use `ΓΓ_block_b` and `ΓΓ_block_a`

**Issue**: Still need to bridge the gap between `hb_pack` RHS and `ΓΓ_block` LHS. The helper lemma proof would need to be:
```lean
have hb_plus :
    (sumIdx B_b) - Cμa + Cνa = bb_core + rho_core_b := by
  calc
    (sumIdx B_b) - Cμa + Cνa
        = sumIdx (fun ρ => B_b ρ - ... + ...) := hb_pack
    _   = [intermediate expanded form] := by simp only [nabla_g, B_b, ...]
                                                  [payload cancellation steps]
    _   = bb_core + rho_core_b := ΓΓ_block_b
```

**Question**: What are the exact simp/rw steps to bridge from `hb_pack` RHS to `ΓΓ_block` LHS?

### Option 2: Inline the Entire Proof Chain

**Approach**: Copy ~100 lines from `hb_pack` through all calc steps to `bb_core + rho_core_b` directly into the helper lemma.

**Downside**: Massive code duplication.

### Option 3: Different Helper Lemma Strategy

**Question for Paul**: Was the helper lemma pseudocode, or should it literally be a one-liner `rw [hb_pack]; exact ΓΓ_block`?

If the latter isn't possible due to the type mismatch, what's the intended proof strategy for the helpers?

---

## Request for Guidance

**Questions**:

1. Should I extract `ΓΓ_block` as standalone lemmas? If yes, what should the type signature be for the extracted lemmas?

2. How do I bridge the gap between `hb_pack` RHS and `ΓΓ_block` LHS in the helper lemma proofs?

3. OR, is there a simpler approach I'm missing?

**Build log**: `build_step9_paul_strategy_a_nov5.txt` (18 errors, lines 9189 and 9194 are the new scope errors)

---

**Status**: Awaiting guidance on implementation approach for Strategy A.
