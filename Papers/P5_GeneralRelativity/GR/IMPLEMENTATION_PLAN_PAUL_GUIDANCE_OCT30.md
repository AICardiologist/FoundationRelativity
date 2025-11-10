# Implementation Plan: Paul's Guidance for Block C Completion

**Date**: October 30, 2025
**From**: Paul's directive on OPTION 1 vs OPTION 2
**Status**: ✅ **CLEAR PATH FORWARD - OPTION 1 FIRST**

---

## Executive Summary

**Decision**: Proceed with **OPTION 1 (Block C path)** for primary implementation, then add **OPTION 2 (JP's quartet fix)** as verification cross-check after Four-Block assembly succeeds.

**Rationale**:
- Block C (`main_to_commutator`) already implements mathematically correct transformation
- Minimizes surface area and removes failed identity from critical path
- Reduces regression risk from binder/simp churn
- JP's lemma valuable as targeted fix and invariant check, but not needed for completion

---

## OPTION 1: Complete Block C (Primary Path)

### Phase 1: Finish Block C Using `main_to_commutator`

**Location**: Riemann.lean:8994-9026

**Current status**: ✅ Compiles and implements correct strategy

**Key transformation** (already working):
```lean
rw [sumIdx_swap]          -- Fubini BEFORE contraction
apply sumIdx_congr        -- Pointwise equality under swapped binders
rw [← sumIdx_mul]         -- Factor the metric
simp only [g_symm]        -- Metric symmetry to align indices
ring                      -- Scalar reordering
```

**Cautions**:
1. Ensure `sumIdx_swap` is stated for `Idx` with `[Fintype Idx] [DecidableEq Idx]`
2. Keep `ring` restricted to scalar ground terms
3. If `ring` triggers typeclass search issues:
   - Add `by classical` locally
   - Use `simp [mul_add, add_mul]` before `ring` to cut search space

**Critical invariant**: Every ΓΓ term sits inside commutator difference **before** any contraction via g. This ensures we never require `[M_μ, M_ν] = 0`.

### Phase 2: Complete `expand_P_ab` and Assemble Four Blocks

**Four-Block Status**:
- **Block A**: `payload_cancel_all` ✅ PROVEN
- **Block B**: `cross_block_zero` ✅ PROVEN (lines 9058-9117)
- **Block C**: `main_to_commutator` ✅ PROVEN (lines 8994-9026)
- **Block D**: `dGamma_match` ✅ PROVEN (lines 9031-9052)

**Blocker**: `expand_P_ab` (line 9141 comment indicates assembly blocked by this)

**Action items**:
1. Investigate status of `expand_P_ab`
2. Complete if needed
3. Execute 8-step assembly in `algebraic_identity_four_block_old` (lines 9127-9149)

### Phase 3: Add Minimal Tests (Catch Future Bugs)

**Test a) Symbolic sanity check** (prevent premature contraction):
```lean
-- No contraction over ρ should appear before sum swapping:
#assert noPrematureContract :
  ¬ appearsBefore (contract ρ) (swap ρ e) main_to_commutator
```

**Test b) Numeric spot-check** (Schwarzschild @ r = 10M):
- Verify LHS ≠ RHS for false contracted Christoffel identity
- Verify Block C pipeline yields expected curvature sign
- Keep tiny and deterministic

---

## OPTION 2: JP's Quartet Fix (Verification Cross-Check)

**Status**: Stage AFTER Block C completion

**Purpose**:
- Correctness oracle (redundancy without re-entangling mainline)
- Targeted fix for quartet approach
- Invariant check that Block C didn't smuggle in commutation assumption

### Implementation: JP's `ΓΓ_commutator_relabel` Lemma

**Location**: Insert around lines 2100-2200 (with other index manipulation lemmas)

**Required shim** (if not present):
```lean
@[simp] lemma g_symm_shim (M r θ : ℝ) (i j : Idx) :
  g M i j r θ = g M j i r θ := by
  simpa [g_symm]  -- or use existing g_symm lemma
```

**Core lemma skeleton** (from Paul/JP):
```lean
/-- **Core reindexing for the ΓΓ commutator block (no diagonality yet).**
    Finite-sum identity: swap dummy indices in ΓΓ double sum,
    commute scalar factors, rename binders. No geometry, no calculus. -/
lemma ΓΓ_commutator_relabel
  (M r θ : ℝ) (μ ν a b : Idx) :
  sumIdx (fun ρ =>
    g M ρ b r θ *
    sumIdx (fun e =>
      Γtot M r θ ρ μ a * Γtot M r θ e ν ρ
    - Γtot M r θ ρ ν a * Γtot M r θ e μ ρ))
  =
  sumIdx (fun ρ =>
    g M ρ b r θ *
    sumIdx (fun e =>
      Γtot M r θ ρ ν e * Γtot M r θ e μ a
    - Γtot M r θ ρ μ e * Γtot M r θ e ν a)) := by
  classical
  -- Step 1: Push g inside inner sum (double sum view)
  -- Step 2: Apply index swap at level of double sum
  -- Step 3: Reorder scalar factors inside each difference
  -- Step 4: Swap finite sums back and rename binders
  -- Step 5: Use metric symmetry g eb = g ρb
  -- Step 6: Pull g back out

  -- Proof structure (from Paul's detailed skeleton):
  calc
    sumIdx (fun ρ =>
      g M ρ b r θ *
      sumIdx (fun e =>
        Γtot M r θ ρ μ a * Γtot M r θ e ν ρ
      - Γtot M r θ ρ ν a * Γtot M r θ e μ ρ))
        = sumIdx (fun ρ => sumIdx (fun e =>
            g M ρ b r θ *
            (Γtot M r θ ρ μ a * Γtot M r θ e ν ρ
          - Γtot M r θ ρ ν a * Γtot M r θ e μ ρ))) := by
              simpa [mul_sumIdx_right]
    _   = sumIdx (fun ρ => sumIdx (fun e =>
            g M e b r θ *
            (Γtot M r θ e μ a * Γtot M r θ ρ ν e
          - Γtot M r θ e ν a * Γtot M r θ ρ μ e))) := by
              simpa using sumIdx_swap_args _
    _   = sumIdx (fun ρ => sumIdx (fun e =>
            g M e b r θ *
            (Γtot M r θ ρ ν e * Γtot M r θ e μ a
          - Γtot M r θ ρ μ e * Γtot M r θ e ν a))) := by
              apply sumIdx_congr; intro ρ
              apply sumIdx_congr; intro e
              ring
    _   = sumIdx (fun e => sumIdx (fun ρ =>
            g M e b r θ *
            (Γtot M r θ ρ ν e * Γtot M r θ e μ a
          - Γtot M r θ ρ μ e * Γtot M r θ e ν a))) := by
              simpa using sumIdx_swap _
    _   = sumIdx (fun ρ => sumIdx (fun e =>
            g M ρ b r θ *
            (Γtot M r θ ρ ν e * Γtot M r θ e μ a
          - Γtot M r θ ρ μ e * Γtot M r θ e ν a))) := by
              -- Binder rename + symmetric metric
              apply sumIdx_congr; intro ρ
              apply sumIdx_congr; intro e
              simp [g_symm_shim]
    _   = sumIdx (fun ρ =>
          g M ρ b r θ *
          sumIdx (fun e =>
            Γtot M r θ ρ ν e * Γtot M r θ e μ a
          - Γtot M r θ ρ μ e * Γtot M r θ e ν a)) := by
              -- Pull g back out
              simp [mul_sumIdx_right]
```

### Where to Apply (Lines 7303 and 7605)

**At quartet pressure points**, replace:
```lean
-- OLD (premature contraction leading to false identity):
-- (collapsed g_{ρb} to g_{bb}, then tried to prove A = B)

-- NEW (keep double sum, relabel, then contract):
rw [ΓΓ_commutator_relabel M r θ μ ν a b]
-- Then apply diagonal contraction AFTER relabel
```

**Critical**: Do NOT orient `sumIdx_swap` in a way that flips commutator sign. Keep single convention: `[A,B] := AB - BA`.

### Pitfalls to Avoid

1. **Sign flips**: Don't write ad-hoc `rw [sub_eq_add_neg]` to make goals line up - you're probably introducing sign mistake
2. **Premature contraction**: Don't collapse free index before `sumIdx_swap` step
3. **Commutator orientation**: Pin `@[simp]` lemma for commutator convention and respect it

### Keep Quartet Path Gated

**Default**: OFF (Block C is primary path)
**Purpose**: Verification cross-check only
**Integration**: After Block C green, add as alternative proof path with explicit flag/comment

---

## Acceptance Criteria

### Criterion 1: Block C Pipeline Never Contracts Before Swap
✅ Every ΓΓ term sits inside commutator difference before any contraction
✅ `expand_P_ab` → Four-Block assembly → never contracts free index before `sumIdx_swap`

### Criterion 2: Quartet Path Agrees with Block C (After OPTION 2)
✅ Quartet path reduces to same commutatorized form via `ΓΓ_commutator_relabel`
✅ Numeric agreement with Block C on fixed coordinate choices

### Criterion 3: False Identity Quarantined
✅ Contracted Christoffel symmetry nowhere in codebase except quarantined test
✅ Test demonstrates its failure on Schwarzschild

---

## Implementation Timeline

### Week 1: OPTION 1 (Block C Path)
**Days 1-2**: Complete `expand_P_ab`
- Investigate current status
- Implement if needed
- Verify dependencies

**Days 3-4**: Four-Block Assembly
- Execute 8-step assembly in `algebraic_identity_four_block_old`
- Apply Blocks A, B, C, D sequentially
- Verify end-to-end curvature

**Day 5**: Testing
- Add symbolic sanity check
- Add numeric Schwarzschild spot-check
- Verify acceptance criteria 1 and 3

### Week 2: OPTION 2 (Quartet Fix as Cross-Check)
**Days 1-2**: Add JP's lemma
- Insert `g_symm_shim` if needed
- Add `ΓΓ_commutator_relabel` with full calc proof
- Verify it compiles independently

**Days 3-4**: Apply to Quartet
- Fix lines 7303 and 7605 using lemma
- Keep gated behind flag/comment
- Verify no regressions

**Day 5**: Cross-Verification
- Compare quartet output with Block C numerically
- Verify acceptance criterion 2
- Document redundancy as verification oracle

---

## Paul's Key Insights

### On Strategy Selection
> "Ship with Block C (OPTION 1), then add JP's lemma to rehabilitate the quartet path (OPTION 2) as a verified alternative."

### On Critical Invariant
> "The only invariant that matters here is that every ΓΓ term sits inside a commutator difference before any lower/raise via g. That ensures you never require [M_μ, M_ν] = 0."

### On Testing
> "Add minimal tests that would have caught the bug... A numeric 'Schwarzschild @ r = 10M' spot-check that LHS ≠ RHS for the false identity."

### On Pitfalls
> "If you see yourself writing ad-hoc rw [sub_eq_add_neg] to make goals line up, pause—you are probably about to reintroduce a sign mistake."

---

## Summary for User

**Path forward is clear**:
1. **Now**: Complete Block C (main_to_commutator already working)
2. **Next**: Finish `expand_P_ab` and Four-Block assembly
3. **Later**: Add JP's quartet fix as verification cross-check

**Key advantage**: Minimizes risk by using proven working code (Block C) for primary path, then adding redundancy for verification.

**No wasted work**:
- Block C already correct ✅
- JP's lemma adds value as correctness oracle ✅
- Quartet code becomes verification tool (not critical path) ✅

---

**Prepared by**: Claude Code (Lean 4 Assistant)
**Date**: October 30, 2025
**Status**: Implementation plan documented - ready to proceed with OPTION 1
**Next action**: Investigate `expand_P_ab` status and complete Four-Block assembly

---

## Appendix: Paul's Full Guidance (Preserved)

[User message preserved as primary reference]

**Key directives**:
1. "Take OPTION 1 now, and stage OPTION 2 as a cross-check once the Four-Block assembly is green."
2. "Ensure sumIdx_swap is stated for your Idx with [Fintype Idx] [DecidableEq Idx]."
3. "Keep ring restricted to scalar ground terms."
4. "Do not orient sumIdx_swap in a way that flips the commutator sign."
5. "Ship with Block C (OPTION 1), then add JP's lemma to rehabilitate the quartet path (OPTION 2) as a verified alternative."
