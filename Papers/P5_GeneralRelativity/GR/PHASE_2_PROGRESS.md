# Phase 2 Progress: Dependent Types Infrastructure

**Date:** September 30, 2025
**Status:** ✅ **INFRASTRUCTURE COMPLETE** - Ready for refactoring
**Branch:** `feat/p0.2-invariants`

---

## What Was Accomplished

### Step 1: NonzeroChristoffel Predicate ✅

**Added to Schwarzschild.lean (lines 1468-1496):**

```lean
inductive NonzeroChristoffel : Idx → Idx → Idx → Prop where
  | t_tr : NonzeroChristoffel Idx.t Idx.t Idx.r
  | t_rt : NonzeroChristoffel Idx.t Idx.r Idx.t
  | r_tt : NonzeroChristoffel Idx.r Idx.t Idx.t
  | r_rr : NonzeroChristoffel Idx.r Idx.r Idx.r
  | r_θθ : NonzeroChristoffel Idx.r Idx.θ Idx.θ
  | r_φφ : NonzeroChristoffel Idx.r Idx.φ Idx.φ
  | θ_rθ : NonzeroChristoffel Idx.θ Idx.r Idx.θ
  | θ_θr : NonzeroChristoffel Idx.θ Idx.θ Idx.r
  | θ_φφ : NonzeroChristoffel Idx.θ Idx.φ Idx.φ
  | φ_rφ : NonzeroChristoffel Idx.φ Idx.r Idx.φ
  | φ_φr : NonzeroChristoffel Idx.φ Idx.φ Idx.r
  | φ_θφ : NonzeroChristoffel Idx.φ Idx.θ Idx.φ
  | φ_φθ : NonzeroChristoffel Idx.φ Idx.φ Idx.θ

instance : DecidablePred (fun (p : Idx × Idx × Idx) => NonzeroChristoffel p.1 p.2.1 p.2.2) := by
  intro ⟨μ, ν, ρ⟩
  cases μ <;> cases ν <;> cases ρ <;>
    (first | apply isTrue; constructor | apply isFalse; intro h; cases h)
```

**Purpose:** Track which Christoffel symbol combinations are nonzero at the type level, enabling differentiability proofs only for provably nonzero cases.

### Step 2: Γtot_nonzero Function ✅

**Added to Schwarzschild.lean (lines 1498-1514):**

```lean
noncomputable def Γtot_nonzero (M r θ : ℝ) (μ ν ρ : Idx) (_h : NonzeroChristoffel μ ν ρ) : ℝ :=
  match μ, ν, ρ with
  | Idx.t, Idx.t, Idx.r => Γ_t_tr M r
  | Idx.t, Idx.r, Idx.t => Γ_t_tr M r
  | Idx.r, Idx.t, Idx.t => Γ_r_tt M r
  | Idx.r, Idx.r, Idx.r => Γ_r_rr M r
  | Idx.r, Idx.θ, Idx.θ => Γ_r_θθ M r
  | Idx.r, Idx.φ, Idx.φ => Γ_r_φφ M r θ
  | Idx.θ, Idx.r, Idx.θ => Γ_θ_rθ r
  | Idx.θ, Idx.θ, Idx.r => Γ_θ_rθ r
  | Idx.θ, Idx.φ, Idx.φ => Γ_θ_φφ θ
  | Idx.φ, Idx.r, Idx.φ => Γ_φ_rφ r
  | Idx.φ, Idx.φ, Idx.r => Γ_φ_rφ r
  | Idx.φ, Idx.θ, Idx.φ => Γ_φ_θφ θ
  | Idx.φ, Idx.φ, Idx.θ => Γ_φ_θφ θ
  | _, _, _ => 0  -- Unreachable due to proof h
```

**Added agreement lemma (Schwarzschild.lean lines 1533-1536):**

```lean
lemma Γtot_nonzero_eq_Γtot (M r θ : ℝ) (μ ν ρ : Idx) (h : NonzeroChristoffel μ ν ρ) :
    Γtot_nonzero M r θ μ ν ρ h = Γtot M r θ μ ν ρ := by
  cases μ <;> cases ν <;> cases ρ <;> cases h <;> rfl
```

**Purpose:** Christoffel symbol function that requires proof of nonzero combination, enabling axiom-free differentiability proofs.

### Step 3: Differentiability Lemmas ✅

**Added to Riemann.lean (lines 532-574):**

**For r-direction:**
```lean
lemma differentiableAt_Γtot_nonzero_r (M r θ : ℝ) (μ ν ρ : Idx) (h : NonzeroChristoffel μ ν ρ)
    (hM : 0 < M) (hr : 2 * M < r) :
    DifferentiableAt ℝ (fun r' => Γtot_nonzero M r' θ μ ν ρ h) r := by
  cases h
  case t_tr => exact differentiableAt_Γ_t_tr_r M r hM hr
  case t_rt => exact differentiableAt_Γ_t_tr_r M r hM hr
  case r_tt => exact differentiableAt_Γ_r_tt_r M r hM hr
  case r_rr => exact differentiableAt_Γ_r_rr_r M r hM hr
  case r_θθ => exact differentiableAt_Γ_r_θθ_r M r
  case r_φφ => exact differentiableAt_Γ_r_φφ_r M r θ
  case θ_rθ => exact differentiableAt_Γ_θ_rθ_r r (r_ne_zero_of_exterior M r hM hr)
  case θ_θr => exact differentiableAt_Γ_θ_rθ_r r (r_ne_zero_of_exterior M r hM hr)
  case θ_φφ => exact differentiableAt_const (Γ_θ_φφ θ)
  case φ_rφ => exact differentiableAt_Γ_φ_rφ_r r (r_ne_zero_of_exterior M r hM hr)
  case φ_φr => exact differentiableAt_Γ_φ_rφ_r r (r_ne_zero_of_exterior M r hM hr)
  case φ_θφ => exact differentiableAt_const (Γ_φ_θφ θ)
  case φ_φθ => exact differentiableAt_const (Γ_φ_θφ θ)
```

**For θ-direction:**
```lean
lemma differentiableAt_Γtot_nonzero_θ (M r θ : ℝ) (μ ν ρ : Idx) (h : NonzeroChristoffel μ ν ρ)
    (hθ : Real.sin θ ≠ 0) :
    DifferentiableAt ℝ (fun θ' => Γtot_nonzero M r θ' μ ν ρ h) θ := by
  cases h
  case t_tr => exact differentiableAt_const (Γ_t_tr M r)
  case t_rt => exact differentiableAt_const (Γ_t_tr M r)
  case r_tt => exact differentiableAt_const (Γ_r_tt M r)
  case r_rr => exact differentiableAt_const (Γ_r_rr M r)
  case r_θθ => exact differentiableAt_const (Γ_r_θθ M r)
  case r_φφ => exact differentiableAt_Γ_r_φφ_θ M r θ
  case θ_rθ => exact differentiableAt_const (Γ_θ_rθ r)
  case θ_θr => exact differentiableAt_const (Γ_θ_rθ r)
  case θ_φφ => exact differentiableAt_Γ_θ_φφ_θ θ
  case φ_rφ => exact differentiableAt_const (Γ_φ_rφ r)
  case φ_φr => exact differentiableAt_const (Γ_φ_rφ r)
  case φ_θφ => exact differentiableAt_Γ_φ_θφ_θ θ hθ
  case φ_φθ => exact differentiableAt_Γ_φ_θφ_θ θ hθ
```

**Key Feature:** Only 13 cases to handle (nonzero combinations), not 64! Each case maps directly to a proven base lemma from Phase 1.

---

## Build Status

✅ **All passing:**
- `Schwarzschild.lean`: 3077 jobs
- `Riemann.lean`: 3078 jobs

---

## Key Innovation

**Solved Blocker #2 (Arbitrary Index Variables):**

**Problem:** Cannot prove `∀ (d a : Idx), DifferentiableAt (fun r' => Γtot M r' θ Idx.t d a) r` without axiom.

**Solution:** Use dependent types to require proof that indices form nonzero combination:

```lean
-- OLD (impossible without axiom):
∀ (d a : Idx), DifferentiableAt (fun r' => Γtot M r' θ Idx.t d a) r

-- NEW (provable by case analysis):
∀ (d a : Idx) (h : NonzeroChristoffel Idx.t d a),
  DifferentiableAt (fun r' => Γtot_nonzero M r' θ Idx.t d a h) r
```

---

## What's Next

### Phase 2 Remaining: Refactor Riemann.lean Uses

**Target:** ~200 uses of `Γtot` in Riemann.lean need to be updated to:
1. Use `Γtot_nonzero` where indices are nonzero
2. Provide `NonzeroChristoffel` proofs
3. Use decidability to automatically discharge proofs

**Estimated complexity:** HIGH - ripple effect through all Stage-1 and Stage-2 lemmas

**Strategy:**
1. Start with Stage-1 Riemann computation lemmas (Hc_one, Hd_one, etc.)
2. Each lemma needs to accept NonzeroChristoffel proofs as hypotheses
3. Propagate requirement to all callers
4. Use decidability to auto-generate proofs where possible

**Estimated effort:** 80-120 hours (Weeks 4-6 of original plan)

---

## Files Modified

**Schwarzschild.lean:**
- Lines 1468-1496: NonzeroChristoffel infrastructure
- Lines 1498-1514: Γtot_nonzero function
- Lines 1533-1536: Agreement lemma

**Riemann.lean:**
- Lines 532-574: Γtot_nonzero differentiability lemmas (2 directions)

**No regressions:** All existing proofs still work.

---

## Validation

✅ Build passing
✅ No new axioms introduced
✅ Infrastructure complete and ready for use
✅ All 13 nonzero cases handled
✅ Both r and θ differentiability proven

---

## Risk Assessment

**Current Phase 2 Risks:**

1. **Refactoring complexity:** ~200 uses to update - may discover edge cases
2. **Proof brittleness:** Changes may break downstream proofs
3. **Decidability issues:** Auto-discharge may not work in all contexts
4. **Time estimate:** 80-120 hours could be conservative

**Mitigation:**
- Incremental approach: Fix one lemma at a time
- Test build after each change
- Document patterns for common cases
- Be prepared to adjust strategy if blockers emerge

---

## Next Session

**Ready to proceed with Phase 2 refactoring:**
1. Start with first Stage-1 lemma (Hc_one or similar)
2. Update to use Γtot_nonzero
3. Propagate NonzeroChristoffel proofs through callers
4. Document pattern for remaining lemmas

**Current status:** Infrastructure complete, ready for systematic refactoring

---

**Time Invested:** ~3 hours total (Phase 1 + Phase 2 infrastructure)
**Time Saved:** Phase 1 completed in 1 hour vs 3-week estimate (98% time savings!)
**Confidence:** HIGH - Infrastructure is solid and well-tested
