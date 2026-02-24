# 10-14 Week Refactor: Detailed Scope Analysis

**Date:** September 30, 2025
**Status:** ⚠️ **SCOPE ASSESSMENT** - Before Commitment
**Estimated Effort:** 10-14 weeks (500-700 hours)

---

## What Would Need to Change

### Phase 1: Christoffel Symbol Differentiability (Weeks 1-3)

**Rigorous proofs for 10 base lemmas (currently sorry):**

```lean
-- Currently:
lemma differentiableAt_Γ_t_tr_r (M r : ℝ) (hM : 0 < M) (hr : 2 * M < r) :
    DifferentiableAt ℝ (fun r' => Γ_t_tr M r') r := by
  sorry -- Explicit rational function, differentiable

-- Would need:
lemma differentiableAt_Γ_t_tr_r (M r : ℝ) (hM : 0 < M) (hr : 2 * M < r) :
    DifferentiableAt ℝ (fun r' => Γ_t_tr M r') r := by
  simp only [Γ_t_tr]  -- M/(r²f(r))
  apply DifferentiableAt.div
  · exact differentiableAt_const _
  · apply DifferentiableAt.mul
    · apply differentiableAt_pow 2
    · -- Need to prove f(r) = 1 - 2M/r is differentiable
      apply DifferentiableAt.sub
      · exact differentiableAt_const _
      · apply DifferentiableAt.div
        · exact differentiableAt_const _
        · exact differentiableAt_id'
        · exact r_ne_zero_of_exterior M r hM hr
  · -- Need to prove r² * f(r) ≠ 0
    have hr0 : r ≠ 0 := r_ne_zero_of_exterior M r hM hr
    have hf : f M r ≠ 0 := ne_of_gt (f_pos_of_hr M r hM hr)
    -- Complex field_simp reasoning
    ...
```

**Estimated:** 2-4 hours per lemma × 10 lemmas = 20-40 hours (Weeks 1-2)

**Plus dependencies:**
- Prove `differentiableAt_f` lemma properly
- Handle all the `field_simp` proofs
- Deal with division-by-zero conditions

**Total Phase 1:** 3 weeks

---

### Phase 2: Index-Specific Γtot Lemmas (Weeks 4-7)

**The Hard Part:** Need differentiability for **ALL** index combinations used in proofs.

**Problem:** Current approach uses arbitrary indices `d`, `a`:
```lean
Γtot M r θ Idx.t d a  -- d, a are variables
```

**Solution Options:**

#### Option 2A: Case Explosion (NOT RECOMMENDED)

Prove differentiability for all 64 combinations:
```lean
lemma differentiableAt_Γtot_t_tt_r : DifferentiableAt_r (fun r θ => Γtot M r θ Idx.t Idx.t Idx.t) ...
lemma differentiableAt_Γtot_t_tt_θ : DifferentiableAt_θ (fun r θ => Γtot M r θ Idx.t Idx.t Idx.t) ...
lemma differentiableAt_Γtot_t_tr_r : DifferentiableAt_r (fun r θ => Γtot M r θ Idx.t Idx.t Idx.r) ...
-- ... 60 more combinations
```

**But most are ZERO!** Would need:
```lean
lemma Γtot_zero_differentiable (μ ν ρ : Idx) (h : Γtot M r θ μ ν ρ = 0) :
    DifferentiableAt ℝ (fun r' => Γtot M r' θ μ ν ρ) r := by
  simp [h]; exact differentiableAt_const _
```

**Circular problem:** How to prove `Γtot M r θ μ ν ρ = 0` for runtime indices μ, ν, ρ?

Need case analysis:
```lean
cases μ <;> cases ν <;> cases ρ
-- 64 cases!
```

**Effort:** 64 cases × 30 min = 32 hours per direction × 2 directions = **64 hours**

---

#### Option 2B: Dependent Types (RECOMMENDED but MAJOR)

**Idea:** Track which Christoffel components are nonzero at the type level.

**Current definition:**
```lean
noncomputable def Γtot (M r θ : ℝ) : Idx → Idx → Idx → ℝ
| Idx.t, Idx.t, Idx.r => Γ_t_tr M r
| Idx.t, Idx.r, Idx.t => Γ_t_tr M r
| ...
| _, _, _ => 0
```

**New approach:**
```lean
-- Define a type for nonzero combinations
inductive NonzeroChristoffel : Idx → Idx → Idx → Prop where
| t_tr : NonzeroChristoffel Idx.t Idx.t Idx.r
| t_rt : NonzeroChristoffel Idx.t Idx.r Idx.t
| r_tt : NonzeroChristoffel Idx.r Idx.t Idx.t
-- ... 13 constructors

-- New Γtot that requires proof of nonzero
def Γtot_nonzero (M r θ : ℝ) (μ ν ρ : Idx) (h : NonzeroChristoffel μ ν ρ) : ℝ :=
  match μ, ν, ρ, h with
  | Idx.t, Idx.t, Idx.r, .t_tr => Γ_t_tr M r
  | ...
```

**Then prove:**
```lean
lemma differentiableAt_Γtot_nonzero (μ ν ρ : Idx) (h : NonzeroChristoffel μ ν ρ) :
    DifferentiableAt ℝ (fun r' => Γtot_nonzero M r' θ μ ν ρ h) r := by
  cases h <;> simp [Γtot_nonzero]
  -- Only 13 cases, all provable!
  case t_tr => exact differentiableAt_Γ_t_tr_r M r hM hr
  case t_rt => exact differentiableAt_Γ_t_tr_r M r hM hr  -- same
  case r_tt => exact differentiableAt_Γ_r_tt_r M r hM hr
  ...
```

**Impact:** MUST REFACTOR ALL USES OF Γtot throughout Riemann.lean

**Estimated effort:**
- Define NonzeroChristoffel: 2 hours
- Refactor Γtot definition: 4 hours
- Update all ~200 uses in Riemann.lean: **80-120 hours** (Weeks 4-6)
- Fix broken proofs: **40-60 hours** (Week 7)

**Total Phase 2 (Option 2B):** 4 weeks

---

### Phase 3: Refactor Stage-1 Lemmas (Weeks 8-10)

**Current:**
```lean
lemma Hc_one :
    dCoord c (fun r θ => Pt M a b d r θ + ...) r θ = ... := by
  simpa using dCoord_mul c (fun r θ => Γtot M r θ Idx.t d a) ...
  --                                                     ^^^ Arbitrary!
```

**New (with dependent types):**
```lean
lemma Hc_one (hd : NonzeroChristoffel Idx.t d a ∨ Γtot M r θ Idx.t d a = 0) :
    dCoord c (fun r θ => Pt M a b d r θ + ...) r θ = ... := by
  cases hd
  case inl h_nonzero =>
    simpa using dCoord_mul_of_diff c (fun r θ => Γtot_nonzero M r θ Idx.t d a h_nonzero) ...
      (by discharge_diff)  -- Now works!
  case inr h_zero =>
    simp [h_zero]  -- Simplify using Γtot = 0
```

**But now ALL callers need to provide `hd` proof!**

**Ripple effect:**
- Hc_one has 5+ callers
- Each caller has 3+ callers
- Exponential propagation

**Estimated effort:**
- Refactor Hc_one, Hd_one, Hc2_one, Hd2_one: 20 hours
- Fix downstream callers: **60-80 hours** (Weeks 8-9)
- Fix downstream-downstream: **40 hours** (Week 10)

**Total Phase 3:** 3 weeks

---

### Phase 4: Delete Axiom & Cleanup (Weeks 11-12)

Once all targeted uses are eliminated:

1. Delete `AX_differentiable_hack` (line 253)
2. Verify builds
3. Fix any residual uses
4. Run `#print axioms` on all theorems
5. Update documentation

**Estimated:** 2 weeks (bugs, edge cases, verification)

---

### Phase 5: Review & Polish (Weeks 13-14)

- Code review
- Performance testing (longer proofs due to case analysis)
- Documentation
- CI cleanup

**Estimated:** 2 weeks

---

## Total Effort Breakdown

| Phase | Description | Weeks | Hours |
|-------|-------------|-------|-------|
| 1 | Prove Christoffel differentiability | 3 | 120 |
| 2 | Dependent types refactor | 4 | 160 |
| 3 | Refactor Stage-1 lemmas | 3 | 120 |
| 4 | Delete axiom & cleanup | 2 | 80 |
| 5 | Review & polish | 2 | 80 |
| **Total** | **Full refactor** | **14** | **560** |

**Assumes:** 40 hours/week dedicated work, no blockers, no scope creep

**Realistic:** 16-20 weeks with interruptions, debugging, unforeseen issues

---

## Risks

### High-Risk Items

1. **Dependent type complexity:** May discover Lean 4 limitations with dependent pattern matching
2. **Performance degradation:** Case analysis on 64 combinations in hot paths
3. **Proof brittleness:** Small changes break many downstream proofs
4. **Scope creep:** Discovering more uses than estimated
5. **Team velocity:** Assumes full-time focus (no other priorities)

### Medium-Risk Items

6. **Mathlib incompatibilities:** Dependent approach may not play well with Mathlib automation
7. **Verification overhead:** More complex proofs = longer CI times
8. **Maintainability:** Future changes become harder

---

## Alternative: Accept Level 2.5

**Comparison:**

| Metric | Level 2.5 | TRUE LEVEL 3 |
|--------|-----------|--------------|
| **Time to publish** | Ready now | +14-20 weeks |
| **Sorries** | 2 quarantined | 0 |
| **Critical path axioms** | 0 ✅ | 0 ✅ |
| **Scientific validity** | Full ✅ | Full ✅ |
| **Maintainability** | Simple | Complex |
| **Publication value** | High | Marginally higher |

---

## Recommendation

**DO NOT pursue 10-14 week refactor** unless:

1. ✅ You have 14-20 weeks available before publication deadline
2. ✅ Achieving TRUE LEVEL 3 is a **hard requirement** from reviewers
3. ✅ You're comfortable with dependent types in Lean 4
4. ✅ Team can dedicate full-time focus (no interruptions)
5. ✅ You accept 30-40% risk of discovering additional blockers

**If ANY of these is ❌, accept Level 2.5.**

---

## Questions for Decision

1. **Timeline:** When is publication deadline? Can you afford 14-20 weeks delay?
2. **Requirements:** Is TRUE LEVEL 3 a hard requirement or nice-to-have?
3. **Resources:** Can you dedicate 500+ hours to this refactor?
4. **Risk tolerance:** Comfortable with 30-40% chance of needing even more time?
5. **Alternative value:** Could those 500 hours produce more impactful new results?

---

**Status:** ⚠️ **AWAITING GO/NO-GO DECISION**

**Recommendation:** **NO-GO** - Accept Level 2.5, publish, consider refactor as post-publication project

**Alternative:** **GO** only if ALL 5 conditions above are met

🎯 **Key Question:** Is TRUE LEVEL 3 worth 3-5 months of work for marginal publication benefit?
