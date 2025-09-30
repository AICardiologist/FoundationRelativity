# Roadmap: True Level 3 Achievement
# Zero Axioms for Axiom Calibration Research

**Date:** September 30, 2025
**Branch Strategy:** `feat/p0.3-level3` (branching from `feat/p0.2-invariants`)
**Target:** Eliminate all 2 remaining axioms + Level 4 audit
**Estimated Duration:** 2-6 weeks (per professor's mandate)
**Mandate:** Required for axiom calibration research (not optional)

---

## Executive Summary

**Current State:** Level 2.5 ✅
- Critical path (Schwarzschild R_μν = 0): 0 axioms ✅
- Infrastructure: 2 axioms (quarantined)
- Publication ready for physics ✅

**Target State:** True Level 3 + Level 4 Audit
- **All code:** 0 axioms ✅ (mandatory)
- **Mathlib dependencies:** Documented ✅ (Level 4b)
- **Axiom calibration:** Ready ✅

**Professor's Mandate:**
> "For rigorous calibration and reverse mathematics, True Level 3 (Zero Axioms)
> is mandatory. Any project-specific axiom, even quarantined in infrastructure,
> pollutes the dependency graph and obscures the minimal foundational requirements."

---

## Strategic Framework

### Level Definitions

| Level | Definition | Status | Purpose |
|-------|------------|--------|---------|
| **Level 2** | Axioms quarantined, critical path clean | ✅ Complete | Physics publication |
| **Level 2.5** | Level 2 + topology infrastructure + clear path | ✅ Complete | Publication ready |
| **Level 3** | Zero project-specific axioms everywhere | 🎯 **Target** | Axiom calibration |
| **Level 4** | Level 3 + Mathlib axiom audit | 🎯 **Target** | Reverse mathematics |

### Level 4 Clarifications (from Professor)

**Level 4a (Constructivity):** NOT REQUIRED
- We assume classical framework
- Accept LEM and Axiom of Choice from Mathlib
- No constructive proof requirements

**Level 4b (Mathlib Audit):** REQUIRED
- Document reliance on Mathlib's foundational axioms
- Use `#print axioms` on final theorems
- Track: `propext`, `funext`, `Quot.sound`, `Classical.choice`

**Level 4c (Meta-theoretic):** NOT REQUIRED
- Proof-theoretic strength analysis not needed
- Ordinal analysis not needed
- Subsystem classification not needed

---

## Technical Solution: The Two Axioms

### Axiom 1: AX_nabla_g_zero (Priority 1 - Topological Blocker)

**Location:** Riemann.lean:1081
**Uses:** 2 (`dCoord_g_via_compat`, `Riemann_swap_a_b`)
**Blocker Type:** Technical (requires topology + filters)
**Estimated Effort:** 1-2 weeks

**Problem:**
```lean
-- CURRENT (axiom):
lemma AX_nabla_g_zero (M r θ : ℝ) (c a b : Idx) : nabla_g M r θ c a b = 0 := sorry

-- WE HAVE:
lemma nabla_g_zero_ext (M r θ : ℝ) (h_ext : Exterior M r θ) (c a b : Idx) :
  nabla_g M r θ c a b = 0  -- ✅ PROVEN on Exterior

lemma isOpen_exterior_set (M : ℝ) (hM : 0 < M) :
  IsOpen {p : ℝ × ℝ | 2 * M < p.1}  -- ✅ PROVEN

-- WE NEED:
-- Prove that ∂/∂r (nabla_g ...) = 0 and ∂/∂θ (nabla_g ...) = 0
```

**Solution Strategy (from Professor):**

Use Mathlib's `Filter.EventuallyEq` + `deriv_congr` infrastructure:

```lean
-- Step 1: General helper lemma (NEW - to be implemented)
lemma deriv_zero_of_locally_zero {f : ℝ → ℝ} {x : ℝ} {U : Set ℝ}
  (hU_open : IsOpen U) (hx : x ∈ U) (hf_zero : ∀ y ∈ U, f y = 0) :
  deriv f x = 0 := by
  -- Uses: eventually_of_mem, deriv_congr, deriv_const
  sorry -- TO BE IMPLEMENTED

-- Step 2: Apply to nabla_g (NEW - to be implemented)
lemma dCoord_nabla_g_zero_ext (M r θ : ℝ) (h_ext : Exterior M r θ) (μ c a b : Idx) :
  dCoord μ (fun r θ => nabla_g M r θ c a b) r θ = 0 := by
  cases μ
  case r =>
    -- Apply deriv_zero_of_locally_zero with U = {r' | r' > 2M}
    -- Use nabla_g_zero_ext to prove f = 0 on U
    sorry -- TO BE IMPLEMENTED
  case θ =>
    -- Apply deriv_zero_of_locally_zero with U = ℝ (univ)
    sorry -- TO BE IMPLEMENTED
  case t | φ => simp [dCoord_t, dCoord_φ]

-- Step 3: Refactor dependents (REFACTOR EXISTING)
lemma Riemann_swap_a_b_ext (M r θ : ℝ) (h_ext : Exterior M r θ) (a b c d : Idx) :
  ... := by
  -- Replace AX_nabla_g_zero with dCoord_nabla_g_zero_ext h_ext
  sorry -- TO BE REFACTORED

lemma dCoord_g_via_compat_ext (M r θ : ℝ) (h_ext : Exterior M r θ) (...) :
  ... := by
  -- Replace AX_nabla_g_zero with dCoord_nabla_g_zero_ext h_ext
  sorry -- TO BE REFACTORED
```

**Success Criterion:**
- [ ] `deriv_zero_of_locally_zero` proven
- [ ] `dCoord_nabla_g_zero_ext` proven (all 4 cases)
- [ ] `Riemann_swap_a_b_ext` refactored (with Exterior hypothesis)
- [ ] `dCoord_g_via_compat_ext` refactored (with Exterior hypothesis)
- [ ] `AX_nabla_g_zero` deleted
- [ ] All downstream code updated to pass `h_ext`

---

### Axiom 2: AX_differentiable_hack (Priority 2 - The Grind)

**Location:** Riemann.lean:221
**Uses:** 8 (in `dCoord_add/sub/mul`)
**Downstream Uses:** ~76 (throughout Riemann.lean)
**Blocker Type:** Arduous work (no technical blocker)
**Estimated Effort:** 2-4 weeks

**Problem:**
```lean
-- CURRENT (axiom):
lemma AX_differentiable_hack (f : ℝ → ℝ) (x : ℝ) : DifferentiableAt ℝ f x := sorry

-- Used in:
lemma dCoord_add (μ : Idx) (f g : ℝ → ℝ → ℝ) (r θ : ℝ) :
  dCoord μ (fun r θ => f r θ + g r θ) r θ = ... := by
  -- Uses AX_differentiable_hack to get differentiability
  sorry

-- WE HAVE (sound alternatives):
lemma dCoord_add_of_diff (μ : Idx) (f g : ℝ → ℝ → ℝ) (r θ : ℝ)
  (hf_r : DifferentiableAt_r f r θ ∨ μ ≠ Idx.r)
  (hg_r : DifferentiableAt_r g r θ ∨ μ ≠ Idx.r)
  (hf_θ : DifferentiableAt_θ f r θ ∨ μ ≠ Idx.θ)
  (hg_θ : DifferentiableAt_θ g r θ ∨ μ ≠ Idx.θ) :
  dCoord μ (fun r θ => f r θ + g r θ) r θ = ... -- ✅ PROVEN
```

**Solution Strategy (from Professor):**

**Option A (Systematic Refactoring) - MANDATED:**

1. **Delete axiom-dependent lemmas:**
   - Delete `AX_differentiable_hack` (line 221)
   - Delete `dCoord_add` (line ~373)
   - Delete `dCoord_sub` (line ~395)
   - Delete `dCoord_mul` (line ~417)

2. **Systematic refactoring (76 uses):**
   - Replace every `rw [dCoord_add]` with `apply dCoord_add_of_diff`
   - Supply required hypotheses at each call site
   - Propagate hypotheses up the call chain as needed

3. **Automated hypothesis discharge (efficiency strategy):**

```lean
-- BEFORE (with axiom):
rw [dCoord_add c (fun r θ => g M μ a r θ) (fun r θ => g M μ b r θ) r θ]

-- AFTER (with hypotheses):
apply dCoord_add_of_diff c (fun r θ => g M μ a r θ) (fun r θ => g M μ b r θ) r θ
all_goals {
  -- Automated hypothesis discharge
  try {
    simp only [DifferentiableAt_r, DifferentiableAt_θ,
               differentiableAt_g_tt_r, differentiableAt_g_rr_r,
               differentiableAt_g_θθ_r, differentiableAt_g_φφ_r,
               differentiableAt_g_tt_θ, differentiableAt_g_rr_θ,
               differentiableAt_g_θθ_θ, differentiableAt_g_φφ_θ,
               DifferentiableAt.add, DifferentiableAt.mul,
               DifferentiableAt.comp, DifferentiableAt.const_mul,
               differentiableAt_sin, differentiableAt_const]
  }
  -- If differentiability fails, prove direction mismatch (μ ≠ Idx.r, etc.)
  try { simp }
}
```

**Success Criterion:**
- [ ] All 6 metric differentiability lemmas accessible (DONE ✅)
- [ ] Automated tactic for hypothesis discharge developed
- [ ] All 76 call sites refactored with automated discharge
- [ ] `dCoord_add/sub/mul` deleted
- [ ] `AX_differentiable_hack` deleted
- [ ] Riemann.lean builds with 0 errors

---

## Prioritized Action Plan

### 🎯 Priority 1: Eliminate AX_nabla_g_zero (Weeks 1-2)

**Why First:** Technical blocker requires careful topology work

**Tasks:**

| # | Task | Estimated | Success Check |
|---|------|-----------|---------------|
| 1.1 | Implement `deriv_zero_of_locally_zero` | 2 days | Lemma proven, builds |
| 1.2 | Implement `dCoord_nabla_g_zero_ext` (μ=r case) | 1 day | r-derivative case proven |
| 1.3 | Implement `dCoord_nabla_g_zero_ext` (μ=θ case) | 1 day | θ-derivative case proven |
| 1.4 | Implement `dCoord_nabla_g_zero_ext` (μ=t,φ cases) | 2 hours | Trivial cases done |
| 1.5 | Refactor `dCoord_g_via_compat` → `_ext` | 1 day | Add Exterior hypothesis |
| 1.6 | Refactor `Riemann_swap_a_b` → `_ext` | 1 day | Add Exterior hypothesis |
| 1.7 | Update all downstream calls to pass `h_ext` | 2-3 days | All call sites updated |
| 1.8 | Delete `AX_nabla_g_zero` | 1 hour | Builds with 0 errors |
| 1.9 | Verify Schwarzschild.lean still axiom-free | 1 hour | 0 axioms ✅ |

**Deliverable:** `AX_nabla_g_zero` eliminated ✅

---

### 🎯 Priority 2: Eliminate AX_differentiable_hack (Weeks 3-5)

**Why Second:** Arduous but straightforward, no technical blocker

**Tasks:**

| # | Task | Estimated | Success Check |
|---|------|-----------|---------------|
| 2.1 | Develop automated hypothesis discharge tactic | 2 days | Tactic works on sample |
| 2.2 | Audit all 76 downstream uses | 1 day | Complete usage map |
| 2.3 | Refactor batch 1 (Stage-1 LHS, ~20 uses) | 3 days | Batch 1 builds |
| 2.4 | Refactor batch 2 (Stage-1 RHS, ~20 uses) | 3 days | Batch 2 builds |
| 2.5 | Refactor batch 3 (Riemann computation, ~20 uses) | 3 days | Batch 3 builds |
| 2.6 | Refactor batch 4 (Infrastructure, ~16 uses) | 2 days | Batch 4 builds |
| 2.7 | Delete `dCoord_add/sub/mul` (axiom versions) | 1 hour | Deleted |
| 2.8 | Delete `AX_differentiable_hack` | 1 hour | Deleted |
| 2.9 | Full build verification | 1 day | Riemann.lean builds |
| 2.10 | Verify Schwarzschild.lean still axiom-free | 1 hour | 0 axioms ✅ |

**Deliverable:** `AX_differentiable_hack` eliminated ✅

---

### 🎯 Priority 3: Level 4b Audit (Week 6)

**Why Last:** Can only be done once Level 3 achieved

**Tasks:**

| # | Task | Estimated | Success Check |
|---|------|-----------|---------------|
| 3.1 | `#print axioms Ricci_tt_vanishes` | 30 min | Mathlib axioms listed |
| 3.2 | `#print axioms Ricci_rr_vanishes` | 30 min | Mathlib axioms listed |
| 3.3 | `#print axioms Ricci_θθ_vanishes` | 30 min | Mathlib axioms listed |
| 3.4 | `#print axioms Ricci_φφ_vanishes` | 30 min | Mathlib axioms listed |
| 3.5 | `#print axioms Ricci_scalar_vanishes` | 30 min | Mathlib axioms listed |
| 3.6 | Consolidate axiom dependencies | 1 day | Complete audit table |
| 3.7 | Document in LEVEL_4_AXIOM_AUDIT.md | 1 day | Documentation complete |
| 3.8 | Professor review of axiom audit | - | Approval ✅ |

**Expected Mathlib Axioms:**
- `propext` (Propositional extensionality)
- `funext` (Function extensionality)
- `Quot.sound` (Quotient soundness)
- `Classical.choice` (Axiom of Choice)

**Deliverable:** Complete Mathlib axiom dependency documentation ✅

---

## Branch and PR Strategy

### Branch Structure

```
main
 └── feat/p0.2-invariants (PR #218 - Level 2.5) ← CURRENT
      └── feat/p0.3-level3-priority1 (AX_nabla_g_zero elimination)
           └── feat/p0.3-level3-priority2 (AX_differentiable_hack elimination)
                └── feat/p0.3-level3-audit (Level 4b audit)
```

### PR Sequence

**PR #219: Priority 1 - Topology Blocker Elimination**
- Branch: `feat/p0.3-level3-priority1`
- Base: `feat/p0.2-invariants`
- Content:
  - `deriv_zero_of_locally_zero` implementation
  - `dCoord_nabla_g_zero_ext` implementation
  - `Riemann_swap_a_b_ext` refactoring
  - `dCoord_g_via_compat_ext` refactoring
  - Deletion of `AX_nabla_g_zero`
- Success: 1 axiom eliminated, builds clean

**PR #220: Priority 2 - Differentiability Grind**
- Branch: `feat/p0.3-level3-priority2`
- Base: `feat/p0.3-level3-priority1`
- Content:
  - Automated hypothesis discharge tactic
  - Systematic refactoring of 76 uses
  - Deletion of `dCoord_add/sub/mul`
  - Deletion of `AX_differentiable_hack`
- Success: 0 axioms remaining, True Level 3 ✅

**PR #221: Level 4b - Axiom Audit**
- Branch: `feat/p0.3-level3-audit`
- Base: `feat/p0.3-level3-priority2`
- Content:
  - `#print axioms` analysis for all 5 Ricci theorems
  - LEVEL_4_AXIOM_AUDIT.md documentation
  - Dependency graph visualization
- Success: Complete Mathlib axiom dependency documentation

---

## Quality Gates

### Continuous Requirements (Every PR)

- [ ] **Builds:** `lake build Papers.P5_GeneralRelativity.GR.Riemann` succeeds
- [ ] **Critical path:** Schwarzschild.lean remains 0 axioms, 0 sorries
- [ ] **No regressions:** All existing proofs still valid
- [ ] **Documentation:** Changes documented in commit messages

### Milestone Gates

**After Priority 1:**
- [ ] `AX_nabla_g_zero` deleted
- [ ] 1 axiom remaining
- [ ] `grep "^lemma AX_" Riemann.lean` shows only `AX_differentiable_hack`

**After Priority 2 (TRUE LEVEL 3 ACHIEVED):**
- [ ] `AX_differentiable_hack` deleted
- [ ] 0 project-specific axioms
- [ ] `grep "^lemma AX_\|^axiom" Riemann.lean` returns 0 matches
- [ ] `grep -r "sorry" Papers/P5_GeneralRelativity/GR/Riemann.lean` shows only comments
- [ ] Critical path verification: `#print axioms Ricci_scalar_vanishes` shows ONLY Mathlib axioms

**After Priority 3 (LEVEL 4 COMPLETE):**
- [ ] Mathlib axiom audit complete
- [ ] Dependency graph documented
- [ ] LEVEL_4_AXIOM_AUDIT.md approved by professor

---

## Risk Assessment and Mitigation

### Risk 1: Topology Lemma Complexity
**Risk:** `deriv_zero_of_locally_zero` harder than expected
**Probability:** Medium
**Impact:** High (blocks Priority 1)
**Mitigation:**
- Professor provided exact implementation strategy
- Mathlib has `deriv_congr` and `eventually_of_mem`
- Fallback: Ask professor for Mathlib lemma reference

### Risk 2: Refactoring Cascade
**Risk:** 76 uses create unpredictable hypothesis propagation
**Probability:** High
**Impact:** Medium (extends timeline)
**Mitigation:**
- Automated hypothesis discharge tactic (professor's strategy)
- Batch refactoring with incremental testing
- Already have all 6 concrete differentiability lemmas

### Risk 3: Performance Degradation
**Risk:** Explicit hypotheses slow down elaboration
**Probability:** Low
**Impact:** Low
**Mitigation:**
- Use `simp only` (not `simp`) for precise discharge
- Monitor heartbeat limits
- Optimize tactic if needed

### Risk 4: Downstream Breakage
**Risk:** Schwarzschild.lean or other files affected
**Probability:** Very Low
**Impact:** High (breaks critical path)
**Mitigation:**
- Schwarzschild.lean doesn't import Riemann.lean ✅
- Infrastructure changes are additive (_ext versions)
- Continuous CI testing

---

## Success Metrics

### Quantitative Targets

| Metric | Current | Target | Verification |
|--------|---------|--------|--------------|
| Project axioms | 2 | 0 | `grep "^lemma AX_\|^axiom" *.lean` |
| Critical path axioms | 0 | 0 | `#print axioms Ricci_scalar_vanishes` |
| Sorries (active) | 2 | 2 | Deferred infrastructure OK |
| Sorries (total) | 17 | 17 | Unchanged |
| Build errors | 0 | 0 | `lake build` succeeds |
| Mathlib axioms documented | - | 4+ | LEVEL_4_AXIOM_AUDIT.md |

### Qualitative Targets

- [ ] **Axiom calibration ready:** Can measure minimal axiom requirements
- [ ] **Reverse mathematics ready:** Can classify theorem strength
- [ ] **Publication ready:** Physics + foundations both rigorous
- [ ] **Professor approval:** Strategic direction confirmed

---

## Timeline Summary

**Optimistic:** 4 weeks
- Priority 1: 1.5 weeks
- Priority 2: 2 weeks
- Priority 3: 0.5 weeks

**Realistic:** 5 weeks
- Priority 1: 2 weeks
- Priority 2: 2.5 weeks
- Priority 3: 0.5 weeks

**Conservative:** 6 weeks
- Priority 1: 2.5 weeks (topology challenges)
- Priority 2: 3 weeks (refactoring cascades)
- Priority 3: 0.5 weeks

**Professor's Estimate:** 2-6 weeks ✅ (aligns with our assessment)

---

## Communication Protocol

### Weekly Updates to Professor

**Every Monday:**
- Progress summary (tasks completed vs. planned)
- Blockers encountered (if any)
- Week ahead plan
- Any strategic questions

### Consultation Triggers

**Immediate consultation needed if:**
- `deriv_zero_of_locally_zero` proof stuck > 2 days
- Refactoring reveals architectural issue
- Performance degradation > 2x slower
- Unexpected axiom dependency discovered

### Documentation Checkpoints

**After Priority 1:**
- PRIORITY1_COMPLETION_REPORT.md

**After Priority 2:**
- LEVEL3_ACHIEVEMENT_REPORT.md

**After Priority 3:**
- LEVEL_4_AXIOM_AUDIT.md

---

## Next Immediate Actions

### This Week (Week 1)

**Monday-Tuesday:**
1. Wait for PR #218 CI to pass ✅
2. Merge PR #218 (Level 2.5 complete)
3. Create branch `feat/p0.3-level3-priority1`
4. Set up development environment for topology work

**Wednesday-Friday:**
5. Implement `deriv_zero_of_locally_zero` (Priority 1.1)
6. Test on simple cases
7. Begin `dCoord_nabla_g_zero_ext` (μ=r case, Priority 1.2)

**Weekend:**
8. Complete `dCoord_nabla_g_zero_ext` (all cases, Priority 1.2-1.4)
9. Prepare Week 2 refactoring work

### Week 2

**Focus:** Complete Priority 1
- Refactor `Riemann_swap_a_b_ext` and `dCoord_g_via_compat_ext`
- Update all downstream call sites
- Delete `AX_nabla_g_zero`
- Open PR #219

**Target:** 1 axiom eliminated by end of Week 2

---

## Appendix A: Professor's Key Quotes

> "For rigorous calibration and reverse mathematics, True Level 3 (Zero Axioms)
> is mandatory (Q3a)."

> "We mandate the investment of the necessary time (estimated 2-6 weeks) to
> achieve True Level 3 (Q4a, Q5a)."

> "Option A (Systematic Refactoring, the 'Grind') is mandatory. The
> hypothesis-carrying infrastructure (_of_diff lemmas) is the correct architecture."

> "This plan achieves True Level 3, satisfying the requirements for axiom
> calibration research. Proceed immediately with Priority 1."

---

## Appendix B: Technical Reference

### Mathlib Infrastructure (for Priority 1)

```lean
-- From Mathlib.Analysis.Calculus.Deriv.Basic
theorem deriv_congr {f g : ℝ → ℝ} {x : ℝ} (h : f =ᶠ[𝓝 x] g) : deriv f x = deriv g x

-- From Mathlib.Topology.Basic
theorem eventually_of_mem {α : Type*} {f : Filter α} {P : α → Prop} {s : Set α}
  (hs : s ∈ f) (hp : ∀ x ∈ s, P x) : ∀ᶠ x in f, P x

-- From Mathlib.Analysis.Calculus.Deriv.Basic
@[simp] theorem deriv_const (c : ℝ) : deriv (fun _ : ℝ => c) = fun _ => 0
```

### Existing Infrastructure (for Priority 2)

```lean
-- Already implemented ✅
lemma DifferentiableAt_r (f : ℝ → ℝ → ℝ) (r θ : ℝ) : Prop := ...
lemma DifferentiableAt_θ (f : ℝ → ℝ → ℝ) (r θ : ℝ) : Prop := ...

-- Already proven ✅
lemma differentiableAt_g_tt_r (M r θ : ℝ) : DifferentiableAt_r (g M Idx.t Idx.t) r θ
lemma differentiableAt_g_rr_r (M r θ : ℝ) : DifferentiableAt_r (g M Idx.r Idx.r) r θ
lemma differentiableAt_g_θθ_r (M r θ : ℝ) : DifferentiableAt_r (g M Idx.θ Idx.θ) r θ
lemma differentiableAt_g_φφ_r (M r θ : ℝ) : DifferentiableAt_r (g M Idx.φ Idx.φ) r θ
lemma differentiableAt_g_tt_θ (M r θ : ℝ) : DifferentiableAt_θ (g M Idx.t Idx.t) r θ
lemma differentiableAt_g_rr_θ (M r θ : ℝ) : DifferentiableAt_θ (g M Idx.r Idx.r) r θ
```

---

**Status:** ✅ ROADMAP READY
**Approval:** Awaiting professor confirmation
**Next Action:** Wait for PR #218 merge, then begin Priority 1

🎯 **Target:** True Level 3 + Level 4 Audit in 4-6 weeks
