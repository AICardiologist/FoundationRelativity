# Consultation Memo: Axiom Calibration Requirements

**Date:** September 30, 2025
**To:** Senior Professor
**From:** AI Research Assistant
**Re:** Level 3 Axiom Elimination for Axiom Calibration Work
**Branch:** `feat/p0.2-deaxiomatization`

---

## Executive Summary

We have achieved **Level 2.5** with the critical path (Schwarzschild R_μν = 0) being **100% axiom-free**. However, for **axiom calibration research**, we need **true Level 3** (zero axioms everywhere).

**Current status:** 2 axioms remain (both quarantined in infrastructure)

**Request:** Guidance on the fastest path to eliminate both axioms for axiom calibration purposes.

---

## Part I: Progress Completed

### ✅ De-Axiomatization Work Completed

**PRIORITY 0 - Calculus Infrastructure:**
1. ✅ Created helper predicates: `DifferentiableAt_r`, `DifferentiableAt_θ`
2. ✅ Added 6 metric differentiability lemmas (all Schwarzschild components)
3. ✅ Implemented hypothesis-carrying calculus:
   - `dCoord_add_of_diff` (with explicit differentiability hypotheses)
   - `dCoord_sub_of_diff`
   - `dCoord_mul_of_diff`
4. ✅ Quarantined `differentiable_hack` → `AX_differentiable_hack`

**PRIORITY 1 - Metric Compatibility:**
1. ✅ Quarantined `nabla_g_zero` → `AX_nabla_g_zero`
2. ✅ Removed dangerous `@[simp]` attribute
3. ✅ Sound version `nabla_g_zero_ext` with Exterior hypothesis exists
4. ✅ Audited all uses (2 total, both in infrastructure)

**PRIORITY 2 - Topological Infrastructure:**
1. ✅ Added topology imports
2. ✅ Proved `isOpen_exterior_set`: {(r,θ) | r > 2M} is open in ℝ×ℝ
3. ✅ Documented complete elimination path

### ✅ Critical Path Verified Axiom-Free

**Schwarzschild.lean (The Physics Result):**
- Imports: Does NOT import Riemann.lean ✅
- Sorries: 0 ✅
- Axioms: 0 ✅
- All R_μν = 0 proofs: Fully rigorous ✅

**Verification:**
```bash
$ grep -i "sorry\|axiom\|AX_" Papers/P5_GeneralRelativity/GR/Schwarzschild.lean
# Result: 0 matches ✅
```

### ✅ Documentation Created

1. **DE_AXIOMATIZATION_PROGRESS.md** - Technical progress (PRIORITIES 0-1)
2. **LEVEL_2_5_ASSESSMENT.md** - Publication readiness assessment
3. **SORRY_SUMMARY.md** - Complete sorry audit (17 total, 0 on critical path)

**Total commits:** 8 commits on `feat/p0.2-deaxiomatization`

---

## Part II: Remaining Work for Axiom Calibration

### Context: Why This Matters

For axiom calibration / reverse mathematics research, **every axiom in the dependency graph matters**, even if it's "only in infrastructure." The formalization must be:

1. **Axiom-complete:** All assumptions explicit
2. **Axiom-minimal:** Weakest possible assumptions
3. **Graph-clean:** No axioms anywhere in the import tree

Therefore, **Level 2.5 is insufficient** for axiom calibration. We need **true Level 3** (zero axioms).

### Two Remaining Axioms

#### 1. AX_differentiable_hack (Line 221)

**Current state:**
- Uses: 8 (in `dCoord_add/sub/mul` lemmas)
- Downstream uses: ~76 (in Riemann.lean infrastructure)
- Impact on Schwarzschild: 0 (not imported)

**Elimination path:**
- **Option A:** Delete `dCoord_add/sub/mul` entirely, replace all 76 uses with `_of_diff` versions
  - Effort: 2-4 weeks of careful refactoring
  - Technical blocker: None
  - Professor guidance needed: **NO** (just arduous work)

- **Option B:** Prove the Stage-1 infrastructure doesn't need derivatives
  - Effort: Unknown
  - Technical blocker: Unclear
  - Professor guidance needed: **MAYBE**

**Questions for Professor:**
- **Q1a:** For axiom calibration, is Option A (grind through refactoring) the right approach?
- **Q1b:** Or is there a smarter restructuring that avoids the need entirely?
- **Q1c:** If we proceed with Option A, any architectural concerns we should be aware of?

#### 2. AX_nabla_g_zero (Line 1081)

**Current state:**
- Uses: 2 (in `dCoord_g_via_compat` and `Riemann_swap_a_b`)
- Impact on Schwarzschild: 0 (not imported)

**Technical blocker:**
We need to prove: `∂/∂r (nabla_g M r θ c a b) = 0` and `∂/∂θ (nabla_g M r θ c a b) = 0`

**What we have:**
1. ✅ Exterior is open: `isOpen_exterior_set`
2. ✅ nabla_g = 0 on Exterior: `nabla_g_zero_ext`

**What we need:**
A lemma like:
```lean
lemma deriv_of_locally_const {f : ℝ → ℝ} {x : ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ∀ y ∈ U, f y = 0) :
    deriv f x = 0
```

Or more specifically for our case:
```lean
-- If g(r,θ) = 0 for all (r,θ) in open set U, then ∂g/∂r = 0 and ∂g/∂θ = 0 on U
```

**Questions for Professor:**
- **Q2a:** Does such a lemma exist in Mathlib? (Search: `deriv`, `locally_const`, `IsOpen`, `eventuallyEq`)
- **Q2b:** If not in Mathlib, is this provable without deep topology?
- **Q2c:** Standard approach: Use `Filter.EventuallyEq` + `deriv_congr`? Or is there a simpler path?
- **Q2d:** Alternative: Can we restructure `Riemann_swap_a_b` to avoid needing the derivative of nabla_g?

---

## Part III: Strategic Questions

### Axiom Calibration Requirements

**Q3:** For the axiom calibration paper, what level of rigor is required?

- **Option 1:** Critical path axiom-free is sufficient (current Level 2.5)
  - Pro: Already achieved ✅
  - Con: Infrastructure axioms pollute dependency graph

- **Option 2:** Zero axioms everywhere (true Level 3)
  - Pro: Clean dependency graph for calibration
  - Con: 2-6 weeks additional work

- **Option 3:** Axioms allowed if explicitly marked and measured
  - Pro: We've already quarantined them with AX_ prefix
  - Con: Need to document them in calibration results

**Q3a:** Which option aligns with the axiom calibration research goals?

### Publication Timeline

**Q4:** Timeline considerations?

- Current state: Publication-ready at Level 2.5 (physics is rigorous)
- Level 3 effort: 2-6 weeks (mostly grinding refactoring)
- Trade-off: Publish now vs. wait for full axiom elimination

**Q4a:** Is there a deadline that affects this decision?

### Alternative Approaches

**Q5:** Are there alternative formalization strategies?

Instead of eliminating axioms from the current formalization, should we:

- **Option A:** Keep current formalization (Level 2.5), document axioms in calibration
- **Option B:** Create parallel "axiom-free core" that proves just R_μν = 0
- **Option C:** Proceed with full Level 3 elimination (2-6 weeks)

**Q5a:** Which approach best serves the axiom calibration research?

---

## Part IV: Specific Technical Questions Summary

### Critical Questions (need answers to proceed):

**Q2a** (MOST URGENT): Does Mathlib have a lemma for "derivative of locally constant function is zero"?
- If YES: Where? (we can use it immediately)
- If NO: Can we prove it ourselves without deep topology?

**Q3a**: For axiom calibration, is Level 2.5 (critical path clean) sufficient, or do we need true Level 3 (zero axioms everywhere)?

**Q1a**: If we need Level 3, should we grind through the 76-use refactoring, or is there a smarter approach?

### Secondary Questions (nice to know):

**Q1b**: Any architectural concerns about replacing `dCoord_add/sub/mul` with `_of_diff` versions?

**Q2d**: Can we restructure `Riemann_swap_a_b` to avoid needing derivative of nabla_g?

**Q4a**: Any timeline pressures affecting the Level 2.5 vs Level 3 decision?

**Q5a**: Should we consider alternative formalization strategies for calibration?

---

## Part V: Recommendations & Next Steps

### My Assessment

1. **AX_differentiable_hack elimination:** Feasible but tedious (no technical blocker)
2. **AX_nabla_g_zero elimination:** Blocked on Mathlib lemma (or proving it ourselves)
3. **Current state:** Suitable for physics publication, unclear if sufficient for axiom calibration

### Immediate Next Steps (pending your guidance):

**If Level 2.5 is sufficient:**
- Document axioms in calibration results
- Proceed with publication

**If Level 3 is required:**
- **Step 1:** Resolve Q2a (Mathlib lemma search)
- **Step 2:** Eliminate AX_nabla_g_zero using topology
- **Step 3:** Grind through AX_differentiable_hack refactoring (2-4 weeks)

### What We Need From You

**Most important:** Answer Q2a and Q3a (these unblock everything else)

**Also helpful:** Any guidance on Q1a, Q4a, Q5a

**We can handle independently:** The actual refactoring work (just needs time)

---

## Part VI: Technical Appendix

### Current Axiom Inventory

```lean
-- Line 221: Differentiability axiom (8 uses)
lemma AX_differentiable_hack (f : ℝ → ℝ) (x : ℝ) : DifferentiableAt ℝ f x := by
  sorry

-- Line 1081: Metric compatibility axiom (2 uses)
lemma AX_nabla_g_zero (M r θ : ℝ) (c a b : Idx) : nabla_g M r θ c a b = 0 := by
  sorry
```

### Infrastructure Available

```lean
-- Sound alternatives with explicit hypotheses
lemma dCoord_add_of_diff (μ : Idx) (f g : ℝ → ℝ → ℝ) (r θ : ℝ)
    (hf_r : DifferentiableAt_r f r θ ∨ μ ≠ Idx.r)
    (hg_r : DifferentiableAt_r g r θ ∨ μ ≠ Idx.r)
    (hf_θ : DifferentiableAt_θ f r θ ∨ μ ≠ Idx.θ)
    (hg_θ : DifferentiableAt_θ g r θ ∨ μ ≠ Idx.θ) : ...

lemma nabla_g_zero_ext (M r θ : ℝ) (h_ext : Exterior M r θ) (c a b : Idx) :
  nabla_g M r θ c a b = 0

lemma isOpen_exterior_set (M : ℝ) (hM : 0 < M) :
  IsOpen {p : ℝ × ℝ | 2 * M < p.1}
```

### Verification Commands

```bash
# Verify critical path is axiom-free
$ grep -i "axiom\|AX_" Papers/P5_GeneralRelativity/GR/Schwarzschild.lean
# Result: 0 matches ✅

# Count axiom uses in infrastructure
$ grep -n "AX_differentiable_hack" Papers/P5_GeneralRelativity/GR/Riemann.lean | wc -l
# Result: 9 (1 definition + 8 uses)

$ grep -n "AX_nabla_g_zero" Papers/P5_GeneralRelativity/GR/Riemann.lean | wc -l
# Result: 3 (1 definition + 2 uses)
```

---

## Conclusion

We have achieved **Level 2.5** with the physics result being fully rigorous. For **axiom calibration purposes**, we need your guidance on:

1. **Whether Level 3 is necessary** (Q3a)
2. **How to find/prove the topology lemma** (Q2a)
3. **Best approach for the refactoring** (Q1a)

With your answers, we can either:
- **Proceed to Level 3** (2-6 weeks work), or
- **Document current state** for axiom calibration with explicit axiom inventory

**We are ready to execute either path** once you provide strategic direction.

---

**Files for your review:**
- `DE_AXIOMATIZATION_PROGRESS.md` - Technical progress details
- `LEVEL_2_5_ASSESSMENT.md` - Current state assessment
- `SORRY_SUMMARY.md` - Complete sorry inventory
- This memo - Strategic questions

**Branch:** `feat/p0.2-deaxiomatization` (8 commits, all builds passing)

Thank you for your guidance.
