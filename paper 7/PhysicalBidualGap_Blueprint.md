# Lean 4 Formalization Blueprint: Physical Bidual Gap

**Purpose:** This document is a complete specification for formalizing the equivalence between WLPO and non-reflexivity of the trace-class operators S₁(H). It is written for a Lean 4 formalization AI to consume directly.

**Dependency:** This formalization extends the existing `gap_equiv_wlpo` codebase (Lee 2025), which already contains:
- `WLPO` definition as `∀ (α : ℕ → Bool), (∀ n, α n = false) ∨ ¬(∀ n, α n = false)`
- `HasWLPO` typeclass
- `BidualGapStrong.{0} ↔ WLPO` (bidirectional, using c₀/ℓ∞)
- `IshiharaKernel` structure and `kernel_implies_wlpo`
- `gap_implies_wlpo` and `wlpo_implies_gap`
- Infrastructure for ℓ∞, c₀, ℓ¹, canonical embeddings, dual pairings

**What we formalize here:** Four new modules extending the above to S₁(H).

---

## Module 1: `PhysicalBidualGap.ReflexiveDual`

### Mathematical content
**Lemma A.** If X is a reflexive Banach space, then X* is reflexive.

### Lean signature

```lean
import Mathlib.Analysis.NormedSpace.Dual
import Mathlib.Analysis.NormedSpace.BanachSteinhaus

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- The canonical embedding J_X : X → X** -/
noncomputable def canonicalEmbedding (x : X) : NormedSpace.Dual 𝕜 (NormedSpace.Dual 𝕜 X) :=
  { toFun := fun f => f x
    map_add' := fun f g => by simp [ContinuousLinearMap.add_apply]
    map_smul' := fun c f => by simp [ContinuousLinearMap.smul_apply]
    cont := by exact (NormedSpace.Dual.eval 𝕜 X x).cont }

/-- X is reflexive if canonicalEmbedding is surjective -/
def IsReflexive (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (X : Type*) [NormedAddCommGroup X] [NormedSpace 𝕜 X] : Prop :=
  Function.Surjective (canonicalEmbedding (𝕜 := 𝕜) (X := X))

/-- Reflexivity of X implies reflexivity of X* -/
theorem reflexive_dual_of_reflexive
    (hX : IsReflexive 𝕜 X) : IsReflexive 𝕜 (NormedSpace.Dual 𝕜 X) := by
  sorry -- proof below
```

### Proof steps (for the AI to fill `sorry`)

The proof constructs, for any `φ : (NormedSpace.Dual 𝕜 X)**`, an element `f : X*` with `J_{X*}(f) = φ`.

**Step 1.** Define `f : X → 𝕜` by `f x := φ (canonicalEmbedding x)`.

```lean
-- Inside the proof:
intro φ
-- Define f as composition: φ ∘ J_X
let f : NormedSpace.Dual 𝕜 X := φ.comp (canonicalEmbedding)
-- Note: this works because canonicalEmbedding : X →L[𝕜] X** is a bounded linear map,
-- and φ : X** →L[𝕜] 𝕜 is bounded, so f = φ ∘ J_X : X →L[𝕜] 𝕜 is bounded.
```

**Step 2.** Show `canonicalEmbedding f = φ`, i.e., for all `g : X*`, `g(f) = φ(g)`.

```lean
-- Need: ∀ g : X*, (canonicalEmbedding f) g = φ g
-- LHS: (canonicalEmbedding f) g = g f = g (φ ∘ J_X)
-- We use surjectivity of J_X: for any g ∈ X**, ∃ x, J_X(x) = g
-- Wait — g ∈ X*, not X**. We need to show:
--   (J_{X*}(f))(g) = φ(g)
--   i.e., g(f) = φ(g)
-- By definition of f: f(x) = φ(J_X(x)) for all x.
-- So g(f) = ... we need to connect g(f) to φ(g).
-- Use reflexivity: since J_X is surjective, write g = J_X(x_g) ... NO, g ∈ X*, not X**.
-- CORRECT APPROACH: We need φ(g) = g(f) for all g ∈ X*.
-- Since X is reflexive (J_X surjective), for each g* ∈ X** there exists x with J_X(x) = g*.
-- But we're working with g ∈ X*, not X**.
-- Actually the proof is simpler:
use f
ext g  -- suffices to show: (J_{X*}(f))(g) = φ(g)
-- (J_{X*}(f))(g) = g(f)  [by definition of canonical embedding]
-- f(x) = φ(J_X(x))       [by definition of f]
-- So g(f) is a real number. We need g(f) = φ(g).
-- KEY: We use reflexivity to rewrite φ(g).
-- Since J_X is surjective, and φ, g are both continuous linear,
-- it suffices to check on the image of J_X, which is all of X**.
-- But g is in X*, and J_X maps X → X**. These are different levels.
-- THE ACTUAL ARGUMENT:
-- φ is determined by its values on J_X(X) = X** (by surjectivity).
-- For any g ∈ X*: we need φ(g) = g(f).
-- There is no direct way to write g as J_X(something) because g ∈ X*, not X**.
-- Instead: use that J_X is surjective to show f works.
-- For any x ∈ X: f(x) = φ(J_X(x)). So f = φ ∘ J_X as maps X → 𝕜.
-- J_{X*}(f)(g) = g(f) [definition]
-- We want: g(f) = φ(g).
-- Rewrite: g(f) = g(φ ∘ J_X) as a map on X... this doesn't simplify.
-- CORRECT CLEAN ARGUMENT (avoiding confusion):
-- We use the natural transformation property.
-- For any g ∈ X* and any x ∈ X:
--   g(f)(not meaningful — g(f) is g applied to f, but f ∈ X*, g ∈ X*, this is wrong)
-- WAIT: J_{X*}(f) is in X***, and g ∈ X**, so J_{X*}(f)(g) means:
-- No. J_{X*} : X* → (X*)** = X***. And (X*)** eats elements of (X*)* = X**.
-- So J_{X*}(f) : X** → 𝕜, defined by J_{X*}(f)(Ψ) = Ψ(f) for Ψ ∈ X**.
-- We need J_{X*}(f) = φ as elements of X*** = (X*)**.
-- I.e., for all Ψ ∈ X**: J_{X*}(f)(Ψ) = φ(Ψ).
-- J_{X*}(f)(Ψ) = Ψ(f) [definition of canonical embedding]
-- Now use surjectivity: Ψ = J_X(x) for some x.
-- Ψ(f) = J_X(x)(f) = f(x) = φ(J_X(x)) = φ(Ψ). ∎
```

**Clean proof script:**

```lean
theorem reflexive_dual_of_reflexive
    (hX : IsReflexive 𝕜 X) : IsReflexive 𝕜 (NormedSpace.Dual 𝕜 X) := by
  intro φ  -- φ : (X*)** = X***
  -- Construct f := φ ∘ J_X : X → 𝕜, which is in X*
  let f : NormedSpace.Dual 𝕜 X := φ.comp (canonicalEmbeddingCLM)
  -- where canonicalEmbeddingCLM : X →L[𝕜] X** is the bounded version
  use f
  -- Need: J_{X*}(f) = φ, i.e., ∀ Ψ : X**, Ψ(f) = φ(Ψ)
  ext Ψ
  -- Use surjectivity of J_X: obtain x with J_X(x) = Ψ
  obtain ⟨x, hx⟩ := hX Ψ
  -- Ψ(f) = J_X(x)(f) = f(x) = (φ ∘ J_X)(x) = φ(J_X(x)) = φ(Ψ)
  rw [← hx]
  -- Now both sides reduce to φ(J_X(x))
  simp [canonicalEmbedding, f]
```

### Contrapositive (what we actually use)

```lean
/-- If X* is not reflexive, then X is not reflexive -/
theorem not_reflexive_of_dual_not_reflexive
    (h : ¬ IsReflexive 𝕜 (NormedSpace.Dual 𝕜 X)) : ¬ IsReflexive 𝕜 X :=
  fun hX => h (reflexive_dual_of_reflexive hX)
```

### Estimated effort: 50–80 lines

---

## Module 2: `PhysicalBidualGap.ReflexiveSubspace`

### Mathematical content
**Lemma B.** Let X be a separable Banach space and Y ⊆ X a closed subspace. If X is reflexive, then Y is reflexive.

### Critical dependency
This requires the **constructive Hahn-Banach separation theorem for separable spaces**. Check Mathlib for:
- `exists_dual_vector_ne_zero` or similar separation lemma
- `Submodule.exists_dual_annihilator` or `exists_extension_norm_eq`

**If Mathlib has Hahn-Banach extension for separable normed spaces** (which it likely does via `exists_extension_norm_eq` in `Mathlib.Analysis.NormedSpace.HahnBanach.Extension`), we can proceed. The separation version follows: if Y is closed and d(x, Y) > 0, then there exists f ∈ X* with f|_Y = 0 and f(x) = d(x, Y).

### Lean signature

```lean
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension
import Mathlib.Topology.MetricSpace.Basic

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable {Y : Submodule 𝕜 X} [hY : IsClosed (Y : Set X)]

/-- A closed subspace of a separable reflexive Banach space is reflexive -/
theorem reflexive_closedSubspace_of_reflexive
    [TopologicalSpace.SeparableSpace X]
    (hX : IsReflexive 𝕜 X)
    (hYc : IsClosed (Y : Set X)) :
    IsReflexive 𝕜 Y := by
  sorry -- proof below
```

### Proof steps

**Step 1: Lift.** Given φ ∈ Y**, define Φ ∈ X** by Φ(f) = φ(f|_Y).

```lean
intro φ  -- φ : Y**
-- Define restriction map: res : X* → Y*
-- res(f) := f.comp (Submodule.subtypeL Y)  [restriction to Y]
let res : NormedSpace.Dual 𝕜 X →L[𝕜] NormedSpace.Dual 𝕜 Y :=
  ContinuousLinearMap.compL 𝕜 Y X 𝕜 (Submodule.subtypeL Y)
-- Lift: Φ := φ ∘ res : X* → 𝕜
let Φ : NormedSpace.Dual 𝕜 (NormedSpace.Dual 𝕜 X) := φ.comp res
```

**Step 2: Represent.** Since X is reflexive, obtain x with J_X(x) = Φ.

```lean
obtain ⟨x, hx⟩ := hX Φ
-- hx : canonicalEmbedding x = Φ
-- This means: ∀ f : X*, f(x) = Φ(f) = φ(f|_Y)
```

**Step 3: x ∈ Y.** Show d(x, Y) = 0 by contradiction using Hahn-Banach separation.

```lean
-- Claim: x ∈ Y (as a set)
-- Proof by contradiction via separation.
-- Suppose x ∉ Y. Since Y is closed, d(x, Y) > 0.
-- By Hahn-Banach separation (for normed spaces):
--   ∃ f₀ : X*, f₀|_Y = 0, f₀(x) ≠ 0
-- But f₀(x) = Φ(f₀) = φ(f₀|_Y) = φ(0) = 0. Contradiction.
--
-- Formally: we show d(x, Y) ≤ ε for all ε > 0, hence d(x, Y) = 0,
-- hence x ∈ closure(Y) = Y.
--
-- For the separation step, use:
--   Mathlib: `geometric_hahn_banach_closed_point` or
--            `SeparatingDual.exists_ne_zero` or
--            `exists_dual_vector_ne_zero`
--
-- The key Mathlib lemma is likely:
--   `NormedSpace.exists_dual_vector_ne_zero`
--   or the separation from closed convex sets.
--
-- ALTERNATIVE (simpler, avoids full separation):
-- Use `Submodule.exists_dual_annihilator_eq_ker`
-- or work with the quotient X/Y and its dual.

-- Simpler approach via by_contra:
by_contra hxy
push_neg at hxy  -- hxy : x ∉ Y
-- Since Y is closed and x ∉ Y:
have hd : 0 < Metric.infDist x Y := by
  exact Metric.infDist_pos_of_not_mem_closure
    (by rwa [hYc.closure_eq] at hxy)
-- Hahn-Banach: ∃ f₀ annihilating Y with f₀(x) ≠ 0
-- Use: exists_dual_vector' or separation for closed subspaces
obtain ⟨f₀, hf₀_ann, hf₀_x⟩ := sorry -- Hahn-Banach separation
-- hf₀_ann : ∀ y ∈ Y, f₀ y = 0
-- hf₀_x : f₀ x ≠ 0 (or f₀ x = d(x,Y) > 0)
-- But f₀(x) = Φ(f₀) = φ(res f₀) = φ(f₀|_Y) = φ(0) = 0
have : f₀ x = 0 := by
  have := congr_fun (congr_arg DFunLike.coe hx) f₀
  simp [Φ, res, canonicalEmbedding] at this
  rw [this]
  simp [hf₀_ann]  -- f₀|_Y = 0, so res(f₀) = 0, so φ(0) = 0
exact absurd this hf₀_x
```

**Step 3 (alternative, cleaner).** Instead of full separation, note that if x ∈ closure(Y) = Y (since Y closed), we're done. If x ∉ Y, use Hahn-Banach to get a contradiction. The Mathlib API to look for:

```
-- Search Mathlib for:
-- `Submodule.dual_annihilator`
-- `Submodule.exists_norm_eq_infDist`  (might not exist)
-- `geometric_hahn_banach_closed_point`
-- `SeparatingDual`
-- `exists_dual_vector_ne_zero`
```

**Step 4: Verify J_Y(x) = φ.** With x ∈ Y established, show the canonical embedding works.

```lean
-- Now x ∈ Y, so let y : Y := ⟨x, hx_mem⟩
-- For any g : Y*, extend to f : X* (Hahn-Banach extension), then:
--   J_Y(y)(g) = g(y) = f(x) = Φ(f) = φ(f|_Y) = φ(g)
-- (using f|_Y = g by construction of the extension)
let y : Y := ⟨x, hx_mem⟩
use y
ext g
-- Extend g to f ∈ X* with f|_Y = g and ‖f‖ = ‖g‖
obtain ⟨f, hf_ext, hf_norm⟩ := exists_extension_norm_eq Y g
-- g(y) = f(x) = Φ(f) = φ(res f) = φ(g)
calc canonicalEmbedding y g
    = g y := rfl
  _ = f x := by rw [← hf_ext]; rfl
  _ = Φ f := by rw [← congr_fun (congr_arg _ hx) f]; rfl
  _ = φ (res f) := rfl
  _ = φ g := by congr 1; ext ⟨z, hz⟩; exact hf_ext ⟨z, hz⟩
```

### Contrapositive (what we actually use)

```lean
/-- If a closed subspace of a separable Banach space is not reflexive,
    then the ambient space is not reflexive -/
theorem not_reflexive_of_closedSubspace_not_reflexive
    [TopologicalSpace.SeparableSpace X]
    (hYc : IsClosed (Y : Set X))
    (hY : ¬ IsReflexive 𝕜 Y) : ¬ IsReflexive 𝕜 X :=
  fun hX => hY (reflexive_closedSubspace_of_reflexive hX hYc)
```

### Estimated effort: 150–300 lines
The bulk is the Hahn-Banach separation step. If Mathlib's `geometric_hahn_banach_closed_point` or `SeparatingDual` provides what we need, the proof shortens dramatically. The extension step (`exists_extension_norm_eq`) should already be in Mathlib.

---

## Module 3: `PhysicalBidualGap.DiagonalEmbedding`

### Mathematical content
**Lemma C.** ℓ¹ embeds isometrically as a closed subspace of S₁(H).

### Strategy decision: Abstract vs. Concrete

**Option A (Recommended): Abstract.** Avoid defining S₁(H) entirely. Instead, state and use only:

```lean
/-- There exists a separable Banach space X containing ℓ¹ as a closed subspace,
    such that X is not isomorphic to ℓ¹ -/
axiom exists_separable_banach_containing_ell1 :
  ∃ (X : Type) [inst1 : NormedAddCommGroup X] [inst2 : NormedSpace ℝ X]
    [inst3 : CompleteSpace X] [inst4 : TopologicalSpace.SeparableSpace X],
    ∃ (ι : ℓ¹ →L[ℝ] X), Isometry ι ∧ IsClosed (Set.range ι)
```

This is a **mathematical fact** (take X = S₁(ℓ²), the Schatten 1-class). It avoids the massive infrastructure cost of defining trace-class operators in Lean.

**For formalization purposes, this can be stated as an axiom or as a `sorry`-backed lemma, with a comment that the witness is S₁(ℓ²(ℕ)).**

**Option B (Full): Define S₁(H).** This requires Schatten class infrastructure. Check Mathlib for:
- `MeasureTheory.Lp` (won't help directly)
- `Analysis.InnerProductSpace.Schatten` (may not exist yet)

If Schatten classes are not in Mathlib, this is a 1000+ line project on its own. **Strongly recommend Option A.**

### Lean signature (Option A)

```lean
import Mathlib.Analysis.NormedSpace.lpSpace

-- ℓ¹ as lp 1
abbrev ell1 := lp (fun _ : ℕ => ℝ) 1

-- The key fact we need (provable but infrastructure-heavy; accept as axiom for now)
/-- S₁(ℓ²(ℕ)) is a separable Banach space containing ℓ¹ isometrically
    as a closed subspace via diagonal embedding.
    Witness: ι(λ) = Σ λₙ |eₙ⟩⟨eₙ| maps ℓ¹ into trace-class operators. -/
class HasTraceClassContainer where
  X : Type
  [instNAG : NormedAddCommGroup X]
  [instNS : NormedSpace ℝ X]
  [instCS : CompleteSpace X]
  [instSep : TopologicalSpace.SeparableSpace X]
  ι : ell1 →L[ℝ] X
  ι_isometry : Isometry ι
  ι_closedRange : IsClosed (Set.range ι)
```

### Estimated effort
- Option A: 20–30 lines (just the interface + axiom/sorry)
- Option B: 1000+ lines (Schatten class infrastructure)

---

## Module 4: `PhysicalBidualGap.Main`

### Mathematical content
Assemble the chain:
- **Forward:** WLPO → ¬(S₁(H) reflexive)
- **Backward:** S₁(H) non-reflexive (witness) → WLPO

### Lean signature

```lean
import PhysicalBidualGap.ReflexiveDual
import PhysicalBidualGap.ReflexiveSubspace
import PhysicalBidualGap.DiagonalEmbedding
import Lee2025.WLPO_NonReflexive  -- provides gap_equiv_wlpo, HasWLPO, etc.

-- ============================================================
-- FORWARD DIRECTION: WLPO → ¬(S₁(H) reflexive)
-- ============================================================

/-- WLPO implies ℓ∞ is not reflexive (from Lee 2025) -/
-- Already available: wlpo_implies_gap gives ℓ∞ non-reflexive with witness

/-- ℓ∞ not reflexive → ℓ¹ not reflexive (via Lemma A contrapositive) -/
theorem ell1_not_reflexive_of_wlpo (hw : WLPO) : ¬ IsReflexive ℝ ell1 := by
  -- Step 1: WLPO → ℓ∞ not reflexive
  -- From Lee 2025: wlpo_implies_gap gives ∃ witness in (ℓ∞)**\J(ℓ∞)
  -- This means ¬(IsReflexive ℝ ell_infty)
  have h_linf : ¬ IsReflexive ℝ ell_infty := wlpo_implies_ell_infty_not_reflexive hw
  -- Step 2: ℓ∞ = (ℓ¹)*, so if ℓ¹ were reflexive, ℓ∞ would be reflexive (Lemma A)
  -- Contrapositive of reflexive_dual_of_reflexive:
  exact not_reflexive_of_dual_not_reflexive h_linf
  -- NOTE: This requires ℓ∞ ≅ (ℓ¹)* as normed spaces.
  -- Mathlib should have: `lp.dualEquiv` or `lp 1 → (lp ∞).dual` isometry
  -- If not, this isometry is a separate ~100-line lemma.

/-- S₁(H) not reflexive (¬-form) assuming WLPO -/
theorem traceClass_not_reflexive_of_wlpo
    [tc : HasTraceClassContainer] (hw : WLPO) :
    ¬ IsReflexive ℝ tc.X := by
  -- ℓ¹ is not reflexive (from above)
  have h1 : ¬ IsReflexive ℝ ell1 := ell1_not_reflexive_of_wlpo hw
  -- ℓ¹ ↪ X = S₁(H) as closed subspace (from HasTraceClassContainer)
  -- If X were reflexive, ℓ¹ would be reflexive (Lemma B contrapositive)
  exact not_reflexive_of_closedSubspace_not_reflexive
    tc.ι_closedRange
    (by -- show ¬ IsReflexive ℝ (range of ι)
        -- ι is an isometry, so range(ι) ≅ ℓ¹ as Banach spaces
        -- not reflexive transfers through isometric isomorphism
        exact h1 ∘ reflexive_of_isometric_iso tc.ι_isometry)

-- ============================================================
-- BACKWARD DIRECTION: S₁(H) non-reflexive (witness) → WLPO
-- ============================================================

/-- If S₁(H) is non-reflexive (witness form), then WLPO -/
theorem wlpo_of_traceClass_not_reflexive_witness
    [tc : HasTraceClassContainer]
    (h : ∃ Ψ : NormedSpace.Dual ℝ (NormedSpace.Dual ℝ tc.X),
         Ψ ∉ Set.range (canonicalEmbedding (X := tc.X))) :
    WLPO := by
  -- Immediate from Lee 2025: any non-reflexive Banach space implies WLPO
  -- gap_equiv_wlpo.mp applied to ⟨tc.X, _, _, Ψ, hΨ⟩
  exact gap_equiv_wlpo.mp ⟨tc.X, inferInstance, inferInstance, h.choose, h.choose_spec⟩

-- ============================================================
-- COMBINED: The Physical Bidual Gap Theorem
-- ============================================================

/-- Main theorem (¬-form forward, witness-form backward) -/
theorem physical_bidual_gap [tc : HasTraceClassContainer] :
    (WLPO → ¬ IsReflexive ℝ tc.X) ∧
    ((∃ Ψ : (tc.X)**, Ψ ∉ Set.range (canonicalEmbedding (X := tc.X))) → WLPO) :=
  ⟨traceClass_not_reflexive_of_wlpo, wlpo_of_traceClass_not_reflexive_witness⟩
```

### Estimated effort: 50–80 lines (assembly only, assuming modules 1–3 work)

---

## Appendix A: Mathlib API Checklist

Before starting formalization, verify these Mathlib items exist. If any are missing, they become sub-tasks.

| Item | Expected Mathlib location | Priority |
|------|---------------------------|----------|
| Canonical embedding X → X** | `NormedSpace.Dual.eval` | Critical |
| Hahn-Banach extension | `exists_extension_norm_eq` | Critical |
| Hahn-Banach separation (closed subspace) | `geometric_hahn_banach_closed_point` or `SeparatingDual` | Critical |
| ℓ¹ as `lp 1` | `Mathlib.Analysis.NormedSpace.lpSpace` | Critical |
| ℓ∞ as `lp ∞` or `lp ⊤` | Same | Critical |
| (ℓ¹)* ≅ ℓ∞ isometric iso | `lp.dualEquiv` or similar | Important |
| `lp` is separable | Should follow from countable dense subset | Important |
| `lp` is complete | Should be in Mathlib | Important |
| `infDist_pos_of_not_mem_closure` | `Mathlib.Topology.MetricSpace.Basic` | Important |
| Isometric iso preserves reflexivity | May need to prove (~30 lines) | Moderate |

### Mathlib search commands

```lean
#check NormedSpace.Dual
#check ContinuousLinearMap.comp
#check exists_extension_norm_eq
#check Metric.infDist
#check lp
#check TopologicalSpace.SeparableSpace
#check Isometry
```

---

## Appendix B: The Gap (for documentation, not formalization)

The forward direction gives `WLPO → ¬(IsReflexive ℝ S₁(H))`.
The backward direction requires the **witness form**: `∃ Ψ ∈ S₁(H)** \ J(S₁(H))`.

These are not equivalent constructively. The gap is: does WLPO suffice to construct such a witness Ψ? This reduces to whether WLPO implies the existence of a singular functional on ℓ∞ (a bounded finitely additive measure on ℕ that is not σ-additive). Classically this requires BPI. Whether WLPO suffices is an open question.

The contrapositive chain gives ¬∀ but not ∃¬. This is the standard constructive gap between proof by contradiction and direct construction.

---

## Appendix C: Alternative Backward Direction (Calkin Extraction)

This is an independent concrete proof of "singular state on B(H) → WLPO" that avoids invoking Lee's generic theorem. It is **not needed for formalization** (Lee's generic theorem suffices) but is of independent mathematical interest.

### Statement

If there exists a state ω on B(H) with ω(K) = 0 for all compact K, then WLPO holds.

### Proof sketch for formalization

```lean
/-- If a singular state on B(H) exists, WLPO holds.
    Proof: For α : ℕ → Bool, define H_α = diag(max(α 1, ..., α n)).
    In the Calkin algebra B(H)/K(H):
      - If ∀n, α n = false, then H_α = 0, Calkin image is [0]
      - If ∃n₀, α n₀ = true, then H_α - 1 is compact, Calkin image is [1]
    Evaluate μ = ω(H_α). By the two cases, μ ∈ {0, 1}.
    Cotransitivity at 1/2 gives WLPO. -/
theorem wlpo_of_singular_state
    (ω : B_H →L[ℝ] ℝ)
    (hω_state : ω 1 = 1 ∧ ∀ T, 0 ≤ T → 0 ≤ ω T)
    (hω_singular : ∀ K, IsCompact K → ω K = 0) :
    WLPO := by
  intro α
  -- Define H_α
  let H_α : B_H := diag (fun n => Finset.sup (Finset.range (n+1)) (fun i => if α i then 1 else 0))
  -- Evaluate
  let μ := ω H_α
  -- μ ∈ [0, 1] and μ ∈ {0, 1} by case analysis
  -- Use cotransitivity: μ < 1/2 ∨ μ > 1/2
  rcases lt_or_gt_of_ne (ne_of_μ_in_01 μ) with h | h
  · left; exact all_false_of_μ_lt h
  · right; exact not_all_false_of_μ_gt h
```

This is a **separate formalization project** (~200 lines) requiring B(H) and compact operator infrastructure. Not recommended as part of the initial formalization.

---

## Summary: Recommended Formalization Order

| Step | Module | Lines | Dependencies |
|------|--------|-------|-------------|
| 1 | `ReflexiveDual` (Lemma A) | 50–80 | Mathlib dual spaces |
| 2 | `DiagonalEmbedding` (Option A, axiom) | 20–30 | lp spaces |
| 3 | `Main` (backward direction) | 20–30 | Lee 2025 `gap_equiv_wlpo` |
| 4 | `ReflexiveSubspace` (Lemma B) | 150–300 | Hahn-Banach separation |
| 5 | `Main` (forward direction assembly) | 30–50 | Steps 1–4 |

**Total new code: 270–490 lines.**

Steps 1–3 can be done immediately. Step 4 is the bottleneck (Hahn-Banach separation infrastructure). Step 5 is assembly.

The backward direction (Step 3) is trivially a one-liner using Lee's existing `gap_equiv_wlpo`, so it should be formalized first to get a quick publishable result.
