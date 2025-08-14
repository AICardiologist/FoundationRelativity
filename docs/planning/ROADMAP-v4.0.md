# Foundation Relativity Roadmap v4.0

**Updated**: August 13, 2025  
**Focus**: Paper 2 - Removing axioms and completing Stone window

## 🎯 Current Status: Post Sprint D - Axiom Removal Phase

### ✅ **COMPLETED**: Core WLPO ↔ BidualGap Theorem
- **Main theorem**: `gap_equiv_wlpo : BidualGapStrong.{0} ↔ WLPO`
- **Axiom profile**: `[propext, Classical.choice, Quot.sound]` + 2 placeholder axioms
- **Forward**: Gap → WLPO via Ishihara's constructive argument (0 sorries)
- **Reverse**: WLPO → Gap via direct construction G = S ∘ Φ₁ (0 sorries)

### ⚠️ **REMAINING**: Two Placeholder Axioms
Current theorem still depends on:
- `dual_is_banach_c0_from_WLPO : WLPO → DualIsBanach c₀`
- `dual_is_banach_c0_dual_from_WLPO : WLPO → DualIsBanach (c₀ →L[ℝ] ℝ)`

---

## What's Left to Formalize (Paper 2 Only)

### A. Remove the Two Placeholder Axioms

**Goal**: Replace both axioms with Lean proofs, keeping constructive shape.

**Primary Strategy**: Isometric identifications
1. `(c₀ →L ℝ) ≃ₗᵢ ℓ¹` via coefficient map `f ↦ (f (e n))`
2. `(ℓ¹ →L ℝ) ≃ₗᵢ ℓ^∞` via bounded multipliers

**Why this fits Paper 2**: DualIsBanach must remain constructive (dependent on WLPO) to make Gap ⇒ WLPO nontrivial. If DualIsBanach were unconditional, WLPO would hold classically (which is wrong).

### B. Stone Window: Finish Boolean Algebra Isomorphism

**Already have**:
- Quotient objects `BooleanAtInfinity`, `SeqModC0`
- Ring/BA structure on quotients
- Embedding `A ↦ [χ_A]`
- Injectivity (`iotaBar_injective`)

**Missing**: Surjectivity onto idempotents of `ℓ^∞/c₀`
- Construct rounding map: `[x̄] ↦ [χ_{n | x̄(n) ≥ 1/2}]`
- Prove well-defined modulo c₀
- Verify inverse on idempotents

### C. (Optional) Universe-Polymorphic Version

Current theorem pinned at `.{0}` (approved by professor). Can generalize later with ULift transport after A & B complete.

---

## Concrete Milestones & Deliverables

### Milestone A1 — Linear Isometry `(c₀ →L ℝ) → ℓ¹`

**Deliverable**:
```lean
def toCoeffs : (c₀ →L[ℝ] ℝ) →ₗᵢ ℓ¹ :=
{ toLinearIsometry := 
    { toLinearMap := { toFun := λ f => fun n => f (e n), ... },
      norm_map' := ... } }
```

**Key lemmas** (already have):
- `summable_abs_eval : Summable (λ n, ‖f (e n)‖)`
- Finite-sum bound from sign-vector test

**Acceptance**: `#print axioms toCoeffs` shows only standard axioms

---

### Milestone A2 — Linear Map `ℓ¹ → (c₀ →L ℝ)` and Isometry

**Deliverable**:
```lean
def ofCoeffs (a : ℓ¹) : c₀ →L[ℝ] ℝ :=
{ toLinearMap := { toFun := λ x => ∑' n, a n * x n, ... },
  cont := ... }

def dual_c0_iso_l1 : (c₀ →L ℝ) ≃ₗᵢ ℓ¹ := 
{ toFun := toCoeffs, invFun := ofCoeffs, ... }
```

**Acceptance**: 
- Two-sided inverse checked
- Norm equalities established
- `#print axioms dual_c0_iso_l1` clean

---

### Milestone A3 — Prove `WLPO → DualIsBanach c₀`

Use isometry to reduce `DualIsBanach c₀` to corresponding property on `ℓ¹`.

```lean
theorem dual_is_banach_c0_from_WLPO (h : WLPO) : DualIsBanach c₀ := by
  -- transport along dual_c0_iso_l1
  -- discharge constructive obligations using h
```

**Acceptance**: Replaces axiom with proof; no new axioms

---

### Milestone B1 — Dual of `ℓ¹` is `ℓ^∞` (Isometry)

**Deliverable**:
```lean
def toBounded (φ : ℓ¹ →L ℝ) : ℕ → ℝ := λ n => φ (e n)
def ofBounded (b : ℓ^∞) : ℓ¹ →L ℝ := λ x => ∑' n, x n * b n

def dual_l1_iso_linf : (ℓ¹ →L ℝ) ≃ₗᵢ ℓ^∞ := ...
```

**Acceptance**: Clean axiom profile; no sorries

---

### Milestone B2 — Prove `WLPO → DualIsBanach (c₀ →L ℝ)`

Combine A2 and B1:
```lean
theorem dual_is_banach_c0_dual_from_WLPO (h : WLPO) : 
  DualIsBanach (c₀ →L ℝ) := by
  -- transport along A2 & B1
  -- discharge constructive obligations via h
```

**Acceptance**: Second axiom removed

---

### Milestone C — Stone Window Surjectivity

**Deliverable**:
```lean
def round : SeqModC0 → BooleanAtInfinity := ...
theorem idempotent_surj :
  ∀ p : Idempotent (ℓ^∞/c₀), ∃ A, p = [χ_A] := ...
```

**Acceptance**: Stone window theorem fully formalized; no sorries

---

### Milestone D — Universe (Optional)

After A & B, add ULift bridge:
```lean
theorem gap_equiv_wlpo : BidualGapStrong ↔ WLPO
```
(no `.{0}`), or document why `.{0}` is intended for Paper 2.

**Acceptance**: Clean CI; theorem matches paper variant

---

## Immediate Action Items (This Week)

### 1. Code Skeletons
Create stubs with precise type signatures and TODO comments:
- [ ] `toCoeffs`, `ofCoeffs`, `dual_c0_iso_l1`
- [ ] `toBounded`, `ofBounded`, `dual_l1_iso_linf`

### 2. Definition Audit of DualIsBanach
- [ ] Confirm what `DualIsBanach` asserts (must be stricter than "complete dual")
- [ ] Write explanation in `Basic.lean` of constructive content WLPO supplies

### 3. Guardrails / CI
- [ ] Add CI job for `#print axioms` on key theorems
- [ ] Add "no sorries" check for HB/ and Gap/ folders

### 4. Documentation Sync
- [ ] Update paper-v4.tex to list two WLPO→DualIsBanach items as pending
- [ ] Add "Note on Universes" above main theorem

---

## Risk Log & Mitigations

### R1: Norm Equality Proofs Get Sticky
**Mitigation**: Reuse signVector lemmas (already proven) for lower bounds; upper bounds straightforward. Keep truncation steps finite.

### R2: Exact Constructive Content of DualIsBanach
**Mitigation**: Document predicate, show which parts follow from WLPO and which are transported by isometries. Refactor if needed for clean transport.

### R3: Stone Rounding Well-Definedness
**Mitigation**: Write lemma "if x−χ_A ∈ c₀ then A determined mod Fin" and mirror existing injectivity proof (ε=1/2 argument).

---

## Acceptance Checklist for Paper 2 (Final)

- [ ] `gap_equiv_wlpo : BidualGapStrong.{0} ↔ WLPO` with no project-level axioms
- [ ] `dual_c0_iso_l1`, `dual_l1_iso_linf` fully proven and axiom-free
- [ ] Stone window theorem surjective (full isomorphism)
- [ ] All active files no sorries
- [ ] CI checks in place
- [ ] Documentation synced

---

## Timeline

### Week 1 (Aug 14-20)
- Create code skeletons for all isometry proofs
- Audit DualIsBanach definition
- Set up CI infrastructure

### Week 2 (Aug 21-27)
- Complete Milestone A1-A2 (c₀ dual isometry)
- Start Milestone B1 (ℓ¹ dual isometry)

### Week 3 (Aug 28-Sep 3)
- Complete Milestone B1-B2
- Remove both axioms
- Start Stone window surjectivity

### Week 4 (Sep 4-10)
- Complete Stone window
- Universe polymorphism (if time)
- Final documentation and CI verification

---

## Success Metrics

- **Primary**: Zero project-level axioms in `gap_equiv_wlpo`
- **Secondary**: Full Stone window isomorphism proven
- **Tertiary**: Universe-polymorphic version (or documented decision to keep `.{0}`)
- **Quality**: All proofs maintainable with clear documentation