# PR Templates for Riemann Activation

## PR-A — LHS activation scaffolding (no math change)

**Title:** P5/GR: Stage-1 LHS split scaffolding (mode=stage1-lhs-both, baseline-neutral)

### Checklist (DoD)
- [ ] Marker set via `./scripts/set-activation.sh stage1-lhs-both`
- [ ] Add local `sumIdx_expand_local` inside c/d split sections (no global `[simp]`)
- [ ] Use `dCoord_sumIdx_via_local_expand` → `dCoord_add4_flat` to show the 4-term linearity bridge
- [ ] Keep Stage-1 facts outside main proof (unchanged)
- [ ] `make audit` ✅; `make baseline` ✅ (still 51)
- [ ] PR template (Paper 5 section) boxes checked

### Verification output
```
$ make check
✅ ACTIVATION_STATUS OK (stage1-lhs-both)
✅ Baseline OK (51 errors)
✅ All checks passed (mode=stage1-lhs-both)
```

---

## PR-B — RHS activation (after Issue B)

**Title:** P5/GR: Stage-1 RHS split (gInv enabled; baseline-neutral)

### Checklist (DoD)
- [ ] `gInv` uncommented per chosen domain strategy (A/B)
- [ ] Local diagonal/off-diagonal simp facts only (no global `[simp]`)
- [ ] Use `dCoord_add4_flat` + `dCoord_mul` pattern for RC/QC families (mirrors LHS)
- [ ] `make audit` ✅; `make baseline` ✅ (still 51)
- [ ] PR template boxes checked

### Verification output
```
$ make check
✅ ACTIVATION_STATUS OK (stage1-full)
✅ Baseline OK (51 errors)
✅ All checks passed (mode=stage1-full)
```

---

## How to Use the Activation Demo

The file contains a commented `ActivationDemo` section (lines 995-1045) that shows:

1. **Local sumIdx expander** using Option A (definitional approach)
2. **Bridge lemma usage** via `dCoord_sumIdx_via_local_expand`
3. **Connection to Stage-1 facts** showing how to apply `Stage1LHS.Hc_one`

To activate:
1. Copy the `sumIdx_expand_local` lemma into your split section
2. Use `dCoord_sumIdx_via_local_expand` to expand the sumIdx
3. Apply the relevant Stage-1 fact (e.g., `Stage1LHS.Hc_one`)

Example snippet:
```lean
-- Inside your split section
local lemma sumIdx_expand_local {α : Type*} [AddCommMonoid α] (f : Idx → α) :
  sumIdx f = f Idx.t + f Idx.r + f Idx.θ + f Idx.φ := by
  simp only [sumIdx, Idx.decEq]
  simp [add_comm, add_left_comm, add_assoc]
local attribute [simp] sumIdx_expand_local

-- Then use it with the bridge:
rw [dCoord_sumIdx_via_local_expand c _ r θ sumIdx_expand_local]
rw [Stage1LHS.Hc_one M r θ a b c d]
```