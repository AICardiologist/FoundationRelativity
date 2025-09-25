# Decision Issues to Open

## Issue A — Choose sumIdx_expand strategy

**Title:** [P5][Decision] sumIdx_expand strategy (Option A vs B)

### Summary
Pick how `sumIdx f` expands to the 4 terms {t,r,θ,φ} for split sections. This is local to Stage-1 splits; no global behavior required.

### Options
- **Option A (definitional):** `sumIdx` definition is literally the 4-term sum.
  - Proof shape: `simp [sumIdx, add_comm, add_left_comm, add_assoc]`.
- **Option B (finite-type):** `sumIdx` is a fold over `Idx` with `[Fintype Idx]`.
  - Proof shape: `classical; -- unfold → Finset.universe.sum → simp [...]`.

### Acceptance criteria
- [ ] Document the chosen option in ACTIVATION_TRACKING.md Status Matrix.
- [ ] Provide a local lemma template:
```lean
-- inside the split section
local lemma sumIdx_expand_local (f : Idx → α) :
  sumIdx f = f Idx.t + f Idx.r + f Idx.θ + f Idx.φ := by
  -- Option A or B proof here
  …
local attribute [simp] sumIdx_expand_local
```
- [ ] Confirm `make audit` passes (no global `[simp]`).
- [ ] Dry-run on a branch: paste the lemma into one split section and ensure baseline stays 51.

**Owners:** Geometry lead (sumIdx definition), Proof engineer (local lemma pattern)
**Due:** TBD

---

## Issue B — Choose gInv domain strategy

**Title:** [P5][Decision] gInv domain strategy (hypothesis-gated vs chart)

### Summary
Pick how to handle denominators in the diagonal inverse metric (e.g., `r ≠ 0`, `sin θ ≠ 0`) for RHS Stage-1 and metric inverse identities.

### Options
- **A — Hypothesis-gated:** keep `gInv` total; state lemmas under `hr : r ≠ 0`, `hs : Real.sin θ ≠ 0`.
- **B — Chart-restricted:** open a section with `variables (hr : r ≠ 0) (hs : Real.sin θ ≠ 0)` and keep simp facts local.

### Acceptance criteria
- [ ] Record the choice in ACTIVATION_TRACKING.md Status Matrix.
- [ ] Provide a minimal set of local simp facts for diagonals/off-diagonals.
- [ ] Confirm pre-commit guards allow RHS sections (`def gInv` visible) and `make audit` passes.
- [ ] Dry-run: enable one RHS Stage-1 lemma in a throwaway branch; baseline unchanged.

**Owners:** Geometry lead (domain choice), Proof engineer (local simp facts)
**Due:** TBD

---

## Issue C — Activation mode for LHS

**Title:** [P5][Decision] Activation mode for LHS (stage1-lhs-first vs stage1-lhs-both)

### Summary
Decide whether to enable only the first family or both families in the split sections.

### Options
- **stage1-lhs-first:** conservative toggle, one family at a time.
- **stage1-lhs-both:** enable both families (recommended—facts already proven).

### Acceptance criteria
- [ ] Set marker with `./scripts/set-activation.sh stage1-lhs-both` (or `stage1-lhs-first`).
- [ ] `make check` passes (activation + baseline).
- [ ] Confirm no Stage-1 code is activated inside the main proof yet (only local lemmas + scaffolding).
- [ ] Update Status Matrix in ACTIVATION_TRACKING.md.

**Owners:** Paper 5 maintainer
**Due:** TBD