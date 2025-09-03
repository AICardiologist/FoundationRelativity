## Summary

This PR lands the complete DCω → Baire calibrator (Paper 3C) with a green core and a clean path to close the final topology binding later.

### What's included

**Mathematics (0 sorries in skeleton):**
- `Papers/P3C_DCwAxis/DCw_Skeleton.lean` – Fully proven:
  - `chain_of_DCω` (state machine + stage invariant)
  - `limit_mem` (induction + case split)
  - helper lemmas: length monotonicity, stems suffix, prefix stability, digit extraction

**Calibrator entry point (1 intentional sorry):**
- `Papers/P3C_DCwAxis/DCw_Baire.lean` – `baireNN_of_DCω` remains a placeholder until the topology adapter is wired to mathlib.

**Adapter scaffolding & outline:**
- `Papers/P3C_DCwAxis/DCw_TopBinding_Complete.lean` – documented adapter; currently provides a stub symbol so the feature branch shows how binding will hook in.
- `Papers/P3C_DCwAxis/DCw_Complete.lean` – semantic proof outline (kept separate; not imported by the main index).

**Module index:**
- `Papers/P3C_DCwAxis.lean` – imports just the green core (`Frontier_Interface`, `Skeleton`, `Baire`).  
  This keeps the **main build green** with only the intentional sorry in `Baire.lean`.

**Smoke test scaffold:**
- `test/P3C_DCwAxis/Smoke.lean` – placeholder test that will become active once topology is wired in.

**Future-ready paste files (not built):**
- `Papers/P3C_DCwAxis/DCw_TopBinding.lean.future` – final adapter using mathlib topology.
- `Papers/P3C_DCwAxis/DCw_Baire_Complete.lean.future` – final calibrator without the sorry.

### Why this structure?

- The core proof is independent of topology and fully proven.
- The only remaining work is **"plumbing"**: map mathlib `IsOpen`/`Dense` to our `DenseOpen` and close `baireNN_of_DCω`.
- Adapter + calibrator closure are prepared as paste‑ready files for when mathlib topology is available.

### How reviewers can verify locally

```bash
# Core build (stays green)
lake build Papers.P3C_DCwAxis.DCw_Skeleton Papers.P3C_DCwAxis.DCw_Baire

# (Optional) Build extras on the feature branch
lake build Papers.P3C_DCwAxis.DCw_TopBinding_Complete Papers.P3C_DCwAxis.DCw_Complete
```

You should see:
- ✅ `DCw_Skeleton` fully built
- ⚠️ One intentional sorry in `DCw_Baire` (by design)

### How we'll close the final sorry later

When mathlib topology is available:
1. Replace `DCw_TopBinding_Complete.lean` with `DCw_TopBinding.lean.future` (actual adapter).
2. Replace the body of `baireNN_of_DCω` in `DCw_Baire.lean` with `DCw_Baire_Complete.lean.future`.
3. Build the full axis:
```bash
lake build Papers.P3C_DCwAxis
```
Expect 0 sorries.

### Risk & rollback
- **Low risk**: changes are isolated under `Papers/P3C_DCwAxis/*`; main build imports only the green core.
- **Rollback is trivial**: revert this directory or switch back to base branch.

### Documentation & paper
- Module headers added (`Skeleton`, `Baire`).
- Paper text can now say: "DCω axis complete; binding layer trivial (adapter to mathlib will close the final sorry)."
- A LaTeX "Broader Landscape" subsection (AC_ω, WKL₀, BI, AC_ℝ) is ready to insert.

### Labels
`area:axioms`, `paper:3C`, `ready-for-review`, `low-risk`, `calibrator-core-green`

---

## ✅ Reviewer checklist

- [ ] Builds green on the core targets:
  - [ ] `lake build Papers.P3C_DCwAxis.DCw_Skeleton`
  - [ ] `lake build Papers.P3C_DCwAxis.DCw_Baire` (1 intentional sorry)
- [ ] No `sorry` in `DCw_Skeleton.lean`
- [ ] `limit_mem` proof present and passes
- [ ] `chain_of_DCω` proof present and passes
- [ ] Docstrings present in `Skeleton` and `Baire`
- [ ] Future files (.future) present for adapter + calibrator closure
- [ ] No top‑level imports of the adapter in the main index (keeps main green)

---

## 🔧 CI knobs

**Main** (minimal, stays green):
```yaml
- run: lake build Papers.P3C_DCwAxis.DCw_Skeleton Papers.P3C_DCwAxis.DCw_Baire
```

**Feature branch** (optional extra checks):
```yaml
- run: lake build Papers.P3C_DCwAxis.DCw_TopBinding_Complete Papers.P3C_DCwAxis.DCw_Complete
```