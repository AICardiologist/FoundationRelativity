# Build Error Report — `Papers.P5_GeneralRelativity.GR.Riemann`

## Build context
- **Command:** `lake build Papers.P5_GeneralRelativity.GR.Riemann`
- **Result:** Lean exited with code 1 because two lemmas still contain `sorry`. Numerous non-fatal linter warnings were also emitted from both `Schwarzschild.lean` and `Riemann.lean` while compiling dependencies.

## Blocking errors
| # | Location | Message | Root cause | Remediation plan |
|---|----------|---------|------------|------------------|
| 1 | `Papers/P5_GeneralRelativity/GR/Riemann.lean:12607` (`sum_k_prod_rule_to_Γ₁`) | `declaration uses 'sorry'` | Proof of the product-rule-to-Γ₁ lemma is stubbed where differentiability lemmas, symmetry rewrites, and the `Γ₁` recognition step should go. (See `SORRY_REPORT.md` entries for the same lemma.) | (a) Supply differentiability witnesses for each `Γtot * g` product: reuse or extend the `dCoord_g_differentiable_{r,θ}_ext` lemmas plus differentiability of `Γtot`. (b) Formalize the interchange-of-sum/derivative step via `dCoord_sumIdx` using those hypotheses. (c) Add small lemmas for torsion-free symmetry (`Γtot` lower-index symmetry) and metric symmetry (`g_symm`). (d) Finish with algebra that unfolds `Γ₁` and repackages the sums. |
| 2 | `Papers/P5_GeneralRelativity/GR/Riemann.lean:12676` (`regroup_right_sum_to_Riemann_CORRECT`) | `declaration uses 'sorry'` | Final "Phase 4" assembly lemma is still a stub; it is supposed to combine `sum_k_prod_rule_to_Γ₁` with `Riemann_via_Γ₁`. | After filling lemma #1, write the advertised three-line `calc`: apply `sum_k_prod_rule_to_Γ₁`, rewrite with `Riemann_via_Γ₁` (already proven earlier in the file), and tidy the sums. No new analysis is required once Phase 2B exists. |

## Non-fatal warnings worth addressing
Although they did not stop the build, these warnings highlight low-hanging cleanups that keep future CI runs green once the blockers above are fixed.

### `Schwarzschild.lean`
- **Repeated `unnecessarySimpa` warnings** (lines 118, 487, 496, 501, 515, 914, 1156, 1228–1287, etc.): replace `simpa` with `simp` when no rewriting happens, or provide a non-trivial rewrite so the linter stops flagging them.
- **`unusedSimpArgs` warnings** (e.g., lines 1076, 1367–1369): drop unused items like `inv_pow`, `Finset.sum_insert`, `Finset.mem_insert`, etc., from `simp only` lists.
- **Deprecated constants**: replace `Finset.not_mem_singleton` with `Finset.notMem_singleton` per the deprecation notice at line 1368.

### `Riemann.lean`
- **Unused tactics** at lines 12382–12385 (`simp ... tactic does nothing` and "tactic is never executed"): delete those inert `simp` calls or rewrite the surrounding `match`/`by_cases` so the goals actually use them.
- **`unnecessarySimpa` warnings** near lines 12395 and 12409: same remediation as above—prefer `simp` or supply a rewrite.
- **Unused variables** (lines 12542–12558): either use the parameters (`μ`, `M`) or mark them as `_` / replace the lemmas with point-free versions so linters are appeased.

Cleaning these warnings now prevents them from obscuring real regressions once the critical lemmas are completed.

## Relation to the outstanding `sorry` inventory
The two blocking errors align with the final two entries in `SORRY_REPORT.md`:
1. **`sum_k_prod_rule_to_Γ₁`** (Phase 2B) — needs differentiability infrastructure and explicit symmetry lemmas before invoking `Γ₁`.
2. **`regroup_right_sum_to_Riemann_CORRECT`** (Phase 4) — depends on (1) plus the already-proven `Riemann_via_Γ₁` identity.

Earlier sorry placeholders (metric-compatibility expansions, differentiability lemmas, algebraic helpers) still exist in `Riemann.lean`; they must be resolved eventually, but Lean currently halts at the two Phase-2B/Phase-4 stubs above. Use the detailed strategies in `SORRY_REPORT.md` when tackling them.

## Recommended next steps
1. **Finish the differentiability lemmas** (`dCoord_g_differentiable_{r,θ}_ext`) so they can be referenced inside `sum_k_prod_rule_to_Γ₁`.
2. **Prove `sum_k_prod_rule_to_Γ₁`** using the plan outlined above; most of the work is bookkeeping.
3. **Wire up `regroup_right_sum_to_Riemann_CORRECT`** via a short `calc` once step (2) is complete.
4. **Clean up linters** in both `Schwarzschild.lean` and `Riemann.lean` (convert `simpa` → `simp`, prune unused `simp` args, remove dead tactics, rename deprecated constants).
5. **Re-run** `lake build Papers.P5_GeneralRelativity.GR.Riemann` to ensure no further blockers remain before addressing the other sorry placeholders enumerated previously.
