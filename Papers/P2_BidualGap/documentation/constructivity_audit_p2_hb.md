# Constructivity Audit (P2 HB/Slim)

**Scope**: `Papers/P2_BidualGap/HB/*.lean` and `Papers/P2_BidualGap/Slim/*.lean`  
**Goal**: Identify classical dependencies (`open Classical`, `by classical`) and mark where CRM‑constructive compliance is currently violated.

## Summary
The HB/Slim path is **not fully CRM‑constructive** yet. We removed several global `classical` openings and refactored the direct dual witness to use `σ_ε` instead of sign‑case splits, but explicit classical steps remain in norm‑location/attainment and in summability arguments. These are not “sneaked in” — they are explicit — but they still violate a strict CRM standard unless WLPO (or stronger principles such as Markov/LPO) are accepted.

## Classical Dependencies (by file)

### `HB/WLPO_DualBanach.lean`
Classical usage:
- `exists_rat_abs_sub_le` (rational density argument).
- `hasOperatorNorm_of_nontrivial` uses classical choice to pick `x ≠ 0`.
- `exists_coeff_near_sup_WLPO` now **uses WLPO** to decide the “all false vs not all false” branch, but still uses **classical extraction** (by‑contradiction on Bool) to obtain a witness index.

Impact:
- Norm locatedness uses classical density of ℚ (acceptable in Lean’s reals, but not CRM‑clean).
- Norm attainment **still depends on classical witness extraction**, even though the decision step is WLPO‑based.

### `HB/DualIsometriesComplete.lean`
Classical usage throughout:
- Many `classical` blocks in the dual isometry development.
- Classical corollaries explicitly re‑introduce WLPO via classical `em`.

Impact:
- The isometry proofs and op‑norm equalities are not CRM‑constructive as written.

### `HB/DirectDual.lean`
Classical usage:
- Sign‑vector replaced by `σ_ε`; no `open Classical`.
- Still uses `summable_of_sum_le` (classical existence of tsum) and a `classical` block in `summable_abs_eval`.

Impact:
- The direct witness `G` is closer to CRM‑friendly (no sign case‑split), but summability is still classical in Lean’s ℝ.

### `HB/WLPO_to_Gap_HB.lean` and `Slim/WLPO_to_Gap_HB.lean`
Classical usage:
- `open Classical …` at top.
- The lemma `dual_is_banach_c0_from_WLPO_struct` is classical (uses `exists_rat_abs_sub_le` etc.).

Impact:
- The current end‑to‑end HB proof uses classical tools for `DualIsBanach c₀`.

### `HB/SimpleFacts.lean`
Classical usage:
- `open Classical …` and one `classical` block.

Impact:
- Minor; still violates strict CRM if used in the main path.

## Current Status vs CRM Standard
**Status**: The HB path is **partially improved** but still classical in key places (witness extraction, summability, Hahn–Banach‑style isometries).  
**CRM requirement**: Replace the classical pieces with WLPO‑only or constructive arguments, or explicitly assume the extra principles (e.g., Markov/LPO).

## Suggested Fix Plan (CRM‑clean)
1. **Eliminate classical witness extraction**
   - Replace the `by_contra` step in `exists_coeff_near_sup_WLPO` with a constructive witness principle, or strengthen the axiom from WLPO to LPO/Markov and state it explicitly.
2. **Replace classical summability**
   - Avoid `summable_of_sum_le`/`tsum`‑based existence by building constructive Cauchy bounds where possible.
3. **Isolate Hahn–Banach dependencies**
   - Keep the dual isometries in a classical namespace and avoid importing them into the WLPO‑only path unless explicitly desired.
4. **Finish WLPO‑only norm attainment**
   - For ℓ∞ coefficients, implement a WLPO‑based bisection that yields a constructive witness (or acknowledge the need for LPO).

## Bottom Line
The current HB proof is correct *classically* but **not CRM‑constructive** yet. The classical dependencies are explicit and localized; eliminating them will require completing the WLPO‑only norm‑locatedness and dual‑isometry steps.
