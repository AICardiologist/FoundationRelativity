# Tactic Playbook for `Riemann.lean` (with Schwarzschild support)

This memo lists the tactics/patterns that keep recurring in `Riemann.lean` and the
adjacent `.md` diagnostics. Use it as a quick reference when extending the proofs.

## 1. SumIdx toolchain

| Pattern | When to use | Example references |
|---------|-------------|--------------------|
| `sumIdx_congr (fun ρ => ?_)` | Pointwise rewrite of a sum. Always introduce `ρ` first, then rewrite/simp inside. | Numerous Case-B calcs (e.g., `Gamma_mu_nabla_nu`, `SESSION_STATUS_OCT28...` lesson 2) |
| `sumIdx_map_sub`, `sumIdx_add3`, `sumIdx_add_distrib` | Repack multiple sums into a *single* sum before running `sumIdx_congr`. Prevents shape mismatches like the one noted in `HANDOFF_TO_JP_BASELINE_RECOVERED_NOV9.md`. | `algebraic_identity` block |
| `mul_sumIdx`, `sumIdx_mul`, `sumIdx_mul_right` | Push constants in/out of sums; used heavily in Step‑8 payload kit. | `expand_nabla_g_pointwise_a/b` |
| `sumIdx_delta_right` + `sumIdx_mul_ite_pick` | Collapses sums after inserting `if ρ = b then 1 else 0`. Apply via `exact` to avoid unfold chains. | Fix A in `HANDOFF...` and diagnostics in `DIAGNOSTIC_NOV8_LEMMA_PROOF_ERRORS.md` |
| Collapse lemmas from Schwarzschild (`comm_r_sum_collapse`, `comm_θ_sum_collapse`, `sumIdx_collapse_left_metric`, `sumIdx_cross_collapse_left`) | Replace nested Σ_λ ΓΓ expressions by a single term when working in the concrete chart. Use `rw`/`exact` instead of bare `simp` to avoid unfolding `g`. | `Schwarzschild.lean` lines 1499‑1580, diagnostics Nov 8 |

**Workflow reminder (hb"): Pack → Congr → δ-insert → δ-eval.** Paul emphasised this for `hb_plus`: unlike scalars, sums must stay in Σ-form until the very end.

## 2. `simp` / `simpa` best practices

1. **Zeroing ∇g payloads:** Use `simp only [nabla_g_zero_ext M r θ h_ext]` *inside* `sumIdx_congr`. Do **not** instantiate the lemma first; let `simp` match the indices (per `SESSION_STATUS_OCT28...` Lesson 1).
2. **Avoid accidental unfolding:** When you just need a previously proved lemma, use `rw [...]` or `exact ...` instead of `simp`. This prevents `simp` from expanding definitions like `g` or `sumIdx`. (See `DIAGNOSTIC_NOV8...` for failures caused by `simp` unfolding `g`.)
3. **`simpa` pitfalls:** Replacing `by simpa using sumIdx_delta_right ...` with `by exact ...` avoids Lean trying to unfold helper lemmas (`HANDOFF...` Fix A). Reserve `simpa` for literal syntactic variations, not delta-collapses.
4. **Restrict lemma set:** Prefer `simp only [list, of, lemmas]` when you want precise control (e.g., `sumIdx_congr; intro ρ; simp only [Γtot, g, mul_zero]`).

## 3. Algebraic finisher tactics

- `ring` / `ring_nf`: Used after commuting/factoring scalar expressions inside `sumIdx`. Many lemmas (`expand_nabla_g_pointwise_*`, `scalar_finish_bb`, etc.) close with `ring_nf` after applying `sumIdx_map_sub`.
- `linarith`: Handy for simple inequalities stemming from Exterior assumptions (rare in the big file but used in Schwarzschild calculus lemmas).
- `field_simp [Exterior.nonzeros_of_exterior ...]`: Use when clearing denominators in `HasDerivAt` or `DifferentiableAt` proofs. Always reference `Exterior.nonzeros_of_exterior` to discharge the nonzero hypotheses automatically.

## 4. Calculus / Differentiability tactics

- Build `DifferentiableAt` goals via `cases` on indices; off-diagonal entries collapse with `[simp]` because `g` is diagonal (`Schwarzschild.lean` `g_offdiag`).
- Use the `f_hasDerivAt` family (lines 207ff in `Schwarzschild.lean`) with `DifferentiableAt.mul`, `DifferentiableAt.comp` to prove the `dCoord_g_differentiable_{r,θ}_ext` lemmas. This is the input expected by `dCoord_sumIdx`.
- When applying product-rule lemmas (`prod_rule_backwards_sum`, `sum_k_prod_rule_to_Γ₁`), always supply the `DifferentiableAt_r/θ` hypotheses first; they come from the previous bullet.

## 5. Index case-splitting

- Recurrent tactic: `cases ρ <;> cases a <;> simp [Γtot, g, ...]`. Useful whenever a sum collapses because the metric/Christoffels are sparse.
- Combine with `[simp]` lemmas from `Schwarzschild.lean` (`Γtot_*`, `Γtot_*_zero`) to avoid manual algebra.

## 6. Known failure modes & fixes

| Failure | Cause | Fix |
|---------|-------|-----|
| `sumIdx_congr` fails with "type mismatch" | Tried to congruence a *triple* sum; the tactic needs one sum per side. | Pack sums first (`sumIdx_map_sub`, `sumIdx_add_distrib`), then call `sumIdx_congr`. (See `HANDOFF...` Fix B.) |
| `simp did nothing` inside sums | Attempted to rewrite `nabla_g` outside the binder. | Move `simp only [...]` inside the `sumIdx_congr` lambda. |
| `simp` unfolds `g` into a huge `match` | Using unrestricted `simp`. | Switch to `rw [sumIdx_collapse_left_metric ...]` or `simp only [...]` to keep `g` abstract (per `DIAGNOSTIC_NOV8...`). |
| Heartbeat / unfold loops with `sumIdx` | Using `simp`/`simpa` on helper lemmas that already match the goal exactly. | Use `exact` or `rw` instead. |

## 7. Recommended tactic recipes

1. **Cancelling ∇g payloads**
   ```lean
   apply sumIdx_congr; intro ρ
   simp only [nabla_g_zero_ext M r θ h_ext]
   ```

2. **Handling Kronecker deltas**
   ```lean
   -- After inserting `if e = ρ then 1 else 0`
   exact sumIdx_delta_right (fun e => A e * g M ρ e r θ) ρ
   ```

3. **Regrouping sums before `sumIdx_congr`**
   ```lean
   calc
     sumIdx (λ k => X k - Y k) + sumIdx Z
         = sumIdx (λ k => (X k - Y k) + Z k) := by
             simpa using sumIdx_add_distrib _ _
     _   = sumIdx (λ k => … simplified …) := by
             apply sumIdx_congr; intro k; …
   ```

4. **Finishing scalar blocks**
   ```lean
   -- After substituting collapse lemmas
   have := ΓΓ_cross_collapse_b ...
   simp [*, mul_comm, mul_assoc] -- or `ring`/`ring_nf`
   ```

Use these patterns to avoid reinventing the wheel when continuing the formalization.
