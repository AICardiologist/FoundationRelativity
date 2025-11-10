# Riemann.lean Sorry Audit

## dCoord_g_expand — `Riemann.lean:2473-2485`
- **Goal**: rewrite `dCoord μ g_{ab}` as the sum of two Γ·g contractions (coordinate form of metric compatibility) on the exterior region.
- **Missing work**: the proof is deferred until `nabla_g_zero_ext` is introduced later, so the lemma currently relies on a blatant `sorry`.
- **Next steps**: once `nabla_g_zero_ext` (∇g = 0) is available, expand the definition of `nabla_g`, specialize to Exterior, and solve the resulting equation for `dCoord μ g_{ab}` to discharge the placeholder.

## flatten_comm_block_r — `Riemann.lean:2555-2594`
- **`h₂` (`Riemann.lean:2570-2583`)**: after distributing and swapping sums, the proof must justify the final index relabeling that turns `Σ_d Γ_{da}^r Γ_{eθ}^d` into `Σ_ρ Γ_{ρ r}^λ Γ_{λ θ a}` with the metric factor pulled out. This needs a clean sum-index renaming lemma (`sumIdx_reindex`) or an explicit bijection between the `Idx` cases.
- **`h₃` (`Riemann.lean:2585-2594`)**: similar algebra for the third term, but now the metric occupies the second slot (`g_{de}`); finishing this requires applying metric diagonality (`sumIdx_reduce_by_diagonality`) so only `e = d` contributes, followed by the same sum swap as in `h₂`.

## flatten_comm_block_θ — `Riemann.lean:2625-2669`
- **`h₂` (`Riemann.lean:2648-2660`)**: θ-version of the previous index reordering. The missing proof mirrors the r-branch: swap the sums, commute factors pointwise, and rename indices so the result matches the target contraction.
- **`h₃` (`Riemann.lean:2660-2669`)**: θ-branch analog of the diagonal-collapse step. Needs the same diagonality lemma plus bookkeeping of Γ indices with r↔θ exchanged.

## dCoord_g_via_compat_ext_temp — `Riemann.lean:2956-2965`
- **Goal**: forward declaration of the Exterior metric-compatibility identity used earlier in the file.
- **Missing work**: the actual proof (`dCoord_g_via_compat_ext`) appears later (~3072), but this placeholder still contains a `sorry`. It should be replaced by a reference to the final lemma once all dependencies compile to keep CI axiom-free.

## expand_PCaCb_to_main_plus_payload — `Riemann.lean:6690-6715`
- **Goal**: Step B1 of the "algebraic identity" proof, expanding `P_terms + C_terms_a + C_terms_b` into the structured `(∂Γ)g + ΓΓg + Γ∂g` blocks.
- **Missing work**: two separate `sorry`s guard (1) the high-level equality statement and (2) the actual calculation. The proof needs to:
  1. Unfold `P_terms`, `C_terms_*`, and `nabla_g`.
  2. Push `dCoord` through sums via `dCoord_sumIdx`/`dCoord_sub_of_diff`, which requires differentiability hypotheses.
  3. Apply `prod_rule_backwards_*` lemmas to move derivatives past Γ·g products.
  4. Reassociate pieces so that payload, main, and cross terms are visibly separated.

## dCoord_g_differentiable_r_ext / dCoord_g_differentiable_θ_ext — `Riemann.lean:6718-6739`
- **Goal**: establish that `r ↦ dCoord ν g_{ab}` and `θ ↦ dCoord ν g_{ab}` are differentiable on Exterior, which is needed to justify commuting derivatives with sums.
- **Missing work**: each lemma currently ends with `sorry`. They should leverage:
  - Case splits on indices to reduce to explicit formulas for Schwarzschild `g`.
  - Known smoothness of the profile functions (`f`, polynomials, trigonometric factors) on Exterior.
  - `DifferentiableAt.comp`/`differentiableAt_const` lemmas to close off trivial cases (off-diagonal zero components, θ-independent entries).

## algebraic_identity (b-branch packing) — `Riemann.lean:8785-8810`
- **`hb_plus`**: the intermediate claim equating the b-branch scalar combination to `-Σ RiemannUp_{ρaμν} g_{ρb} + rho_core_b` is left as `sorry`.
- **Required reasoning**: substitute the definitions of `B_b`, `rho_core_b`, and `RiemannUp`, carry out the ΓΓ regrouping performed later in the proof (using `ΓΓ_main_reindex_*` / `ΓΓ_cross_collapse_*`), then isolate the `rho_core_b` remainder. The target is essentially the statement proven immediately afterwards (`hb`), so `hb_plus` should become a short helper lemma feeding into that final simplification.

## ricci_identity_on_g — `Riemann.lean:9922-9944`
- **Goal**: show ` [∇_c, ∇_d] g_{ab} = -R_{bacd} - R_{abcd}` without assuming domain restrictions.
- **Blocking issues**: the existing tactic script times out; the lemma is currently a bare `sorry`. Finishing it likely requires:
  - Reusing the structured approach from `algebraic_identity` (expand ∇∇g, regroup into Riemann pieces).
  - A more granular case split on indices to keep simplifications manageable (Lean hints at needing per-component proofs).
  - Potentially crafting auxiliary lemmas for zero/off-diagonal cases to avoid heavy algebra in the main proof.

## Riemann_swap_a_b — `Riemann.lean:10008-10035`
- **Goal**: global antisymmetry `R_{bacd} = -R_{abcd}`.
- **Current state**: entire proof is `sorry`, with an outline (commented) suggesting a case split on whether the point lies in Exterior (`0<M`, `2M<r`) and fallback lemmas for the boundary / degenerate cases. Once `ricci_identity_on_g` and `nabla_nabla_g_zero_ext` stabilize, this lemma should:
  1. Invoke `Riemann_swap_a_b_ext` on the Exterior region.
  2. Provide separate proofs for `$r ≤ 2M$` and `$M ≤ 0$` cases, likely by unfolding `Riemann` (since the spacetime is flat there or the metric degenerates), filling in the currently-commented `sorry` lines.

## sum_k_prod_rule_to_Γ₁ — `Riemann.lean:12604-12674`
Multiple `sorry`s mark the subgoals needed to convert `Σ_k ∂(Γ·g)` into `∂Γ₁`:
1. **`h_diff_r` / `h_diff_θ` (`Riemann.lean:12619-12622`)**: need differentiability proofs for each product `Γtot * g`, probably by combining existing C¹ lemmas for Γ and g plus `DifferentiableAt.mul`.
2. **Interchanging derivative and sum (`Riemann.lean:12624-12636`)**: once differentiability is established, apply `dCoord_sumIdx`-style lemmas to swap `dCoord` with `sumIdx`. This requires packaging `h_diff_*` into the `DifferentiableAt_r/θ` hypotheses those lemmas expect.
3. **Symmetry rewrites (`Riemann.lean:12636-12654`)**: the `congr` block needs torsion-freeness (`Γtot k θ a = Γtot k a θ`) and metric symmetry (`g_{kb} = g_{bk}`). These lemmas exist earlier (e.g., `Gamma_tot_symm_lower`, `g_symm`), but they are not invoked yet.
4. **Γ₁ recognition (`Riemann.lean:12654-12666`)**: folding the sums back into the definition of `Γ₁` requires just expanding the definition and possibly a `sumIdx_congr` to match the order.

## regroup_right_sum_to_Riemann_CORRECT — `Riemann.lean:12680-12695`
- **Goal**: final Phase-4 assembly, showing the right-hand commutator sums collapse to `Σ_k R_{ka rθ} g_{kb}`.
- **Missing work**: once `sum_k_prod_rule_to_Γ₁` is proved, this lemma should chain:
  1. The product-rule lemma to replace `Σ_k ∂(Γ·g)` with `Σ_k ∂Γ₁`.
  2. `Riemann_via_Γ₁` (already proved earlier) to rewrite `∂Γ₁` in terms of Riemann.
  3. A final simplification aligning indices. The `sorry` currently blocks this straightforward calculation.

