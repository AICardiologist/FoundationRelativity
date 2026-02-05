# Riemann & Schwarzschild Lemma Reference

This note collects the portions of `Papers/P5_GeneralRelativity/GR/Riemann.lean` and the
supporting facts from `Schwarzschild.lean` that repeatedly come up when working on the
open proofs (metric compatibility, Step‑8 algebra, Ricci identity, etc.).  Line numbers use
`Riemann.lean` unless stated otherwise.

## 1. Riemann.lean roadmap

| Block | Key items | Dependencies | Typical uses |
|-------|-----------|--------------|--------------|
| **Exterior basics** (lines 24‑120) | `Exterior` structure plus `Exterior.r_ne_zero`, `f_ne_zero`, `nonzeros_of_exterior`, openness lemmas | Algebraic properties of `f` imported from `Schwarzschild.lean` | Every lemma that needs `r ≠ 0`, `f ≠ 0`, or `Real.sin θ ≠ 0` when working on the exterior chart |
| **Metric compatibility payload** (lines 2479‑3075) | `dCoord_g_expand` (2479), `prod_rule_backwards_sum` (2897) and `_direct` (2946), forward reference `dCoord_g_via_compat_ext_temp` (2956) leading to the actual proof at 3072 | `nabla_g_zero_ext` (proved later), product-rule helpers from ` prod_rule_backwards_sum`, differentiability lemmas for `g` | Converts ∇g=0 into explicit formulas for `dCoord μ g_ab` so 
Γ∂g payloads inside Nabla/Tensor expansions can be discharged |
| **Riemann via Γ₁** (lines 2790‑2985) | Cancellation lemmas `Riemann_via_Γ₁_Cancel_{r,θ}`, identification lemmas `Riemann_via_Γ₁_Identify_{r,θ}`, and the core identity `Riemann_via_Γ₁` (2977) | Product rule lemmas + the Γ₁ definition (`Γ₁ := Σ g · Γ`) | Phase‑3 of Step‑8: converts derivatives of Γ₁ into the standard covariant Riemann expression |
| **Payload expansion kit** (lines 6689‑7050) | `expand_PCaCb_to_main_plus_payload` (6689), `expand_nabla_g_pointwise_a/b` (6750/6824), their lifted versions `expand_Ca`, `expand_Cb`, and `expand_Cb_for_C_terms_b` | `dCoord_sumIdx`, `dCoord_mul_of_diff`, differentiability lemmas for Γ and g, algebraic lemmas such as `sumIdx_map_sub`, `sumIdx_add3` | Breaks `P_terms + C_terms_a + C_terms_b` into 
(i) payload (`Γ·∂g`), (ii) main (`ΓΓ·g`), (iii) cross (`ΓΓ·g` with metric indices swapped), enabling the cancellation arguments in Blocks B1–B4 |
| **Differentiability infrastructure** (lines 6725‑10124) | `dCoord_g_differentiable_r_ext` (6725), `dCoord_g_differentiable_θ_ext` (6736), higher-regularity lemmas `dCoord_g_differentiable_r/θ` (10047/10124), pointwise Clairaut theorem `clairaut_g` (7038), helper lemmas `diff_Xκ_r`, `dCoord_sumIdx_of_diff`, etc. | Smoothness of the Schwarzschild metric components (from `Schwarzschild.lean`), calculus facts about `f`, field-simp lemmas extracted from `Exterior` | Justify commuting derivatives with `sumIdx` and using product rules in the Nabla expansions |
| **Algebraic identity & Ricci kit** (lines 8258‑10150) | `algebraic_identity` (8258), historical version `algebraic_identity_four_block_old` (9704), `ricci_identity_on_g_general` (9357), specialized forms `ricci_identity_on_g_rθ_ext` (9834) and the global goal `ricci_identity_on_g` (9935), symmetry lemmas `Riemann_swap_a_b_ext` (10024) and `Riemann_swap_a_b` (10030) | Output from the payload kit + Step‑8 cancellations (`expand_Ca/Cb`, `comm_r_sum_collapse`, etc.), metric compatibility, `nabla_g_zero_ext` | Prove that `[∇_μ, ∇_ν] g_{ab}` reduces to the covariant Riemann expressions and deduce first-pair antisymmetry |
| **Phase 4 (final regrouping)** (lines 12607‑12695) | `sum_k_prod_rule_to_Γ₁` (12607) and `regroup_right_sum_to_Riemann_CORRECT` (12676) | Everything above: differentiability lemmas, `prod_rule_backwards_sum`, torsion-free/metric symmetry of Γ and g, `Riemann_via_Γ₁` | Finishes the corrected regrouping argument: rewrites Σ(∂Γ·g) as Σ(∂Γ₁), then as Σ(Riemann·g) |

### Notable supporting lemmas (hook points for future proofs)
- `sumIdx_reduce_by_diagonality`, `sumIdx_swap`, `sumIdx_map_sub`, `sumIdx_add3` — algebraic utilities for reorganizing finite sums.
- `insert_delta_right_diag`, `scalar_pack4` — helper lemmas used during the Block‑B cancellations to repackage scalar expressions.
- `comm_r_sum_collapse`, `comm_θ_sum_collapse` (imported from `Schwarzschild.lean`, see below) — collapse the Σ_λ ΓΓ terms to single-index expressions in the Schwarzschild chart, crucial for the unfinished `flatten_comm_block_{r,θ}` lemmas and for simplifying the ΓΓ blocks in `algebraic_identity`.

## 2. Selected Schwarzschild.lean reference

The Schwarzschild file provides the concrete ingredients that `Riemann.lean` treats abstractly.  The following pieces are used repeatedly in the GR proof stack:

1. **Metric scalars (`lines 207‑320`)**
   - Definitions of the diagonal metric components `g_tt`, `g_rr`, `g_θθ`, `g_φφ` and their inverses.
   - Calculus facts for the Schwarzschild factor `f M r`: positivity (`f_pos_of_hr`), derivative (`f_derivative`), horizon behavior (`f_eq_zero_iff_r_eq_2M`).
   - Exterior-domain utilities (`r_pos_of_exterior`, `r_ne_zero_of_exterior`) feed directly into the `Exterior` lemmas at the top of `Riemann.lean`.

2. **Metric tensor as a 2-form (`lines 1005‑1050`)**
   - `[simp]` lemmas `g_apply_tt`, `g_apply_rr`, `g_apply_θθ`, `g_apply_φφ`, and the off-diagonal vanishing lemma `g_offdiag` show the metric is diagonal in Schwarzschild coordinates.
   - These lemmas justify diagonal collapses used when contracting `g` inside `sumIdx` expressions (e.g. in the unfinished `flatten_comm_block_*` proofs).

3. **Total Christoffel symbols (`lines 1499‑1580`)**
   - `Γtot_nonzero` computes Christoffel symbols case-by-case, while `Γtot` packages them into a total function on indices.
   - Component lemmas (`Γtot_r_tt`, `Γtot_θ_rθ`, …) expose each non-zero entry.
   - Sparsity/collapse lemmas:
     * `[simp]` lemmas for vanishing components, e.g., `Γtot_θ_θθ_zero`.
     * `comm_r_sum_collapse` and `comm_θ_sum_collapse` show that the Σ_λ ΓΓ products in the r- and θ-blocks reduce to single terms. These are exactly the facts needed to finish `h₂`, `h₃` in `flatten_comm_block_{r,θ}` and to simplify the ΓΓ blocks in `algebraic_identity`.

4. **Differentiability / calculus helper lemmas**
   - Chain-rule lemmas for `g_rr`, `g_inv_tt`, etc. discharge denominator side conditions (see `lines 435‑615`).
   - These are the analytic inputs feeding the `DifferentiableAt_*` lemmas in `Riemann.lean` (e.g., when proving that `r ↦ dCoord ν g_{ab}` is differentiable on the exterior).

5. **Domain-wide facts**
   - Multiple “Exterior specialization” lemmas (search for *Exterior specialization* in `Schwarzschild.lean`) convert assumptions like `2M < r` into the non-vanishing denominators demanded by `field_simp` or derivative rules.  These facts back the `Exterior.nonzeros_of_exterior` bundle in `Riemann.lean`.

## 3. How to navigate the files while proving new lemmas

- **Need a sum/swap identity?** Search for `sumIdx_*` in `Riemann.lean` — most variations (`sumIdx_swap`, `sumIdx_map_sub`, `sumIdx_add3`, `sumIdx_mul`) are defined near the "Standardized Distribution" section (~2600‑2800).
- **Need a concrete Γ component?** Jump to `Schwarzschild.lean:1499‑1580` for `Γtot_*` lemmas. The collapses (`comm_r_sum_collapse`, `comm_θ_sum_collapse`) immediately answer “what does Σ_λ ΓΓ look like in Schwarzschild coordinates?”
- **Need differentiability side-conditions?** Use `dCoord_g_differentiable_r_ext` / `_θ_ext` (6725/6736) plus the supporting calculus lemmas. The non-`_ext` versions at 10047/10124 cover the general (non-Exterior) domain.
- **Need to commute derivatives with `sumIdx` or `Γ₁`?** See the block containing `prod_rule_backwards_sum` and `sum_k_prod_rule_to_Γ₁`: they already codify the pattern “d/dx of Σ_k g·Γ” → “Σ_k (∂g·Γ + g·∂Γ)”.

These references prevent re-deriving the same facts and help jump directly to the lemmas each open proof needs.

## 4. Using existing lemmas to clear the open goals

Below is a checklist linking each outstanding `sorry` or build-stopping error to the lemmas
already available in `Riemann.lean` / `Schwarzschild.lean`.

1. **`dCoord_g_expand` (`Riemann.lean:2479`)**
   - *Use*: `nabla_g_zero_ext` (proved later in the file) rewrites covariant derivatives to zero on Exterior.  Combine it with the `Exterior` helpers (`r_ne_zero`, `f_ne_zero`) so every denominator discharge is automatic.
   - *Plan*: Expand the definition of `nabla_g` using `sumIdx` notation, solve for `dCoord μ g_ab`, and reuse the `sumIdx` utilities to move Γ contractions to the RHS.

2. **`flatten_comm_block_r/θ` pending steps (`lines 2550‑2669`)**
   - `h₂`/`h₃` are pure algebra: apply the Schwarzschild collapse lemmas `comm_r_sum_collapse` and `comm_θ_sum_collapse` to turn Σ_d(Γ·Γ) into a single term, and `g_offdiag` to justify pulling `g` outside the inner sums.
   - `sumIdx_swap` + `sumIdx_map_sub` (already used earlier in each proof) finish the bookkeeping once the collapse lemmas are invoked.

3. **`expand_PCaCb_to_main_plus_payload` (`line 6689`)**
   - *Inputs*: differentiability lemmas (`dCoord_g_differentiable_{r,θ}_ext`), `dCoord_sumIdx`, `dCoord_mul_of_diff`.
   - *Strategy*: invoke `expand_nabla_g_pointwise_a/b` pointwise, then lift across Σ_ρ using `sumIdx_congr` the same way `expand_Ca` and `expand_Cb` already do.  The goal statement is simply the sum of those two lifted lemmas.

4. **`dCoord_g_differentiable_r_ext` / `_θ_ext` (`lines 6725/6736`)**
   - Pull the calculus facts from `Schwarzschild.lean`:
     * the component functions `g_tt`, `g_rr`, `g_θθ`, `g_φφ` are smooth combinations of polynomials, `f`, and trigonometric functions;
     * `f_hasDerivAt`, `f_derivative`, `f_pos_*` supply the nonzero denominators.
   - Split on indices (`cases ν; cases a; cases b`) and apply `DifferentiableAt.mul`, `DifferentiableAt.const_sub`, etc.  The trivial off-diagonal cases close by `[simp]` using `g_offdiag`.

5. **`expand_nabla_g_*` already proven** → **`expand_Ca`, `expand_Cb`, `expand_Cb_for_C_terms_b`** (lines 6894‑7010)
   - These completions show how to lift pointwise lemmas across `sumIdx`.  Follow the exact pattern when needing similar lifts later (e.g., in `sum_k_prod_rule_to_Γ₁`).

6. **`hb_plus` inside `algebraic_identity` (`~8785`)**
   - This subgoal matches the combination already proved right below (the lemma `hb`). Reuse `ΓΓ_main_reindex_b_*`, `ΓΓ_cross_collapse_b_*`, `insert_delta_right_diag`, and `sumIdx_map_sub` to show that the Σ(B_b) difference equals the `RiemannUp` term plus `rho_core_b`.
   - The collapse lemmas from `Schwarzschild.lean` eliminate the inner Σ layers once indices are swapped appropriately.

7. **`ricci_identity_on_g` (`line 9935`)**
   - `ricci_identity_on_g_general` (9357) is already finished; specialize μ=Idx.r, ν=Idx.θ and reuse the Exterior assumptions just as in `ricci_identity_on_g_rθ_ext` (9834).
   - The only additional work is addressing the non-Exterior cases. These can be handled by case splits on `M` and `r` using the raw component formulas for `Riemann` (which vanish in the degenerate regimes) and the definitions of `Exterior` for the safe region.

8. **`Riemann_swap_a_b` (`line 10030`)**
   - After finishing `ricci_identity_on_g`, the global antisymmetry follows immediately from `Riemann_swap_a_b_ext` plus the case split hints already sketched in the comment block. Each case either invokes the exterior lemma or unfolds the metric/connection definitions to show both sides vanish.

9. **`sum_k_prod_rule_to_Γ₁` (`line 12607`)**
   - Differentiability: cite `dCoord_g_differentiable_{r,θ}_ext` for the product `Γtot * g` (since both factors are smooth on Exterior).
   - Interchange derivative and Σ: apply `dCoord_sumIdx` using those differentiability proofs.
   - Symmetry rewrites: use the torsion-free/metric symmetries encoded in the `[simp]` lemmas for `Γtot` and in `g_offdiag` (metric symmetry is immediate from the definition of `g`).
   - Last step: unfold `Γ₁` and use `sumIdx_congr` to match the definition.

10. **`regroup_right_sum_to_Riemann_CORRECT` (`line 12676`)**
    - Once the lemma above is in place, the advertised 3-step `calc` is immediate: apply `sum_k_prod_rule_to_Γ₁`, rewrite with `Riemann_via_Γ₁` (2977), and finish with algebra.

Addressing these items systematically will remove the current `sorry` blockers and unblock `lake build Papers.P5_GeneralRelativity.GR.Riemann`.
