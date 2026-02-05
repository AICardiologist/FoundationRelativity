-- Sub-Lemma Stubs for algebraic_identity (JP's Guidance, Oct 23, 2025)
-- PASTE THESE BEFORE the algebraic_identity lemma in Riemann.lean

/-! ### Sub-lemmas for algebraic_identity (B1-B4)

These break down the algebraic heavy lifting into manageable pieces:
  B1: Expand nabla_g, push dCoord through sums/products
  B2a/b: Cancel Γ∂g payloads using collector lemmas
  B3: Cancel mixed partials (∂∂g) using Clairaut
  B4: Regroup remaining terms to Riemann definition

Reference: JP_TACTICAL_GUIDANCE_OCT23.md
-/

/-- B1: Expansion sub-lemma.
    Expands nabla_g inside P, C_a, C_b and pushes dCoord through sums/products.

The shape obtained has four "commutator blocks", each with:
  - Main part: (∂Γ)g + ΓΓg terms
  - Payload part: Γ∂g terms (to be cancelled in B2)

Uses: dCoord_sumIdx, dCoord_mul_of_diff, discharge_diff tactic -/
private lemma expand_PCaCb_to_main_plus_payload
    (M r θ : ℝ) (h_ext : Exterior M r θ) (μ ν a b : Idx) :
  P_terms M r θ μ ν a b + C_terms_a M r θ μ ν a b + C_terms_b M r θ μ ν a b
  =
  -- TODO: Fill in expanded form showing (∂Γ)g + ΓΓg + Γ∂g structure
  -- For a-branch:
  --   ∑_ρ (∂_μ Γ^ρ_νa) g_ρb + ∑_ρ Γ^ρ_νa (∂_μ g_ρb) - (swap μ↔ν)
  --   + ∑_ρ,λ (Γ^ρ_μλ Γ^λ_νa - Γ^ρ_νλ Γ^λ_μa) g_ρb
  -- Plus analogous for b-branch and C_a, C_b contributions
  sorry := by
  unfold P_terms C_terms_a C_terms_b
  unfold nabla_g
  -- Push dCoord through sumIdx (need differentiability)
  -- Push dCoord through products (product rule)
  -- Discharge DifferentiableAt_* side conditions
  sorry

/-- B2a: Payload cancellation for a-branch.
    Cancels Γ∂g payload from a-branch against C_a contribution.

Key insight (JP): Use sumIdx_collect_comm_block_with_extras with:
  G ρ := g M ρ b r θ
  A ρ := ∂_μ Γ^ρ_νa
  B ρ := ∂_ν Γ^ρ_μa
  C ρ := ∑_λ Γ^ρ_μλ Γ^λ_νa
  D ρ := ∑_λ Γ^ρ_νλ Γ^λ_μa
  P ρ := Γ^ρ_νa (∂_μ g_ρb)
  Q ρ := Γ^ρ_μa (∂_ν g_ρb)

Collector gives: ∑G*((A-B)+(C-D)) + ∑(P-Q)
The ∑(P-Q) cancels with C_a exactly (sumIdx_congr + ring).

Uses: sumIdx_collect_comm_block_with_extras, sumIdx_congr, ring -/
private lemma payload_cancel_a
    (M r θ : ℝ) (h_ext : Exterior M r θ) (μ ν a b : Idx) :
  [expanded form from B1]
  =
  [same but with a-branch Γ∂g payload removed]
  sorry := by
  -- Define G, A, B, C, D, P, Q as in JP's mapping
  let G  : Idx → ℝ := fun ρ => g M ρ b r θ
  let A  : Idx → ℝ := fun ρ => dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ
  let B  : Idx → ℝ := fun ρ => dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ
  let C  : Idx → ℝ := fun ρ => sumIdx (fun lam => Γtot M r θ ρ μ lam * Γtot M r θ lam ν a)
  let D  : Idx → ℝ := fun ρ => sumIdx (fun lam => Γtot M r θ ρ ν lam * Γtot M r θ lam μ a)
  let P  : Idx → ℝ := fun ρ => Γtot M r θ ρ ν a * dCoord μ (fun r θ => g M ρ b r θ) r θ
  let Q  : Idx → ℝ := fun ρ => Γtot M r θ ρ μ a * dCoord ν (fun r θ => g M ρ b r θ) r θ

  -- Apply collector: (∑(A*G+P)) - (∑(B*G+Q)) + ... = ∑G*((A-B)+(C-D)) + ∑(P-Q)
  have hCollect := sumIdx_collect_comm_block_with_extras G A B C D P Q

  -- Show ∑(P-Q) cancels with C_a contribution
  -- Use sumIdx_congr to rename dummy index λ → ρ
  -- Then ring to finish
  sorry

/-- B2b: Payload cancellation for b-branch.
    Cancels Γ∂g payload from b-branch against C_b contribution.

Same pattern as B2a but with a ↔ b swapped.

Uses: sumIdx_collect_comm_block_with_extras, sumIdx_congr, ring -/
private lemma payload_cancel_b
    (M r θ : ℝ) (h_ext : Exterior M r θ) (μ ν a b : Idx) :
  [form from B2a]
  =
  [same but with b-branch Γ∂g payload removed]
  sorry := by
  -- Mirror of B2a with a ↔ b
  let Gb : Idx → ℝ := fun ρ => g M a ρ r θ
  let Ab : Idx → ℝ := fun ρ => dCoord μ (fun r θ => Γtot M r θ ρ ν b) r θ
  let Bb : Idx → ℝ := fun ρ => dCoord ν (fun r θ => Γtot M r θ ρ μ b) r θ
  let Cb : Idx → ℝ := fun ρ => sumIdx (fun lam => Γtot M r θ ρ μ lam * Γtot M r θ lam ν b)
  let Db : Idx → ℝ := fun ρ => sumIdx (fun lam => Γtot M r θ ρ ν lam * Γtot M r θ lam μ b)
  let Pb : Idx → ℝ := fun ρ => Γtot M r θ ρ ν b * dCoord μ (fun r θ => g M a ρ r θ) r θ
  let Qb : Idx → ℝ := fun ρ => Γtot M r θ ρ μ b * dCoord ν (fun r θ => g M a ρ r θ) r θ

  have hCollect := sumIdx_collect_comm_block_with_extras Gb Ab Bb Cb Db Pb Qb
  sorry

/-- B3: Mixed partials cancellation.
    Uses Clairaut's theorem to cancel ∂∂g terms from P_terms expansion.

After B2, we have only (∂Γ)g and ΓΓg terms plus mixed partials ∂∂g.
This lemma eliminates the ∂∂g using dCoord_commute_for_g_all.

Uses: dCoord_commute_for_g_all (Clairaut for smooth metric) -/
private lemma mixed_partials_cancel_in_P
    (M r θ : ℝ) (h_ext : Exterior M r θ) (μ ν a b : Idx) :
  [form from B2b with mixed partials ∂_μ∂_ν g - ∂_ν∂_μ g]
  =
  [same but with ∂∂g terms cancelled to 0]
  sorry := by
  -- Use Clairaut: ∂_μ∂_ν g = ∂_ν∂_μ g (for smooth g)
  have hmixed := dCoord_commute_for_g_all M r θ a b μ ν
  -- Subtract: (∂_μ∂_ν - ∂_ν∂_μ) g = 0
  sorry

/-- B4: Regroup to Riemann definition.
    Recognizes remaining (∂Γ)g + ΓΓg terms as Riemann tensor.

After B2-B3, we have only:
  ∑_ρ g_ρb ( ∂_μ Γ^ρ_νa - ∂_ν Γ^ρ_μa
           + ∑_λ (Γ^ρ_μλ Γ^λ_νa - Γ^ρ_νλ Γ^λ_μa) )
Plus mirror with a ↔ b.

This is BY DEFINITION: -R_baμν - R_abμν

Uses: RiemannUp definition, Riemann_contract_first, sumIdx_collect6, g_symm -/
private lemma regroup_main_to_Riemann
    (M r θ : ℝ) (h_ext : Exterior M r θ) (μ ν a b : Idx) :
  [form from B3 with only (∂Γ)g + ΓΓg]
  =
  - Riemann M r θ b a μ ν - Riemann M r θ a b μ ν := by
  -- Unfold RiemannUp, Riemann definitions
  -- Use sumIdx_collect6 for (2 ∂Γ + 4 ΓΓ) structure
  -- Apply Riemann_contract_first to re-express ∑_ρ g_ρb · RiemannUp
  -- Use g_symm where needed (g M a ρ = g M ρ a)
  sorry

/-! ### Alternative: Can combine B2a and B2b into single lemma if preferred

private lemma payload_cancel_both
    (M r θ : ℝ) (h_ext : Exterior M r θ) (μ ν a b : Idx) :
  [expanded form]
  =
  [form with BOTH a-branch and b-branch payloads removed]
  := by
  -- Apply both collectors in sequence
  sorry
-/
