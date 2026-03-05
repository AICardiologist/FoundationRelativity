/-
  Paper 98: The Motivic CRM Architecture — Archimedean Obstruction Theorem

  Any proof path avoiding Archimedean realizations and comparisons has
  BISH signature. This is the central theorem of the paper.
-/

import Papers.P98_MotivicCRM.CRMLevel
import Papers.P98_MotivicCRM.Realizations

/-! ## Proof Paths -/

/-- A proof path through a motive uses specific realizations and comparisons. -/
structure ProofPath where
  realizations : List Realization
  comparisons  : List ComparisonMap
  deriving Repr

/-- The CRM signature of a proof path is the join (max) of all components:
    the motive (always BISH), the realizations used, and the comparisons needed. -/
def proof_signature (p : ProofPath) : CRMLevel :=
  let real_sigs := p.realizations.map (fun r => (realization_signature r).level)
  let comp_sigs := p.comparisons.map (fun c => (comparison_signature c).level)
  let all_sigs := [motive_signature.level] ++ real_sigs ++ comp_sigs
  all_sigs.foldl CRMLevel.join .BISH


/-! ## Helper Lemmas -/

/-- If all elements of a mapped list satisfy P, then the original list satisfies
    the corresponding property. -/
private theorem map_all_bish_realizations (l : List Realization)
    (h : ∀ r ∈ l, is_non_archimedean r = true) :
    ∀ x ∈ l.map (fun r => (realization_signature r).level), x = CRMLevel.BISH := by
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨r, hr, hrx⟩ := hx
  rw [← hrx]
  exact non_archimedean_is_bish r (h r hr)

private theorem map_all_bish_comparisons (l : List ComparisonMap)
    (h : ∀ c ∈ l, comparison_is_non_archimedean c = true) :
    ∀ x ∈ l.map (fun c => (comparison_signature c).level), x = CRMLevel.BISH := by
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨c, hc, hcx⟩ := hx
  rw [← hcx]
  exact non_archimedean_comparison_is_bish c (h c hc)

/-- Appending lists where all elements are BISH preserves the all-BISH property. -/
private theorem append_all_bish (l₁ l₂ : List CRMLevel)
    (h₁ : ∀ x ∈ l₁, x = CRMLevel.BISH)
    (h₂ : ∀ x ∈ l₂, x = CRMLevel.BISH) :
    ∀ x ∈ l₁ ++ l₂, x = CRMLevel.BISH := by
  intro x hx
  rw [List.mem_append] at hx
  cases hx with
  | inl h => exact h₁ x h
  | inr h => exact h₂ x h

/-- foldl join BISH l = BISH when all elements are BISH,
    extended to arbitrary initial accumulator: if acc = BISH and all l = BISH,
    then foldl join acc l = BISH. -/
private theorem foldl_join_bish_acc (l : List CRMLevel) (acc : CRMLevel)
    (hacc : acc = .BISH) (h : ∀ x ∈ l, x = CRMLevel.BISH) :
    l.foldl CRMLevel.join acc = .BISH := by
  subst hacc
  exact CRMLevel.foldl_join_bish l h


/-! ## The Archimedean Obstruction Theorem -/

/-- **Theorem A (Archimedean Obstruction).**
    Any proof path that avoids the Betti, Hodge, and automorphic realizations,
    and avoids comparisons through them, has BISH signature.

    This is the central result of the paper: ℝ is the unique source of
    non-constructive content in arithmetic geometry. -/
theorem archimedean_obstruction (p : ProofPath)
    (h_real : ∀ r ∈ p.realizations, is_non_archimedean r = true)
    (h_comp : ∀ c ∈ p.comparisons, comparison_is_non_archimedean c = true) :
    proof_signature p = .BISH := by
  unfold proof_signature
  -- All realization signatures are BISH
  have hr := map_all_bish_realizations p.realizations h_real
  -- All comparison signatures are BISH
  have hc := map_all_bish_comparisons p.comparisons h_comp
  -- The motive signature is BISH
  have hm : ∀ x ∈ [motive_signature.level], x = CRMLevel.BISH := by
    intro x hx; simp at hx; subst hx; rfl
  -- Combine: all elements in the concatenated list are BISH
  have hall := append_all_bish _ _ (append_all_bish _ _ hm hr) hc
  -- foldl join BISH over all-BISH list = BISH
  exact foldl_join_bish_acc _ .BISH rfl hall
