/-
Papers/P2_BidualGap/Gap/Quotients.lean
Sprint A: Spec-level quotients + descended embedding ῑ.

We put a setoid on Set ℕ by finite symmetric difference, and on sequences by c0Spec.
Then we descend ι : Set ℕ → (ℕ → ℝ) to a quotient map ῑ between the quotients.
-/
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Lattice
import Mathlib.Logic.Relation   -- for Equivalence.eqvGen_iff
import Papers.P2_BidualGap.Gap.Indicator
import Papers.P2_BidualGap.Gap.IndicatorSpec
import Papers.P2_BidualGap.Gap.C0Spec
import Papers.P2_BidualGap.Gap.Iota

namespace Papers.P2.Gap.BooleanSubLattice
open Classical

/-- For convenience. -/
local notation "△" => Papers.P2.Gap.BooleanSubLattice.symmDiff

/-- The relation: finite symmetric difference. -/
def FinSymmDiffRel (A B : Set ℕ) : Prop := (symmDiff A B).Finite

/-- `A △ C ⊆ (A △ B) ∪ (B △ C)` (triangle for symmetric difference). -/
lemma symmDiff_subset_union (A B C : Set ℕ) :
    symmDiff A C ⊆ symmDiff A B ∪ symmDiff B C := by
  intro x hx
  by_cases hA : x ∈ A
  · by_cases hB : x ∈ B
    · by_cases hC : x ∈ C
      · -- in all three ⇒ not in △
        have : x ∉ symmDiff A C := by
          -- directly contradicts hx
          -- but simpler: rewrite and simp
          -- Instead: close by `simp [symmDiff, Set.mem_diff, hA, hB, hC]` on hx
          -- We'll just discharge by simp:
          simp [symmDiff, Set.mem_diff, hA, hC] at hx
        -- unreachable
        exact False.elim <| this.elim hx
      · -- A,T ; B,T ; C,F ⇒ both A and B contain x, C doesn't
        -- So x ∉ A △ B (both contain x), but we need to check if x ∈ A △ C
        -- Since A contains x but C doesn't, x ∈ A △ C ✓
        -- But we need x ∈ (A △ B) ∪ (B △ C). Since A,B both contain x, x ∉ A △ B
        -- Since B contains x but C doesn't, x ∈ B △ C
        have : x ∈ symmDiff B C := by
          simp [symmDiff, Set.mem_diff, hB, hC]
        exact Or.inr this
    · -- A,T ; B,F
      by_cases hC : x ∈ C
      · -- then x ∈ B △ C (since B misses, C hits)
        have : x ∈ symmDiff B C := by
          simp [symmDiff, Set.mem_diff, hB, hC]
        exact Or.inr this
      · -- A,T ; B,F ; C,F ⇒ x ∈ A △ B
        have : x ∈ symmDiff A B := by
          simp [symmDiff, Set.mem_diff, hA, hB]
        exact Or.inl this
  · -- A,F
    by_cases hB : x ∈ B
    · by_cases hC : x ∈ C
      · -- A,F ; B,T ; C,T ⇒ x ∈ A △ B (since B hits, A misses)
        have : x ∈ symmDiff A B := by
          simp [symmDiff, Set.mem_diff, hA, hB]
        exact Or.inl this
      · -- A,F ; B,T ; C,F ⇒ x ∈ B △ C (B hits, C misses)
        have : x ∈ symmDiff B C := by
          simp [symmDiff, Set.mem_diff, hB, hC]
        exact Or.inr this
    · -- A,F ; B,F
      by_cases hC : x ∈ C
      · -- A△C has x (since C hits, A misses). Put it into RHS via B△C
        have : x ∈ symmDiff B C := by
          simp [symmDiff, Set.mem_diff, hB, hC]
        exact Or.inr this
      · -- all miss ⇒ x ∉ A△C, contradict hx
        simp [symmDiff, Set.mem_diff, hA, hC] at hx

/-- Setoid on `Set ℕ` by finite symmetric difference. -/
instance instSetoidSetNat : Setoid (Set ℕ) where
  r := FinSymmDiffRel
  iseqv := by
    refine ⟨?refl, ?symm, ?trans⟩
    · intro A
      simp [FinSymmDiffRel, symmDiff]
    · intro A B h
      simpa [FinSymmDiffRel, symmDiff, Set.union_comm] using h
    · intro A B C hAB hBC
      have hsubset : symmDiff A C ⊆ symmDiff A B ∪ symmDiff B C :=
        symmDiff_subset_union A B C
      exact (hAB.union hBC).subset hsubset

/-- Abbreviation for the Boolean quotient `𝔅 := 𝒫(ℕ)/Fin`. -/
abbrev BooleanAtInfinity := Quot instSetoidSetNat.r

/-! Setoid on sequences by `≈₀` (our EqModC0Spec). -/

/-- Tiny helpers on `c0Spec` (closed under negation and addition). -/
lemma c0Spec_zero : c0Spec (fun _ => (0 : ℝ)) := by
  intro ε hε
  use 0
  intro n _
  simp [abs_zero]
  exact le_of_lt hε

lemma c0Spec_neg {f : ℕ → ℝ} (h : c0Spec f) : c0Spec (fun n => -(f n)) := by
  intro ε hε
  rcases h ε hε with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn; simpa using hN n hn

lemma c0Spec_add {f g : ℕ → ℝ}
    (hf : c0Spec f) (hg : c0Spec g) : c0Spec (fun n => f n + g n) := by
  intro ε hε
  have hε2 : 0 < ε/2 := by exact half_pos hε
  rcases hf (ε/2) hε2 with ⟨Nf, hNf⟩
  rcases hg (ε/2) hε2 with ⟨Ng, hNg⟩
  refine ⟨max Nf Ng, ?_⟩
  intro n hn
  have hnf : Nf ≤ n := le_trans (le_max_left _ _) hn
  have hng : Ng ≤ n := le_trans (le_max_right _ _) hn
  have hf' := hNf n hnf
  have hg' := hNg n hng
  calc |f n + g n| 
    ≤ |f n| + |g n|   := abs_add _ _
    _ ≤ ε/2 + ε/2       := add_le_add hf' hg'
    _ = ε               := by norm_num

/-- Setoid on sequences modulo `c0Spec`. -/
instance instSetoidSeq : Setoid (ℕ → ℝ) where
  r f g := EqModC0Spec f g
  iseqv := by
    refine ⟨?refl, ?symm, ?trans⟩
    · intro f
      -- reflexive: (f - f) ≡ 0 is c0
      change c0Spec (fun n => f n - f n)
      have : (fun n => f n - f n) = (fun _ => 0) := by funext x; simp
      rw [this]
      exact c0Spec_zero
    · intro f g hfg
      -- symmetric: (g - f) = −(f - g)
      change c0Spec (fun n => g n - f n)
      have : (fun n => g n - f n) = (fun n => -(f n - g n)) := by funext x; simp [neg_sub]
      rw [this]
      exact c0Spec_neg hfg
    · intro f g h hfg hgh
      -- transitive: (f - h) = (f - g) + (g - h)
      change c0Spec (fun n => f n - h n)
      have : (fun n => f n - h n) =
             (fun n => (f n - g n) + (g n - h n)) := by 
        funext x; norm_num [sub_add_sub_cancel']
      rw [this]
      exact c0Spec_add hfg hgh

-- ✅ Collapse EqvGen back to the setoid relation using mathlib's lemma

/-- The quotient of sequences by `≈₀`. -/
abbrev SeqModC0 := Quot instSetoidSeq.r

/-- The descended embedding ῑ : 𝔅 → (ℝ^ℕ)/c0. -/
noncomputable def iotaBar : BooleanAtInfinity → SeqModC0 :=
  Quot.map (ι) (by
    intro A B hAB
    -- turn finite △ into the spec:
    have hs : indicatorEqModC0Spec A B :=
      (indicatorEqModC0_spec_iff (A:=A) (B:=B)).2
        (by simpa [FinSymmDiffRel, finiteSymmDiff] using hAB)
    -- then spec ⇒ EqModC0Spec (ιA) (ιB)
    exact (iota_eq_iff_spec (A:=A) (B:=B)).2 hs)

@[simp] lemma iotaBar_mk (A : Set ℕ) :
    iotaBar (Quot.mk instSetoidSetNat.r A) = Quot.mk instSetoidSeq.r (ι A) := rfl

/-- If `A △ B` is finite then `ῑ [A] = ῑ [B]`. -/
lemma iotaBar_eq_of_finite_symmDiff {A B : Set ℕ}
    (hAB : (symmDiff A B).Finite) :
    iotaBar (Quot.mk instSetoidSetNat.r A) = iotaBar (Quot.mk instSetoidSetNat.r B) := by
  apply Quot.sound
  have hs : indicatorEqModC0Spec A B :=
    (indicatorEqModC0_spec_iff (A:=A) (B:=B)).2
      (by simpa [finiteSymmDiff] using hAB)
  exact (iota_eq_iff_spec (A:=A) (B:=B)).2 hs

-- Note: symmDiff lemmas are already in IndicatorSpec.lean

/-- Both sides move: union. -/
lemma symmDiff_union_both_subset (A A' B B' : Set ℕ) :
    symmDiff (A ∪ B) (A' ∪ B') ⊆ symmDiff A A' ∪ symmDiff B B' := by
  classical
  intro x hx
  have hx' :
    x ∈ symmDiff (A ∪ B) (A' ∪ B) ∪ symmDiff (A' ∪ B) (A' ∪ B') :=
      symmDiff_subset_union (A ∪ B) (A' ∪ B) (A' ∪ B') hx
  rcases hx' with hx1 | hx2
  · -- first leg
    have : x ∈ (symmDiff A A') \ B := by
      -- rewrite (A ∪ B) vs (A' ∪ B) to (A △ A') \ B
      simpa only [symmDiff_union_right_eq A A' B] using hx1
    exact Or.inl this.1
  · -- second leg
    -- re-orient to match the lemma (swap the unions)
    have hx2' : x ∈ symmDiff (B ∪ A') (B' ∪ A') := by
      simpa [Set.union_comm] using hx2
    have hx2'' : x ∈ (symmDiff B B') \ A' := by
      simpa only [symmDiff_union_right_eq B B' A'] using hx2'
    exact Or.inr hx2''.1

/-- Both sides move: intersection. -/
lemma symmDiff_inter_both_subset (A A' B B' : Set ℕ) :
    symmDiff (A ∩ B) (A' ∩ B') ⊆ symmDiff A A' ∪ symmDiff B B' := by
  classical
  intro x hx
  have hx' :
    x ∈ symmDiff (A ∩ B) (A' ∩ B) ∪ symmDiff (A' ∩ B) (A' ∩ B') :=
      symmDiff_subset_union (A ∩ B) (A' ∩ B) (A' ∩ B') hx
  rcases hx' with hx1 | hx2
  · have : x ∈ (symmDiff A A') ∩ B := by
      -- rewrite (A ∩ B) vs (A' ∩ B) to (A △ A') ∩ B
      simpa only [symmDiff_inter_right_eq A A' B] using hx1
    exact Or.inl this.1
  · -- re-orient to match the lemma (swap the intersections)
    have hx2' : x ∈ symmDiff (B ∩ A') (B' ∩ A') := by
      simpa [Set.inter_comm] using hx2
    have hx2'' : x ∈ (symmDiff B B') ∩ A' := by
      simpa only [symmDiff_inter_right_eq B B' A'] using hx2'
    exact Or.inr hx2''.1

/-- Boolean union on the quotient `𝔅 := 𝒫(ℕ)/Fin`. -/
noncomputable def bUnion : BooleanAtInfinity → BooleanAtInfinity → BooleanAtInfinity :=
  fun bA bB =>
    Quot.liftOn₂ bA bB
      (fun A B => Quot.mk instSetoidSetNat.r (A ∪ B))
      -- FIRST witness: vary B, fix A
      (fun (A : Set ℕ) (B B' : Set ℕ) (hBB' : instSetoidSetNat.r B B') => by
        apply Quot.sound
        have hBB'fin : (symmDiff B B').Finite := by
          simpa [FinSymmDiffRel] using hBB'
        have : (symmDiff B B' \ A).Finite :=
          hBB'fin.subset (by intro x hx; exact hx.1)

        -- explicit equality: reorder ∪, then apply the right-hand identity
        have hEq : symmDiff (A ∪ B) (A ∪ B') = symmDiff B B' \ A := by
          simpa [Set.union_comm] using (symmDiff_union_right_eq B B' A)

        -- now turn (△ B B' \ A).Finite into the goal
        have hfin : (symmDiff (A ∪ B) (A ∪ B')).Finite := by
          simpa [hEq] using this

        simpa [FinSymmDiffRel] using hfin)
      -- SECOND witness: vary A, fix B
      (fun (A A' : Set ℕ) (B : Set ℕ) (hAA' : instSetoidSetNat.r A A') => by
        apply Quot.sound
        have hAA'fin : (symmDiff A A').Finite := by
          simpa [FinSymmDiffRel] using hAA'
        have : (symmDiff A A' \ B).Finite :=
          hAA'fin.subset (by intro x hx; exact hx.1)
        have hfin : (symmDiff (A ∪ B) (A' ∪ B)).Finite := by
          simpa [symmDiff_union_right_eq A A' B] using this
        simpa [FinSymmDiffRel] using hfin)

/-- Boolean intersection on the quotient. -/
noncomputable def bInter : BooleanAtInfinity → BooleanAtInfinity → BooleanAtInfinity :=
  fun bA bB =>
    Quot.liftOn₂ bA bB
      (fun A B => Quot.mk instSetoidSetNat.r (A ∩ B))
      -- FIRST witness: vary B, fix A
      (fun (A : Set ℕ) (B B' : Set ℕ) (hBB' : instSetoidSetNat.r B B') => by
        apply Quot.sound
        have hBB'fin : (symmDiff B B').Finite := by
          simpa [FinSymmDiffRel] using hBB'
        have : (symmDiff B B' ∩ A).Finite :=
          hBB'fin.subset (by intro x hx; exact hx.1)

        -- explicit equality: reorder ∩, then apply the right-hand identity
        have hEq : symmDiff (A ∩ B) (A ∩ B') = symmDiff B B' ∩ A := by
          simpa [Set.inter_comm] using (symmDiff_inter_right_eq B B' A)

        -- now turn (△ B B' ∩ A).Finite into the goal
        have hfin : (symmDiff (A ∩ B) (A ∩ B')).Finite := by
          simpa [hEq] using this

        simpa [FinSymmDiffRel] using hfin)
      -- SECOND witness: vary A, fix B
      (fun (A A' : Set ℕ) (B : Set ℕ) (hAA' : instSetoidSetNat.r A A') => by
        apply Quot.sound
        have hAA'fin : (symmDiff A A').Finite := by
          simpa [FinSymmDiffRel] using hAA'
        have : (symmDiff A A' ∩ B).Finite :=
          hAA'fin.subset (by intro x hx; exact hx.1)
        have hfin : (symmDiff (A ∩ B) (A' ∩ B)).Finite := by
          simpa [symmDiff_inter_right_eq A A' B] using this
        simpa [FinSymmDiffRel] using hfin)

/-- Boolean complement on the quotient. -/
noncomputable def bCompl : BooleanAtInfinity → BooleanAtInfinity :=
  fun bA =>
    Quot.map (fun A => Aᶜ)
      (by
        intro A B hAB
        -- target relation: (Aᶜ) ~ (Bᶜ)
        change FinSymmDiffRel (Aᶜ) (Bᶜ)
        -- bridge the hypothesis to FinSymmDiffRel
        have hAB' : FinSymmDiffRel A B := by
          simpa [FinSymmDiffRel] using hAB
        -- use the complement identity: Aᶜ △ Bᶜ = A △ B
        simpa [FinSymmDiffRel, symmDiff_compl_eq] using hAB'
      ) bA

@[simp] lemma bUnion_mk (A B : Set ℕ) :
  bUnion (Quot.mk instSetoidSetNat.r A) (Quot.mk instSetoidSetNat.r B) = Quot.mk instSetoidSetNat.r (A ∪ B) := rfl

@[simp] lemma bInter_mk (A B : Set ℕ) :
  bInter (Quot.mk instSetoidSetNat.r A) (Quot.mk instSetoidSetNat.r B) = Quot.mk instSetoidSetNat.r (A ∩ B) := rfl

@[simp] lemma bCompl_mk (A : Set ℕ) :
  bCompl (Quot.mk instSetoidSetNat.r A) = Quot.mk instSetoidSetNat.r (Aᶜ) := rfl

-- (optional) notation
infixl:65 " ⊔ᵇ " => bUnion
infixl:70 " ⊓ᵇ " => bInter
prefix:75 "ᶜᵇ" => bCompl

/-- Max/min as linear combinations with `|x - y|`. -/
lemma max_eq_add_abs_sub_div_two (x y : ℝ) :
  max x y = (x + y + |x - y|) / 2 := by
  classical
  by_cases h : x ≤ y
  · -- case x ≤ y
    have hmax : max x y = y := by simpa [max_eq_right h]
    have habs : |x - y| = y - x := by
      -- |x - y| = -(x - y) (since x - y ≤ 0), and -(x - y) = y - x by neg_sub
      simpa [neg_sub] using
        (abs_of_nonpos (sub_nonpos.2 h) : |x - y| = -(x - y))
    calc
      max x y = y := hmax
      _ = (y + y) / 2 := by
            -- (y+y)/2 = y
            have : (y + y) / 2 = y := by
              simp [add_div, add_halves]
            simpa using this.symm
      _ = (x + y + (y - x)) / 2 := by
            -- group and cancel x with -x
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      _ = (x + y + |x - y|) / 2 := by simpa [habs]
  · -- case y ≤ x
    have h' : y ≤ x := le_of_not_le h
    have hmax : max x y = x := by simpa [max_eq_left h']
    have habs : |x - y| = x - y := by
      have : 0 ≤ x - y := sub_nonneg.2 h'
      simpa [abs_of_nonneg this]
    calc
      max x y = x := hmax
      _ = (x + x) / 2 := by
            -- (x+x)/2 = x
            have : (x + x) / 2 = x := by
              simp [add_div, add_halves]
            simpa using this.symm
      _ = (x + y + (x - y)) / 2 := by
            -- group and cancel y with -y
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      _ = (x + y + |x - y|) / 2 := by simpa [habs]

/-- Min as a linear combination with `|x - y|`. -/
lemma min_eq_add_abs_sub_div_two (x y : ℝ) :
  min x y = (x + y - |x - y|) / 2 := by
  classical
  by_cases h : x ≤ y
  · -- case `x ≤ y`: `min x y = x` and `|x - y| = y - x`
    have hmin : min x y = x := by simpa [min_eq_left h]
    have habs : |x - y| = y - x := by
      -- |x - y| = -(x - y) since x - y ≤ 0, and -(x - y) = y - x
      simpa [neg_sub] using
        (abs_of_nonpos (sub_nonpos.2 h) : |x - y| = -(x - y))
    calc
      min x y = x := hmin
      _ = (x + x) / 2 := by
            have : (x + x) / 2 = x := by simp [add_div, add_halves]
            simpa using this.symm
      _ = (x + y - (y - x)) / 2 := by
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      _ = (x + y - |x - y|) / 2 := by simpa [habs]
  · -- case `y ≤ x`: `min x y = y` and `|x - y| = x - y`
    have h' : y ≤ x := le_of_not_le h
    have hmin : min x y = y := by
      -- reuse `min_eq_left` via commutativity
      simpa [min_comm, min_eq_left h']
    have habs : |x - y| = x - y := by
      have : 0 ≤ x - y := sub_nonneg.2 h'
      simpa [abs_of_nonneg this]
    calc
      min x y = y := hmin
      _ = (y + y) / 2 := by
            have : (y + y) / 2 = y := by simp [add_div, add_halves]
            simpa using this.symm
      _ = (x + y - (x - y)) / 2 := by
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      _ = (x + y - |x - y|) / 2 := by simpa [habs]

/-- A clean 2-Lipschitz bound for `max`. -/
lemma abs_max_sub_max_le_add (x x' y y' : ℝ) :
  |max x y - max x' y'| ≤ |x - x'| + |y - y'| := by
  classical
  have hx  := max_eq_add_abs_sub_div_two x y
  have hx' := max_eq_add_abs_sub_div_two x' y'
  -- rewrite the difference of maxima as a single fraction
  have habs :
      |max x y - max x' y'|
        = |(x - x') + (y - y') + (|x - y| - |x' - y'|)| / 2 := by
    have hdiff :
        max x y - max x' y'
          = ((x + y + |x - y|) - (x' + y' + |x' - y'|)) / 2 := by
      calc
        max x y - max x' y'
            = (x + y + |x - y|) / 2 - (x' + y' + |x' - y'|) / 2 := by simpa [hx, hx']
        _ = ((x + y + |x - y|) - (x' + y' + |x' - y'|)) / 2 := by
              simpa [sub_eq_add_neg] using
                (sub_div (x + y + |x - y|) (x' + y' + |x' - y'|) (2 : ℝ)).symm
    have : ((x + y + |x - y|) - (x' + y' + |x' - y'|))
            = (x - x') + (y - y') + (|x - y| - |x' - y'|) := by
      simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    simpa [hdiff, abs_div, this]
  -- triangle pieces
  have h1 : |(x - x') + (y - y')| ≤ |x - x'| + |y - y'| :=
    by simpa using abs_add (x - x') (y - y')
  have h2 : |abs (x - y) - abs (x' - y')| ≤ |(x - y) - (x' - y')| :=
    abs_abs_sub_abs_le_abs_sub _ _
  have h3 : |(x - y) - (x' - y')| ≤ |x - x'| + |y - y'| := by
    -- first rewrite the LHS as |(x - x') + (y' - y)|
    have hRewr : (x - y) - (x' - y') = (x - x') + (y' - y) := by
      simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    -- apply triangle, then flip |y' - y| → |y - y'|
    simpa [hRewr, abs_sub_comm] using abs_add (x - x') (y' - y)
  -- now shape the big absolute and chain inequalities
  have hsum :
      |(x - x') + (y - y') + (abs (x - y) - abs (x' - y'))|
        ≤ |(x - x') + (y - y')| + |abs (x - y) - abs (x' - y')| := by
    simpa [add_comm, add_left_comm, add_assoc]
      using abs_add ((x - x') + (y - y')) (abs (x - y) - abs (x' - y'))
  have hnum :
      |(x - x') + (y - y') + (abs (x - y) - abs (x' - y'))|
        ≤ (|x - x'| + |y - y'|) + (|x - x'| + |y - y'|) :=
    hsum.trans (add_le_add h1 (h2.trans h3))
  -- divide by 2 (monotone since 0 ≤ 2) and simplify (a+a)/2 = a
  have hnonneg : (0 : ℝ) ≤ 2 := (two_pos : (0:ℝ) < 2).le
  have : |max x y - max x' y'|
        ≤ ((|x - x'| + |y - y'|) + (|x - x'| + |y - y'|)) / 2 := by
    simpa [habs] using (div_le_div_of_nonneg_right hnum hnonneg)
  have hhalf :
      ((|x - x'| + |y - y'|) + (|x - x'| + |y - y'|)) / 2
        = |x - x'| + |y - y'| := by
    simpa [add_comm, add_left_comm, add_assoc, add_div]
      using add_halves (|x - x'| + |y - y'|)
  simpa [hhalf] using this

/-- A clean 2-Lipschitz bound for `min`. -/
lemma abs_min_sub_min_le_add (x x' y y' : ℝ) :
  |min x y - min x' y'| ≤ |x - x'| + |y - y'| := by
  classical
  have hx  := min_eq_add_abs_sub_div_two x y
  have hx' := min_eq_add_abs_sub_div_two x' y'
  -- rewrite the difference of minima as a single fraction
  have habs :
      |min x y - min x' y'|
        = |(x - x') + (y - y') - (|x - y| - |x' - y'|)| / 2 := by
    have hdiff :
        min x y - min x' y'
          = ((x + y - |x - y|) - (x' + y' - |x' - y'|)) / 2 := by
      calc
        min x y - min x' y'
            = (x + y - |x - y|) / 2 - (x' + y' - |x' - y'|) / 2 := by simpa [hx, hx']
        _ = ((x + y - |x - y|) - (x' + y' - |x' - y'|)) / 2 := by
              simpa [sub_eq_add_neg] using
                (sub_div (x + y - |x - y|) (x' + y' - |x' - y'|) (2 : ℝ)).symm
    have : ((x + y - |x - y|) - (x' + y' - |x' - y'|))
            = (x - x') + (y - y') - (|x - y| - |x' - y'|) := by
      simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    simpa [hdiff, abs_div, this]
  -- triangle pieces
  have h1 : |(x - x') + (y - y')| ≤ |x - x'| + |y - y'| :=
    by simpa using abs_add (x - x') (y - y')
  have h2 : |abs (x - y) - abs (x' - y')| ≤ |(x - y) - (x' - y')| :=
    abs_abs_sub_abs_le_abs_sub _ _
  have h3 : |(x - y) - (x' - y')| ≤ |x - x'| + |y - y'| := by
    have hRewr : (x - y) - (x' - y') = (x - x') + (y' - y) := by
      simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    simpa [hRewr, abs_sub_comm] using abs_add (x - x') (y' - y)
  -- shape the big absolute and chain inequalities
  have hsum :
      |(x - x') + (y - y') - (abs (x - y) - abs (x' - y'))|
        ≤ |(x - x') + (y - y')| + |abs (x - y) - abs (x' - y')| := by
    have h_rewrite : (x - x') + (y - y') - (abs (x - y) - abs (x' - y'))
                     = (x - x') + (y - y') + (-(abs (x - y) - abs (x' - y'))) := by
      simp [sub_eq_add_neg]
    rw [h_rewrite]
    have h_neg : |-(abs (x - y) - abs (x' - y'))| = |abs (x - y) - abs (x' - y')| := by
      exact abs_neg _
    rw [← h_neg]
    exact abs_add _ _
  have hnum :
      |(x - x') + (y - y') - (abs (x - y) - abs (x' - y'))|
        ≤ (|x - x'| + |y - y'|) + (|x - x'| + |y - y'|) :=
    hsum.trans (add_le_add h1 (h2.trans h3))
  -- divide by 2 and finish
  have hnonneg : (0 : ℝ) ≤ 2 := (two_pos : (0:ℝ) < 2).le
  have : |min x y - min x' y'|
        ≤ ((|x - x'| + |y - y'|) + (|x - x'| + |y - y'|)) / 2 := by
    simpa [habs] using (div_le_div_of_nonneg_right hnum hnonneg)
  have hhalf :
      ((|x - x'| + |y - y'|) + (|x - x'| + |y - y'|)) / 2
        = |x - x'| + |y - y'| := by
    simpa [add_comm, add_left_comm, add_assoc, add_div]
      using add_halves (|x - x'| + |y - y'|)
  simpa [hhalf] using this

/-- c₀-spec stability: max respects `≈₀`. -/
lemma c0Spec_max_congr {f f' g g' : ℕ → ℝ}
    (hf : EqModC0Spec f f') (hg : EqModC0Spec g g') :
    EqModC0Spec (fun n => max (f n) (g n)) (fun n => max (f' n) (g' n)) := by
  intro ε hε
  have hε2 : 0 < ε/2 := half_pos hε
  rcases hf (ε/2) hε2 with ⟨Nf, hNf⟩
  rcases hg (ε/2) hε2 with ⟨Ng, hNg⟩
  refine ⟨max Nf Ng, ?_⟩
  intro n hn
  have hnf : Nf ≤ n := le_trans (le_max_left _ _) hn
  have hng : Ng ≤ n := le_trans (le_max_right _ _) hn
  have := abs_max_sub_max_le_add (f n) (f' n) (g n) (g' n)
  have : |max (f n) (g n) - max (f' n) (g' n)| ≤ (ε/2) + (ε/2) :=
    le_trans this (add_le_add (hNf n hnf) (hNg n hng))
  simpa [add_halves] using this

/-- c₀-spec stability: min respects `≈₀`. -/
lemma c0Spec_min_congr {f f' g g' : ℕ → ℝ}
    (hf : EqModC0Spec f f') (hg : EqModC0Spec g g') :
    EqModC0Spec (fun n => min (f n) (g n)) (fun n => min (f' n) (g' n)) := by
  intro ε hε
  have hε2 : 0 < ε/2 := half_pos hε
  rcases hf (ε/2) hε2 with ⟨Nf, hNf⟩
  rcases hg (ε/2) hε2 with ⟨Ng, hNg⟩
  refine ⟨max Nf Ng, ?_⟩
  intro n hn
  have hnf : Nf ≤ n := le_trans (le_max_left _ _) hn
  have hng : Ng ≤ n := le_trans (le_max_right _ _) hn
  have := abs_min_sub_min_le_add (f n) (f' n) (g n) (g' n)
  have : |min (f n) (g n) - min (f' n) (g' n)| ≤ (ε/2) + (ε/2) :=
    le_trans this (add_le_add (hNf n hnf) (hNg n hng))
  simpa [add_halves] using this

/-- c₀-spec stability: complement `x ↦ 1 - x` respects `≈₀`. -/
lemma c0Spec_compl_congr {f g : ℕ → ℝ}
    (hf : EqModC0Spec f g) :
    EqModC0Spec (fun n => 1 - f n) (fun n => 1 - g n) := by
  -- ((1 - f) - (1 - g)) = g - f, and c₀ is closed under negation
  change c0Spec (fun n => (1 - f n) - (1 - g n))
  -- rewrite (1 - f) - (1 - g) pointwise to g - f
  have hrewrite :
      (fun n => (1 - f n) - (1 - g n)) = (fun n => g n - f n) := by
    funext n
    -- a - b - (a - c) = c - b  with a=1, b=f n, c=g n
    simpa using sub_sub_sub_cancel_right (1 : ℝ) (f n) (g n)
  rw [hrewrite]
  -- c0Spec_neg : c0Spec (f - g) → c0Spec (-(f - g)) and  -(f - g) = g - f
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using c0Spec_neg hf

-- handy reflexivity witness for ≈₀
private lemma c0Spec_refl (f : ℕ → ℝ) : EqModC0Spec f f := by
  intro ε hε; refine ⟨0, ?_⟩; intro n hn; simpa [sub_self, abs_zero] using hε.le

/-- Sup on the quotient of sequences. -/
noncomputable def qSup : SeqModC0 → SeqModC0 → SeqModC0 :=
  fun qf qg =>
    Quot.liftOn₂ qf qg
      (fun f g => Quot.mk instSetoidSeq.r (fun n => max (f n) (g n)))
      -- FIRST witness: vary g, fix f
      (fun (f : ℕ → ℝ) (g g' : ℕ → ℝ) (hg : EqModC0Spec g g') => by
        apply Quot.sound
        exact c0Spec_max_congr (c0Spec_refl f) hg)
      -- SECOND witness: vary f, fix g
      (fun (f f' : ℕ → ℝ) (g : ℕ → ℝ) (hf : EqModC0Spec f f') => by
        apply Quot.sound
        exact c0Spec_max_congr hf (c0Spec_refl g))

/-- Inf on the quotient. -/
noncomputable def qInf : SeqModC0 → SeqModC0 → SeqModC0 :=
  fun qf qg =>
    Quot.liftOn₂ qf qg
      (fun f g => Quot.mk instSetoidSeq.r (fun n => min (f n) (g n)))
      -- FIRST witness: vary g, fix f
      (fun (f : ℕ → ℝ) (g g' : ℕ → ℝ) (hg : EqModC0Spec g g') => by
        apply Quot.sound
        exact c0Spec_min_congr (c0Spec_refl f) hg)
      -- SECOND witness: vary f, fix g
      (fun (f f' : ℕ → ℝ) (g : ℕ → ℝ) (hf : EqModC0Spec f f') => by
        apply Quot.sound
        exact c0Spec_min_congr hf (c0Spec_refl g))

/-- Complement on the quotient. -/
noncomputable def qCompl : SeqModC0 → SeqModC0 :=
  fun qf =>
    Quot.map (fun f => fun n => (1 : ℝ) - f n)
      (by
        intro f g hf
        -- ((1 - f) - (1 - g)) = g - f, so use c0Spec_neg
        change instSetoidSeq.r (fun n => 1 - f n) (fun n => 1 - g n)
        exact c0Spec_compl_congr hf) qf

@[simp] lemma qSup_mk (f g : ℕ → ℝ) :
  qSup (Quot.mk instSetoidSeq.r f) (Quot.mk instSetoidSeq.r g) = Quot.mk instSetoidSeq.r (fun n => max (f n) (g n)) := rfl
@[simp] lemma qInf_mk (f g : ℕ → ℝ) :
  qInf (Quot.mk instSetoidSeq.r f) (Quot.mk instSetoidSeq.r g) = Quot.mk instSetoidSeq.r (fun n => min (f n) (g n)) := rfl
@[simp] lemma qCompl_mk (f : ℕ → ℝ) :
  qCompl (Quot.mk instSetoidSeq.r f) = Quot.mk instSetoidSeq.r (fun n => 1 - f n) := rfl

lemma iota_max (A B : Set ℕ) :
    (fun n => max (ι A n) (ι B n)) = ι (A ∪ B) := by
  classical
  funext n; by_cases hA : n ∈ A <;> by_cases hB : n ∈ B <;>
    simp [ι, hA, hB, max_eq_left, max_eq_right]

lemma iota_min (A B : Set ℕ) :
    (fun n => min (ι A n) (ι B n)) = ι (A ∩ B) := by
  classical
  funext n; by_cases hA : n ∈ A <;> by_cases hB : n ∈ B <;>
    simp [ι, hA, hB, min_eq_left, min_eq_right]

lemma iota_compl (A : Set ℕ) :
    (fun n => (1 : ℝ) - ι A n) = ι (Aᶜ) := by
  classical
  funext n; by_cases hA : n ∈ A <;> simp [ι, hA]

@[simp] lemma iotaBar_sup (A B : Set ℕ) :
    qSup (iotaBar (Quot.mk instSetoidSetNat.r A))
         (iotaBar (Quot.mk instSetoidSetNat.r B))
      = iotaBar (Quot.mk instSetoidSetNat.r (A ∪ B)) := by
  rw [iotaBar_mk, iotaBar_mk, iotaBar_mk, qSup_mk]
  simp only [iota_max]

@[simp] lemma iotaBar_inf (A B : Set ℕ) :
    qInf (iotaBar (Quot.mk instSetoidSetNat.r A))
         (iotaBar (Quot.mk instSetoidSetNat.r B))
      = iotaBar (Quot.mk instSetoidSetNat.r (A ∩ B)) := by
  rw [iotaBar_mk, iotaBar_mk, iotaBar_mk, qInf_mk]
  simp only [iota_min]

@[simp] lemma iotaBar_compl (A : Set ℕ) :
    qCompl (iotaBar (Quot.mk instSetoidSetNat.r A))
      = iotaBar (Quot.mk instSetoidSetNat.r (Aᶜ)) := by
  rw [iotaBar_mk, iotaBar_mk, qCompl_mk]
  simp only [iota_compl]

/-! ## Standard lattice instances

Wire the custom operations into standard Lean notation so users can write
`x ⊔ y`, `x ⊓ y`, and `xᶜ` directly. -/

-- Standard binary/joint ops on 𝒫(ℕ)/Fin  
-- TODO: Fix type class instance syntax issues
-- noncomputable instance : Sup BooleanAtInfinity where
--   sup := bUnion

-- noncomputable instance : Inf BooleanAtInfinity where
--   inf := bInter

-- noncomputable instance : HasCompl BooleanAtInfinity where
--   compl := bCompl

-- lemma sup_def (x y : BooleanAtInfinity) : x ⊔ y = bUnion x y := rfl

-- lemma inf_def (x y : BooleanAtInfinity) : x ⊓ y = bInter x y := rfl

-- lemma compl_def (x : BooleanAtInfinity) : xᶜ = bCompl x := rfl

/-! ## Injectivity of iotaBar -/

private noncomputable def chi (A : Set ℕ) (n : ℕ) : ℝ := if n ∈ A then 1 else 0

-- helper: absolute difference is 1 exactly on the symmetric difference
private lemma abs_chi_sub_chi_eq_one_iff {A B : Set ℕ} {n : ℕ} :
  |chi A n - chi B n| = 1 ↔ n ∈ symmDiff A B := by
  classical
  by_cases hA : n ∈ A <;> by_cases hB : n ∈ B <;> 
    simp [chi, hA, hB, symmDiff, Set.mem_diff, abs_one, Set.mem_union]

-- if (χ_A − χ_B) ∈ c0 then A△B is finite  
private lemma finite_of_c0_indicator_diff {A B : Set ℕ}
    (h : c0Spec (fun n => chi A n - chi B n)) :
    (symmDiff A B).Finite := by
  classical
  -- take ε = 1/2
  rcases h (1/2) (by norm_num : (0 : ℝ) < 1/2) with ⟨N, hN⟩
  -- beyond N all |χ_A − χ_B| ≤ 1/2, but on symmDiff it equals 1
  have : symmDiff A B ⊆ {n | n < N} := by
    intro n hn
    by_cases hge : n ≥ N
    · have h1 : |chi A n - chi B n| ≤ 1/2 := hN n hge
      have h2 : |chi A n - chi B n| = 1 := (abs_chi_sub_chi_eq_one_iff).mpr hn
      -- derive contradiction: from h1 and h2 we get 1 ≤ 1/2
      exfalso
      have hle : (1 : ℝ) ≤ (1/2 : ℝ) := by simpa [h2] using h1
      -- but 1/2 < 1, so not (1 ≤ 1/2)
      exact (one_half_lt_one.not_le) hle
    · -- ¬n ≥ N means n < N
      exact Nat.lt_of_not_ge hge
  -- finiteness: {n | n < N} is finite
  exact (Set.finite_lt_nat N).subset this

theorem iotaBar_injective : Function.Injective iotaBar := by
  classical
  intro x y hxy
  -- Use induction and explicitly manage the assumption transformation
  refine Quot.induction_on₂ x y (fun A B hAB => ?_) hxy
  -- hAB: iotaBar (Quot.mk _ A) = iotaBar (Quot.mk _ B)
  -- Goal: Quot.mk _ A = Quot.mk _ B
  -- Transport equality through the simp lemma for iotaBar on representatives  
  have hmk : Quot.mk instSetoidSeq.r (ι A) = Quot.mk instSetoidSeq.r (ι B) := by
    show Quot.mk instSetoidSeq.r (ι A) = Quot.mk instSetoidSeq.r (ι B)
    rw [← iotaBar_mk, ← iotaBar_mk]
    exact hAB
  
  -- Collapse EqvGen back to the setoid relation using Mathlib's canonical lemma
  have h1 : EqModC0Spec (ι A) (ι B) :=
    (instSetoidSeq.iseqv.eqvGen_iff).1 ((Quot.eq).1 hmk)
  -- 'chi' agrees pointwise with ι
  have hAchi : (fun n => chi A n) = ι A := by
    funext n; simp [ι, χ, chi]
  have hBchi : (fun n => chi B n) = ι B := by
    funext n; simp [ι, χ, chi]

  have h2 : EqModC0Spec (fun n => chi A n) (fun n => chi B n) := by
    simpa [hAchi, hBchi] using h1

  -- turn EqModC0Spec into the c₀ condition for the difference
  have hc0 : c0Spec (fun n => chi A n - chi B n) := by
    simpa [EqModC0Spec] using h2
  have hfin : (symmDiff A B).Finite := finite_of_c0_indicator_diff hc0
  -- back to equality in the Boolean quotient
  exact Quot.sound (by simpa [FinSymmDiffRel] using hfin)

end Papers.P2.Gap.BooleanSubLattice

/-! ## Standard lattice instances for SeqModC0 -/

namespace Papers.P2.Gap

open Papers.P2.Gap.BooleanSubLattice

-- TODO: Fix type class instance syntax issues  
-- noncomputable instance : Sup SeqModC0 := ⟨qSup⟩
-- noncomputable instance : Inf SeqModC0 := ⟨qInf⟩
-- noncomputable instance : HasCompl SeqModC0 := ⟨qCompl⟩

-- lemma sup_mk_seq (f g : ℕ → ℝ) :
--   (Quot.mk (@instSetoidSeq.r) f ⊔ Quot.mk (@instSetoidSeq.r) g)
--   = Quot.mk (@instSetoidSeq.r) (fun n => max (f n) (g n)) := rfl

-- lemma inf_mk_seq (f g : ℕ → ℝ) :
--   (Quot.mk (@instSetoidSeq.r) f ⊓ Quot.mk (@instSetoidSeq.r) g)  
--   = Quot.mk (@instSetoidSeq.r) (fun n => min (f n) (g n)) := rfl

-- lemma compl_mk_seq (f : ℕ → ℝ) :
--   (Quot.mk (@instSetoidSeq.r) f)ᶜ
--   = Quot.mk (@instSetoidSeq.r) (fun n => 1 - f n) := rfl

end Papers.P2.Gap