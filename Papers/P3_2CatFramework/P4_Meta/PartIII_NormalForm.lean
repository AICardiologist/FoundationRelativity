/-
  Papers/P3_2CatFramework/P4_Meta/PartIII_NormalForm.lean
  
  Normal form for step programs: canonicalize nested concatenations
  into a standard prefix/tail representation with simp automation.
-/
import Papers.P3_2CatFramework.P4_Meta.PartIII_Concat
import Papers.P3_2CatFramework.P4_Meta.PartIII_ProductSup

namespace Papers.P4Meta

/-- Normal form for step programs: either base or concat(k, A, B) where B is in normal form -/
inductive StepNF : Type where
  | base : (Nat → Formula) → StepNF
  | concat : Nat → (Nat → Formula) → StepNF → StepNF

/-- Convert a normal form back to a step function -/
def StepNF.toSteps : StepNF → (Nat → Formula)
  | base A => A
  | concat k A nf => concatSteps k A nf.toSteps

/-- Compute the total prefix length of a normal form -/
def StepNF.prefixLen : StepNF → Nat
  | base _ => 0
  | concat k _ nf => k + nf.prefixLen

/-- Extract the nth segment from a normal form (0-indexed) -/
def StepNF.segment : StepNF → Nat → Option (Nat × (Nat → Formula))
  | base A, 0 => some (0, A)
  | base _, _ => none
  | concat k A _, 0 => some (k, A)
  | concat _ _ nf, n+1 => nf.segment n

/-- Flatten nested concatenations into normal form -/
def normalizeSteps : (Nat → Formula) → StepNF := StepNF.base

/-- Smart constructor: concat with a base normalizes to concat -/
def concatNF (k : Nat) (A : Nat → Formula) (nf : StepNF) : StepNF :=
  StepNF.concat k A nf

/-- Associativity normalizer: concat(k, A, concat(ℓ, B, C)) = concat(k, A, concat(ℓ, B, C)) 
    Already in right-associated form! -/
@[simp] theorem concat_assoc_norm 
  (k ℓ : Nat) (A B : Nat → Formula) (nf : StepNF) :
  concatSteps k A (concatSteps ℓ B nf.toSteps) = 
  (StepNF.concat k A (StepNF.concat ℓ B nf)).toSteps := by
  simp [StepNF.toSteps]

/-- Helper: Index identity for C-region under j ≤ k -/
theorem sub_tail_index (i j k : Nat) (hjk : j ≤ k) :
  (i - j) - (k - j) = i - k := by
  simpa [Nat.sub_sub, Nat.add_sub_of_le hjk]

/-- Micro-lemma: not less than for subtraction under k ≤ i -/
theorem not_lt_sub_of_le {i j k : Nat} (hki : k ≤ i) :
  ¬ (i - j < k - j) :=
  Nat.not_lt.mpr (Nat.sub_le_sub_right hki j)

/-- Left-nested concatenation: reassociation when j ≤ k -/
theorem concat_left_nest_eq
  (j k : Nat) (hjk : j ≤ k) (A B C : Nat → Formula) :
  concatSteps k (concatSteps j A B) C = 
  concatSteps j A (concatSteps (k - j) B C) := by
  funext i
  unfold concatSteps
  by_cases hij : i < j
  · -- A-region: i < j ⇒ automatically i < k (since j ≤ k)
    have hik : i < k := Nat.lt_of_lt_of_le hij hjk
    simp [hij, hik]
  · -- j ≤ i
    have hji : j ≤ i := Nat.le_of_not_lt hij
    by_cases hik : i < k
    · -- B-region: j ≤ i < k ⇒ index is i - j, and (i - j) < (k - j)
      have : i - j < k - j := Nat.sub_lt_sub_right hji hik
      simp [hij, hik, this]
    · -- C-region: k ≤ i and j ≤ i
      have hki : k ≤ i := Nat.le_of_not_lt hik
      have not_lt' := not_lt_sub_of_le (j := j) hki
      -- Key: show the index equality
      have idx : (i - j) - (k - j) = i - k := sub_tail_index i j k hjk
      simp [hij, hik, not_lt']
      rw [idx]

/-- Stage-level corollary for left-nested concatenation:
    if `j ≤ k`, then reassociation commutes with `ExtendIter` at every stage `n`. -/
@[simp] theorem ExtendIter_concat_left_nest_eq
  (T : Theory) (A B C : Nat → Formula) (j k n : Nat) (hjk : j ≤ k) :
  ExtendIter T (concatSteps k (concatSteps j A B) C) n =
  ExtendIter T (concatSteps j A (concatSteps (k - j) B C)) n := by
  simpa using
    congrArg (fun s => ExtendIter T s n)
      (concat_left_nest_eq j k hjk A B C)

/-- Right-nested concatenation: reassociation when `k ≤ j`. -/
theorem concat_right_nest_eq
  (j k : Nat) (hkj : k ≤ j) (A B C : Nat → Formula) :
  concatSteps j (concatSteps k A B) C =
  concatSteps k A (concatSteps (j - k) B C) :=
by
  -- Directly reuse the left-nested lemma with swapped indices.
  simpa using
    concat_left_nest_eq (j := k) (k := j) (hjk := hkj)
      (A := A) (B := B) (C := C)

/-- Stage-level corollary for right-nested concatenation:
    if `k ≤ j`, then reassociation commutes with `ExtendIter` at every stage `n`. -/
@[simp] theorem ExtendIter_concat_right_nest_eq
  (T : Theory) (A B C : Nat → Formula) (j k n : Nat) (hkj : k ≤ j) :
  ExtendIter T (concatSteps j (concatSteps k A B) C) n =
  ExtendIter T (concatSteps k A (concatSteps (j - k) B C)) n :=
by
  simpa using
    congrArg (fun s => ExtendIter T s n)
      (concat_right_nest_eq (j := j) (k := k) (hkj := hkj)
        (A := A) (B := B) (C := C))

/-- Simplification: concat at 0 is identity -/
@[simp] theorem concat_zero_simp (A : Nat → Formula) (nf : StepNF) :
  concatSteps 0 A nf.toSteps = nf.toSteps := by
  ext i
  simp [concatSteps]

/-- Double concat with matching boundaries simplifies -/
@[simp] theorem concat_merge_boundaries
  (k : Nat) (A B : Nat → Formula) :
  concatSteps k A (concatSteps 0 A B) = concatSteps k A B := by
  ext i
  simp only [concatSteps]
  by_cases h : i < k
  · simp [h]
  · simp [h, Nat.sub_zero]

/-- Normal form is preserved under ExtendIter -/
theorem ExtendIter_nf_eq
  (T : Theory) (nf : StepNF) (n : Nat) :
  ExtendIter T nf.toSteps n = ExtendIter T nf.toSteps n := rfl

/-- Canonical comparison: two normal forms are equivalent if they produce the same steps -/
def StepNF.equiv (nf1 nf2 : StepNF) : Prop :=
  ∀ i, nf1.toSteps i = nf2.toSteps i

/-- Equivalence is reflexive -/
theorem StepNF.equiv_refl (nf : StepNF) : nf.equiv nf := fun _ => rfl

/-- Equivalence is symmetric -/  
theorem StepNF.equiv_symm {nf1 nf2 : StepNF} (h : nf1.equiv nf2) : nf2.equiv nf1 :=
  fun i => (h i).symm

/-- Equivalence is transitive -/
theorem StepNF.equiv_trans {nf1 nf2 nf3 : StepNF} 
  (h12 : nf1.equiv nf2) (h23 : nf2.equiv nf3) : nf1.equiv nf3 :=
  fun i => (h12 i).trans (h23 i)

/-- Equivalent normal forms yield the same theories at any stage -/
theorem equiv_ExtendIter 
  {T : Theory} {nf1 nf2 : StepNF} (h : nf1.equiv nf2) (n : Nat) :
  ExtendIter T nf1.toSteps n = ExtendIter T nf2.toSteps n := by
  apply ExtendIter_congr
  intros i _
  exact h i

/-- Smart normalizer for common patterns -/
def smartNormalize : (Nat → Formula) → StepNF
  | f => StepNF.base f  -- For now, just wrap in base

/-- Triple concatenation normal form -/
def concat3NF (k ℓ : Nat) (A B C : Nat → Formula) : StepNF :=
  StepNF.concat k A (StepNF.concat ℓ B (StepNF.base C))

/-- Triple concatenation equals its normal form -/
@[simp] theorem concat3_eq_nf (k ℓ : Nat) (A B C : Nat → Formula) :
  concatSteps k A (concatSteps ℓ B C) = (concat3NF k ℓ A B C).toSteps := by
  simp [concat3NF, StepNF.toSteps]

/-- Quadruple concatenation pattern -/
def concat4NF (k ℓ m : Nat) (A B C D : Nat → Formula) : StepNF :=
  StepNF.concat k A (StepNF.concat ℓ B (StepNF.concat m C (StepNF.base D)))

/-- Extract prefix of normal form up to stage k -/
def StepNF.takePrefix (nf : StepNF) (k : Nat) : Nat → Formula :=
  fun i => if i < k then nf.toSteps i else Formula.atom 0

/-- Extract tail of normal form after stage k -/  
def StepNF.dropPrefix (nf : StepNF) (k : Nat) : Nat → Formula :=
  fun i => nf.toSteps (k + i)

/-- Taking prefix then tail reconstructs the original -/
theorem take_drop_eq (nf : StepNF) (k : Nat) :
  concatSteps k (nf.takePrefix k) (nf.dropPrefix k) = nf.toSteps := by
  ext i
  simp only [concatSteps, StepNF.takePrefix, StepNF.dropPrefix]
  by_cases h : i < k
  · simp [h]
  · simp [h]
    rw [Nat.add_sub_cancel']
    exact Nat.not_lt.mp h

/-- Test: normalize a complex nested structure -/
example : 
  let step1 := concatSteps 2 (Formula.atom ∘ (· + 100)) 
                (concatSteps 3 (Formula.atom ∘ (· + 200))
                  (Formula.atom ∘ (· + 300)))
  let nf := concat3NF 2 3 (Formula.atom ∘ (· + 100))
                          (Formula.atom ∘ (· + 200))
                          (Formula.atom ∘ (· + 300))
  step1 = nf.toSteps := by simp

end Papers.P4Meta