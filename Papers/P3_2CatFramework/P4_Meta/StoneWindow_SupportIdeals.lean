/-
  File: Papers/P3_2CatFramework/P4_Meta/StoneWindow_SupportIdeals.lean
  
  Purpose: WP-D Stone Window for Support Ideals
  - Generalizes Stone window beyond Fin to arbitrary Boolean ideals
  - Parameterized by rings with only trivial idempotents
  - Algebraic proof without topology or choice
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic

namespace Papers.P4Meta
namespace StoneSupport

open Set

/-! ## D1. Boolean ideals on ℕ and the powerset quotient

This section defines:
* `BoolIdeal` — a Boolean ideal of subsets of ℕ
* the symmetric difference `△` and the equivalence relation modulo an ideal
* the quotient type `PowQuot 𝓘 := (𝒫(ℕ))/𝓘`
Everything here is elementary with no unfinished proofs. -/

/-- A Boolean ideal on subsets of ℕ. -/
structure BoolIdeal : Type where
  mem       : Set (Set ℕ)
  empty_mem : (∅ : Set ℕ) ∈ mem
  downward  : ∀ {A B : Set ℕ}, B ⊆ A → A ∈ mem → B ∈ mem
  union_mem : ∀ {A B : Set ℕ}, A ∈ mem → B ∈ mem → A ∪ B ∈ mem

/-- Symmetric difference of sets of naturals. -/
def sdiff (A B : Set ℕ) : Set ℕ := (A \ B) ∪ (B \ A)
infix:70 " △ " => sdiff

/-- Basic algebra of symmetric difference. -/
lemma sdiff_self (A : Set ℕ) : A △ A = (∅ : Set ℕ) := by
  ext n; by_cases hA : n ∈ A <;> simp [sdiff]

lemma sdiff_comm (A B : Set ℕ) : A △ B = B △ A := by
  -- case-split on membership in A and B; all cases are propositional tautologies
  ext n; by_cases hA : n ∈ A <;> by_cases hB : n ∈ B <;> simp [sdiff, hA, hB, and_comm, or_comm]

/-- Triangle-style inclusion: `(A △ C) ⊆ (A △ B) ∪ (B △ C)`. -/
lemma sdiff_subset_union (A B C : Set ℕ) :
    A △ C ⊆ (A △ B) ∪ (B △ C) := by
  intro n hn
  rcases hn with hAC | hCA
  · -- n ∈ A \ C
    rcases hAC with ⟨hA, hCnot⟩
    by_cases hB : n ∈ B
    · exact Or.inr (Or.inl ⟨hB, hCnot⟩)      -- n ∈ B \ C ⊆ (B △ C)
    · exact Or.inl (Or.inl ⟨hA, hB⟩)          -- n ∈ A \ B ⊆ (A △ B)
  · -- n ∈ C \ A
    rcases hCA with ⟨hC, hAnot⟩
    by_cases hB : n ∈ B
    · exact Or.inl (Or.inr ⟨hB, hAnot⟩)       -- n ∈ B \ A ⊆ (A △ B)
    · exact Or.inr (Or.inr ⟨hC, hB⟩)          -- n ∈ C \ B ⊆ (B △ C)

/-- The setoid: `A ~ B` iff `A △ B ∈ 𝓘`. -/
def sdiffSetoid (𝓘 : BoolIdeal) : Setoid (Set ℕ) where
  r     := fun A B => (A △ B) ∈ 𝓘.mem
  iseqv := by
    classical
    refine ⟨?refl, ?symm, ?trans⟩
    · intro A
      -- A △ A = ∅ and ∅ ∈ 𝓘
      rw [sdiff_self]
      exact 𝓘.empty_mem
    · intro A B h
      -- symmetry via commutativity of △
      rw [sdiff_comm]
      exact h
    · intro A B C hAB hBC
      -- transitivity via `(A △ C) ⊆ (A △ B) ∪ (B △ C)` and ideal closure
      have hsubset : A △ C ⊆ (A △ B) ∪ (B △ C) := sdiff_subset_union A B C
      have hUnion   : (A △ B) ∪ (B △ C) ∈ 𝓘.mem := 𝓘.union_mem hAB hBC
      exact 𝓘.downward hsubset hUnion

/-- Powerset quotient `𝒫(ℕ)/𝓘`. -/
abbrev PowQuot (𝓘 : BoolIdeal) := Quot (sdiffSetoid 𝓘)

/-! ### A concrete example: the ideal of finite sets -/

/-- The ideal of finite subsets of ℕ. -/
def FinIdeal : BoolIdeal where
  mem       := {A | A.Finite}
  empty_mem := Set.finite_empty
  downward  := by
    intro A B hBA hA
    exact hA.subset hBA
  union_mem := by
    intro A B hA hB
    exact hA.union hB

/-! ### Sanity: small lemmas showing the quotient behaves as expected -/
section Sanity
variable (𝓘 : BoolIdeal)

lemma quot_mk_eq_of_rel {A B : Set ℕ}
    (h : (A △ B) ∈ 𝓘.mem) :
    Quot.mk (sdiffSetoid 𝓘) A = Quot.mk (sdiffSetoid 𝓘) B :=
  Quot.sound h

example (A : Set ℕ) :
    Quot.mk (sdiffSetoid 𝓘) A = Quot.mk (sdiffSetoid 𝓘) A := rfl

end Sanity

/-! ## D2. ℓ∞ support ideal and function quotient (set-level, no algebra)

We work with plain functions `ℕ → R`:
* `Linf R` — our ℓ∞-like function space (no topology used)
* `supp x` — support of a function (indices where `x n ≠ 0`)
* `linfEqMod 𝓘` — equality modulo ideal 𝓘 via the **difference set** `{n | x n ≠ y n}`
* `LinfQuot 𝓘 R` — the quotient `(ℕ → R)/~` where `~` is `linfEqMod 𝓘`

No ring structure is assumed here. Algebraic quotients and idempotents are deferred to D3.
-/
open Classical
open Set

section D2

variable {R : Type*}

/-- ℓ∞-like function space: sequences over `R` indexed by naturals. -/
abbrev Linf (R : Type*) := ℕ → R

/-- Support of a function: indices where it is nonzero. Needs only `Zero R`. -/
def supp [Zero R] (x : Linf R) : Set ℕ := {n | x n ≠ 0}

/-- Functions whose support lies in a Boolean ideal `𝓘`. -/
def I_support (𝓘 : BoolIdeal) [Zero R] : Set (Linf R) :=
  {x | supp (R := R) x ∈ 𝓘.mem}

/-- Difference set between two functions: indices where they differ. -/
def diffSet [DecidableEq R] (x y : Linf R) : Set ℕ := {n | x n ≠ y n}

@[simp] lemma diffSet_self [DecidableEq R] (x : Linf R) :
    diffSet (R := R) x x = (∅ : Set ℕ) := by
  ext n; simp [diffSet]

@[simp] lemma diffSet_comm [DecidableEq R] (x y : Linf R) :
    diffSet (R := R) x y = diffSet (R := R) y x := by
  ext n; simp [diffSet, ne_comm]

/-- Triangle-style inclusion for difference sets:
    `diffSet x z ⊆ diffSet x y ∪ diffSet y z`. -/
lemma diffSet_subset_union [DecidableEq R] (x y z : Linf R) :
    diffSet (R := R) x z ⊆ diffSet (R := R) x y ∪ diffSet (R := R) y z := by
  intro n hn
  have hxz : x n ≠ z n := by simpa [diffSet] using hn
  by_cases hxy : x n = y n
  · -- then y n ≠ z n, otherwise x n = z n
    have : y n ≠ z n := by
      intro hyz; rw [hxy, hyz] at hxz; exact hxz rfl
    exact Or.inr (by simp [diffSet, this])
  · -- else x n ≠ y n
    exact Or.inl (by simp [diffSet, hxy])

/-- Setoid of equality modulo a Boolean ideal `𝓘`:
    `x ~ y` iff the set of indices where they differ lies in `𝓘`. -/
def linfEqMod (𝓘 : BoolIdeal) [DecidableEq R] : Setoid (Linf R) where
  r     := fun x y => diffSet (R := R) x y ∈ 𝓘.mem
  iseqv := by
    refine ⟨?refl, ?symm, ?trans⟩
    · intro x
      rw [diffSet_self]
      exact 𝓘.empty_mem
    · intro x y h
      rw [diffSet_comm]
      exact h
    · intro x y z hxy hyz
      have hsubset : diffSet (R := R) x z ⊆
          diffSet (R := R) x y ∪ diffSet (R := R) y z :=
        diffSet_subset_union (R := R) x y z
      have hUnion : diffSet (R := R) x y ∪ diffSet (R := R) y z ∈ 𝓘.mem :=
        𝓘.union_mem hxy hyz
      exact 𝓘.downward hsubset hUnion

/-- The quotient `(ℕ → R)/~` where `~` is equality mod `𝓘` via difference sets. -/
abbrev LinfQuot (𝓘 : BoolIdeal) (R : Type*) [DecidableEq R] :=
  Quot (linfEqMod (R := R) 𝓘)

/-- The zero function on `Linf R`. -/
@[simp] def linfZero [Zero R] : Linf R := fun _ => (0 : R)

/-- For zero, `diffSet x 0 = supp x`. -/
lemma diffSet_zero_eq_supp [Zero R] [DecidableEq R] (x : Linf R) :
    diffSet (R := R) x (linfZero (R := R)) = supp (R := R) x := by
  ext n; simp [diffSet, supp, linfZero]

/-- If `supp x ∈ 𝓘`, then `x` is equivalent to zero in the quotient. -/
lemma class_eq_zero_of_supp_mem
    (𝓘 : BoolIdeal) [Zero R] [DecidableEq R]
    {x : Linf R} (hx : supp (R := R) x ∈ 𝓘.mem) :
    Quot.mk (linfEqMod (R := R) 𝓘) x
      = Quot.mk (linfEqMod (R := R) 𝓘) (linfZero (R := R)) := by
  apply Quot.sound
  show diffSet x linfZero ∈ 𝓘.mem
  rw [diffSet_zero_eq_supp]
  exact hx

end D2

/-! ## D3(a). Support ideal as an ideal of the pointwise semiring `Linf R`

We show `I_support 𝓘` is an ideal of `Linf R := ℕ → R` under pointwise operations.
No topology or choice is used; we only need `[Semiring R]`.
-/

open Classical

section D3a

variable {R : Type*} [CommSemiring R]

/-- Support (reused from D2, restated to have local typeclass context). -/
@[reducible] def supp' (x : Linf R) : Set ℕ := {n | x n ≠ 0}

/-- Functions whose support lies in a Boolean ideal `𝓘`. -/
@[reducible] def I_support' (𝓘 : BoolIdeal) : Set (Linf R) := {x | supp' (R := R) x ∈ 𝓘.mem}

/-! ### Basic support lemmas under pointwise ring operations -/

/-- `supp 0 = ∅`. -/
@[simp] lemma supp'_zero : supp' (R := R) (0 : Linf R) = (∅ : Set ℕ) := by
  ext n; simp [supp']

/-- `supp (x + y) ⊆ supp x ∪ supp y`. -/
lemma supp'_add_subset (x y : Linf R) :
    supp' (R := R) (x + y) ⊆ supp' (R := R) x ∪ supp' (R := R) y := by
  intro n hn
  classical
  have hxy : x n + y n ≠ 0 := by simpa [supp'] using hn
  by_cases hx : x n = 0
  · by_cases hy : y n = 0
    · have : x n + y n = 0 := by simp [hx, hy]
      exact (hxy this).elim
    · exact Or.inr (by simp [supp', hy])
  · exact Or.inl (by simp [supp', hx])

/-- `supp (c * x) ⊆ supp x` (left multiplication). -/
lemma supp'_mul_left_subset (c x : Linf R) :
    supp' (R := R) (c * x) ⊆ supp' (R := R) x := by
  intro n hn
  simp [supp'] at hn ⊢
  contrapose! hn
  simp [hn]

/-- The support ideal as an ideal of `Linf R` under pointwise operations. -/
def ISupportIdeal (𝓘 : BoolIdeal) : Ideal (Linf R) where
  carrier  := I_support' (R := R) 𝓘
  zero_mem' := by
    -- `supp 0 = ∅ ∈ 𝓘`
    simp [I_support', supp'_zero, 𝓘.empty_mem]
  add_mem' := by
    intro x y hx hy
    -- downward closure + union closure
    have hsubset := supp'_add_subset (R := R) x y
    exact 𝓘.downward hsubset (𝓘.union_mem hx hy)
  smul_mem' := by
    intro c x hx
    -- `supp (c * x) ⊆ supp x`
    have hsubset := supp'_mul_left_subset (R := R) c x
    exact 𝓘.downward hsubset hx

/-- Unfolding lemma for membership in the support ideal. -/
@[simp] lemma mem_ISupportIdeal_iff (𝓘 : BoolIdeal) (x : Linf R) :
    x ∈ ISupportIdeal (R := R) 𝓘 ↔ supp' (R := R) x ∈ 𝓘.mem := Iff.rfl

end D3a

/-! ### Small inclusion lemmas -/

section SmallInclusions
open Classical
variable {R : Type*} [CommRing R] [DecidableEq R]

/-- If `x n - y n ≠ 0` then `x n ≠ y n`, pointwise; hence the support
    of `(x - y)` is contained in `diffSet x y`. -/
lemma supp'_sub_subset_diffSet (x y : Linf R) :
  supp' (R := R) (x - y) ⊆ diffSet (R := R) x y := by
  intro n hn
  have hxmy : x n - y n ≠ 0 := by simpa [supp'] using hn
  -- If x n = y n then x n − y n = 0, contradiction.
  have hxy : x n ≠ y n := by
    intro h
    have : x n - y n = 0 := by simp [h, sub_self]
    exact hxmy this
  simpa [diffSet] using hxy

end SmallInclusions

/-! ## D3(b). Characteristic functions and the set→function quotient lift

We define `chi : Set ℕ → Linf R` and show that equality modulo 𝓘 of sets
(respect to symmetric difference) implies equality modulo 𝓘 of characteristic
functions (with respect to the `diffSet` relation). This yields a well-defined
map `PowQuot 𝓘 → LinfQuot 𝓘 R`.

No ring structure is used in this section; only `[Zero R] [One R] [DecidableEq R]`.
-/

open Classical

section D3b

variable {R : Type*} [Zero R] [One R] [DecidableEq R]

/-- Characteristic function of a set (values in `{0,1}` over `R`). -/
noncomputable def chi (A : Set ℕ) : Linf R := fun n => if n ∈ A then (1 : R) else 0

section ChiLemmas
variable {R : Type*} [Zero R] [One R]

@[simp] lemma chi_of_mem  {A : Set ℕ} {n : ℕ} (h : n ∈ A) :
  chi (R := R) A n = 1 := by simp [chi, h]

@[simp] lemma chi_of_not_mem {A : Set ℕ} {n : ℕ} (h : n ∉ A) :
  chi (R := R) A n = 0 := by simp [chi, h]
end ChiLemmas

section mem_xor_of_chi_ne_scoped
variable {R : Type*} [Zero R] [One R]

/-- If the characteristic values differ at `n`, then membership in `A` and `B`
must differ at `n`. We prove this by cases on membership, without using `0 ≠ 1`. -/
lemma mem_xor_of_chi_ne {A B : Set ℕ} {n : ℕ}
    (hne : chi (R := R) A n ≠ chi (R := R) B n) :
    (n ∈ A ∧ n ∉ B) ∨ (n ∉ A ∧ n ∈ B) := by
  classical
  by_cases hA : n ∈ A
  · by_cases hB : n ∈ B
    · have : chi (R := R) A n = chi (R := R) B n := by
        simp [chi, hA, hB]
      exact (hne this).elim
    · exact Or.inl ⟨hA, hB⟩
  · by_cases hB : n ∈ B
    · exact Or.inr ⟨hA, hB⟩
    · have : chi (R := R) A n = chi (R := R) B n := by
        simp [chi, hA, hB]
      exact (hne this).elim

end mem_xor_of_chi_ne_scoped

/-- Difference set of `chi A` and `chi B` is contained in the symmetric difference `A △ B`. -/
lemma diffSet_chi_subset_sdiff (A B : Set ℕ) :
    diffSet (R := R) (chi (R := R) A) (chi (R := R) B) ⊆ (A △ B) := by
  intro n hn
  have hne : chi (R := R) A n ≠ chi (R := R) B n := by
    simpa [diffSet] using hn
  rcases mem_xor_of_chi_ne (R := R) (A := A) (B := B) hne with ⟨hA, hB⟩ | ⟨hA, hB⟩
  · exact Or.inl ⟨hA, hB⟩
  · exact Or.inr ⟨hB, hA⟩

/-- The set→function quotient lift:
`PowQuot 𝓘 = (𝒫(ℕ)/𝓘)` maps to `LinfQuot 𝓘 R = ((ℕ → R)/~)` by `[A] ↦ [χ_A]`. -/
noncomputable def PhiSetToLinfQuot (𝓘 : BoolIdeal) : PowQuot 𝓘 → LinfQuot 𝓘 R :=
  Quot.lift
    (fun A : Set ℕ => Quot.mk (linfEqMod (R := R) 𝓘) (chi (R := R) A))
    (by
      intro A B hAB
      -- Well-definedness: if `A △ B ∈ 𝓘`, then `diffSet (chi A) (chi B) ∈ 𝓘` by downward closure.
      apply Quot.sound
      exact 𝓘.downward (diffSet_chi_subset_sdiff (R := R) A B) hAB)

@[simp] lemma PhiSetToLinfQuot_mk (𝓘 : BoolIdeal) (A : Set ℕ) :
    PhiSetToLinfQuot (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) A)
  = Quot.mk (linfEqMod (R := R) 𝓘) (chi (R := R) A) := rfl

end D3b

/-! ## D3(c1). Idempotents modulo the ideal (pre-ring)

We explore functions that are idempotent modulo the ideal,
that is, `f^2 - f` has support in `𝓘`.

This is preparatory for building quotients that respect multiplication.
-/

section D3c1

variable {R : Type*} [CommRing R] [DecidableEq R] (𝓘 : BoolIdeal)

/-- A function `f : ℕ → R` is idempotent modulo `𝓘` if `f * f - f` has support in `𝓘`. -/
def IsIdemMod (f : Linf R) : Prop :=
  supp (R := R) (f * f - f) ∈ 𝓘.mem

/-- The subtype of functions that are idempotent modulo `𝓘`. -/
def IdemMod := {f : Linf R // IsIdemMod 𝓘 f}

/-- The quotient of `IdemMod` by the equivalence `linfEqMod`. -/
def IdemClass := Quot (fun (x y : IdemMod 𝓘) =>
  linfEqMod (R := R) 𝓘 x.val y.val)

/-! ### Characteristic functions are idempotent modulo any ideal -/

section chi_IsIdemMod_scoped
variable {R : Type*} [CommRing R] (𝓘 : BoolIdeal)

/-- For any set `A`, `chi A` is idempotent modulo any ideal.
    This is because `chi A * chi A = chi A` pointwise. -/
lemma chi_IsIdemMod (A : Set ℕ) : IsIdemMod 𝓘 (chi (R := R) A) := by
  unfold IsIdemMod
  have : chi (R := R) A * chi (R := R) A = chi (R := R) A := by
    ext n
    simp only [chi, Pi.mul_apply]
    by_cases h : n ∈ A
    · simp [h]
    · simp [h]
  rw [this]
  simp [supp]
  exact 𝓘.empty_mem

end chi_IsIdemMod_scoped

/-- Lift from `PowQuot` to `IdemClass` via characteristic functions. -/
noncomputable def PhiIdemMod : PowQuot 𝓘 → IdemClass (R := R) 𝓘 :=
  fun q => q.lift
    (fun A => Quot.mk _ ⟨chi (R := R) A, chi_IsIdemMod 𝓘 A⟩)
    (fun A B h => by
      apply Quot.sound
      show linfEqMod (R := R) 𝓘 (chi A) (chi B)
      exact 𝓘.downward (diffSet_chi_subset_sdiff A B) h)

/-! 
This gives us:
- A notion of idempotency modulo the ideal
- The fact that characteristic functions are always idempotent
- A canonical map from set quotients to idempotent quotients

The next step would be to show that `IdemClass` has a natural ring structure
when `R` is a Boolean ring or has special properties.
-/

end D3c1

/-! ### D3(c1) Polish: Setoid structure and compatibility -/

-- TODO: Fix universe level issues in this section
-- The D3c1_Setoid section is commented out due to universe level issues
-- It provides an alternative setoid-based presentation but is not needed
-- for the main implementation

/-
-- section D3c1_Setoid
-- def idemSetoid (𝓘 : BoolIdeal) : Setoid (IdemMod (R := R) 𝓘) where
  r u v := diffSet (R := R) u.1 v.1 ∈ 𝓘.mem
  iseqv := by
    refine ⟨?refl, ?symm, ?trans⟩
    · intro u
      -- diffSet u u = ∅, and ∅ ∈ 𝓘
      rw [diffSet_self]
      exact 𝓘.empty_mem
    · intro u v h
      -- symmetry by diffSet_comm
      rw [diffSet_comm]
      exact h
    · intro u v w huv hvw
      -- transitivity via inclusion and ideal closure
      have hsubset :
          diffSet (R := R) u.1 w.1
            ⊆ diffSet (R := R) u.1 v.1 ∪ diffSet (R := R) v.1 w.1 :=
        diffSet_subset_union u.1 v.1 w.1
      have hUnion :
          diffSet (R := R) u.1 v.1 ∪ diffSet (R := R) v.1 w.1 ∈ 𝓘.mem :=
        𝓘.union_mem huv hvw
      exact 𝓘.downward hsubset hUnion

/-- Canonical quotient of idempotent representatives. -/
abbrev IdemClass' (𝓘 : BoolIdeal) : Type* :=
  Quotient (idemSetoid (R := R) 𝓘)

/-- The forgetful map `IdemClass' → LinfQuot` induced by `Subtype.val`. -/
noncomputable def toLinfQuot (𝓘 : BoolIdeal) :
    IdemClass' 𝓘 → LinfQuot (R := R) 𝓘 :=
  Quotient.map (fun u : IdemMod (R := R) 𝓘 => u.1)
    (by
      intro u v huv
      -- Respect of relations: just reuse the restricted definition
      exact huv)

/-- Compatibility: forgetting idempotent structure agrees with the D3(b) lift. -/
noncomputable def PhiIdemMod' (𝓘 : BoolIdeal) :
    PowQuot 𝓘 → IdemClass' 𝓘 :=
  Quot.lift
    (fun A : Set ℕ => Quotient.mk (idemSetoid (R := R) 𝓘)
      ⟨chi (R := R) A, by
        -- your `chi_IsIdemMod` proof
        have : chi (R := R) A * chi (R := R) A = chi (R := R) A := by
          ext n; by_cases h : n ∈ A; simp [chi, h]; simp [chi, h]
        -- hence support of (χ^2 - χ) is empty
        unfold IsIdemMod
        rw [this]
        simp [supp]
        exact 𝓘.empty_mem⟩)
    (by
      intro A B hAB
      -- well-defined: same argument as D3(b)
      apply Quotient.sound
      exact 𝓘.downward (diffSet_chi_subset_sdiff (R := R) A B) hAB
    )

lemma Phi_commutes (𝓘 : BoolIdeal) :
    (toLinfQuot 𝓘) ∘ (PhiIdemMod' 𝓘)
  = PhiSetToLinfQuot (R := R) 𝓘 := rfl

-- end D3c1_Setoid
-/

/-! ## D3(c2). Algebraic Stone map scaffold -/

section D3c2
open Classical
variable {R : Type*} [CommRing R] [DecidableEq R]

/-- The ring quotient `(ℕ → R) ⧸ ISupportIdeal 𝓘`. -/
abbrev LinfQuotRing (𝓘 : BoolIdeal) (R : Type*) [CommRing R] [DecidableEq R] : Type _ :=
  (Linf R) ⧸ (ISupportIdeal (R := R) 𝓘)

/-- The algebraic Stone map `[A] ↦ class of χ_A` into the ring quotient. -/
noncomputable def PhiStone (𝓘 : BoolIdeal) :
    PowQuot 𝓘 → LinfQuotRing 𝓘 R :=
  Quot.lift
    (fun A : Set ℕ => Ideal.Quotient.mk (ISupportIdeal (R := R) 𝓘) (chi (R := R) A))
    (by
      intro A B hAB
      -- We must show (χ_A - χ_B) ∈ ISupportIdeal 𝓘.
      -- This is equivalent to showing that the two quotient elements are equal
      apply Ideal.Quotient.eq.mpr
      -- Need to show: chi A - chi B ∈ ISupportIdeal 𝓘
      rw [mem_ISupportIdeal_iff]
      -- Need to show: supp' (chi A - chi B) ∈ 𝓘.mem
      have h₁ : supp' (R := R) (chi (R := R) A - chi (R := R) B)
                ⊆ diffSet (R := R) (chi (R := R) A) (chi (R := R) B) :=
        supp'_sub_subset_diffSet (chi (R := R) A) (chi (R := R) B)
      have h₂ :
        diffSet (R := R) (chi (R := R) A) (chi (R := R) B)
          ⊆ (A △ B) := diffSet_chi_subset_sdiff (R := R) A B
      -- `supp' (...) ⊆ A △ B`, so if `A △ B ∈ 𝓘` then `supp' (...) ∈ 𝓘`.
      have : supp' (R := R) (chi (R := R) A - chi (R := R) B) ⊆ (A △ B) :=
        Set.Subset.trans h₁ h₂
      exact 𝓘.downward this hAB
    )

end D3c2

/-! ## D3(c3). Pack the algebraic Stone map into the idempotent subset -/

section D3c3
open Classical
variable {R : Type*} [CommRing R] [DecidableEq R]

/-- Idempotents of the ring quotient `(ℕ → R) ⧸ ISupportIdeal 𝓘`. -/
abbrev LinfQuotRingIdem (𝓘 : BoolIdeal) (R : Type*) [CommRing R] [DecidableEq R] : Type _ :=
  {e : LinfQuotRing 𝓘 R // e * e = e}

-- Removed Coe instance to avoid universe constraint issues
-- We use .1 explicitly where needed

section chi_idem_in_quot_scoped
variable {R : Type*} [CommRing R] (𝓘 : BoolIdeal)

/-- The class of `χ_A` is idempotent in the ring quotient. -/
lemma chi_idem_in_quot (A : Set ℕ) :
    (Ideal.Quotient.mk (ISupportIdeal (R := R) 𝓘) (chi (R := R) A) :
      LinfQuotRing 𝓘 R)
  *
    Ideal.Quotient.mk (ISupportIdeal (R := R) 𝓘) (chi (R := R) A)
  =
    Ideal.Quotient.mk (ISupportIdeal (R := R) 𝓘) (chi (R := R) A) := by
  -- Equality in the quotient via membership of the difference in the ideal
  refine (Ideal.Quotient.eq (I := ISupportIdeal (R := R) 𝓘)).mpr ?_
  -- Show `(χ_A * χ_A) - χ_A ∈ ISupportIdeal 𝓘`
  -- It suffices to show the support lies in 𝓘.mem
  have hχ : chi (R := R) A * chi (R := R) A = chi (R := R) A := by
    ext n
    by_cases h : n ∈ A
    · simp [chi, h]
    · simp [chi, h]
  -- Using D3(a) unfolding lemma for ISupportIdeal
  -- support of zero is ∅ ∈ 𝓘
  rw [mem_ISupportIdeal_iff]
  -- rewrite to zero, then use empty_mem
  simp [supp', hχ]
  exact 𝓘.empty_mem

end chi_idem_in_quot_scoped

/-- Stone map into the idempotent subset of the ring quotient. -/
noncomputable def PhiStoneIdem (𝓘 : BoolIdeal) :
    PowQuot 𝓘 → LinfQuotRingIdem 𝓘 R :=
  Quot.lift
    (fun A : Set ℕ =>
      ⟨ Ideal.Quotient.mk (ISupportIdeal (R := R) 𝓘) (chi (R := R) A),
        chi_idem_in_quot 𝓘 A ⟩)
    (by
      intro A B hAB
      -- Under the hood this is the same well-definedness as `PhiStone`
      -- (χ_A - χ_B) ∈ ISupportIdeal 𝓘 ⇒ equal classes in the quotient
      -- so the `Subtype` witnesses agree as elements of the quotient.
      apply Subtype.ext -- equality of Subtype by value equality
      -- Value equality in the quotient ring:
      apply Ideal.Quotient.eq.mpr
      -- As in D3(c2):
      have h₁ : supp' (R := R) (chi (R := R) A - chi (R := R) B)
                ⊆ diffSet (R := R) (chi (R := R) A) (chi (R := R) B) :=
        supp'_sub_subset_diffSet (chi (R := R) A) (chi (R := R) B)
      have h₂ : diffSet (R := R) (chi (R := R) A) (chi (R := R) B) ⊆ (A △ B) :=
        diffSet_chi_subset_sdiff A B
      have hsub : supp' (R := R) (chi (R := R) A - chi (R := R) B) ⊆ (A △ B) :=
        Set.Subset.trans h₁ h₂
      -- Downward closure to 𝓘.mem:
      --   (A △ B) ∈ 𝓘 from `hAB`
      -- ⇒ support ∈ 𝓘
      rw [mem_ISupportIdeal_iff]
      exact 𝓘.downward hsub hAB
    )

-- The following lemma shows the relationship between PhiStoneIdem and PhiStone
-- Note: This is definitionally equal - both use Quot.lift with chi
-- lemma PhiStoneIdem_val {R : Type*} [CommRing R] [DecidableEq R] (𝓘 : BoolIdeal) (q : PowQuot 𝓘) :
--     (PhiStoneIdem (R := R) 𝓘 q).1 = PhiStone (R := R) 𝓘 q := rfl

end D3c3

/-! ## Support lemmas (moved from D3c4 for better accessibility) -/

section SupportLemmas
variable {R : Type*} [CommRing R] [DecidableEq R]

/-- Support of negation is the same as the support. -/
lemma supp'_neg (f : Linf R) : supp' (R := R) (-f) = supp' (R := R) f := by
  ext n; by_cases h : f n = 0 <;> simp [supp', h]

end SupportLemmas

/-! ## D3(c4). Two idempotents hypothesis and equivalence scaffold -/

section D3c4
open Classical
variable {R : Type*}

/-- Rings with only two idempotents, 0 and 1. -/
class TwoIdempotents (R : Type*) [Semiring R] : Prop where
  resolve : ∀ x : R, x * x = x → x = 0 ∨ x = 1

section
variable [CommRing R] [DecidableEq R] (𝓘 : BoolIdeal) [TwoIdempotents R]

/-- Extract the subset A from an idempotent representative.
    For each n, since f(n)^2 = f(n), `TwoIdempotents.resolve` tells us f(n) ∈ {0,1}. 
    We define A_of(f) = { n | f(n) = 1 }. -/
noncomputable def A_of (f : Linf R) : Set ℕ := { n | f n = 1 }

/-- If `f n` is idempotent, then the characteristic function of `A_of f` agrees with `f` at `n`. -/
lemma chi_matches_of_idem_point (f : Linf R) {n : ℕ}
    (hidem : f n * f n = f n) :
    chi (R := R) (A_of f) n = f n := by
  classical
  rcases TwoIdempotents.resolve (R := R) (f n) hidem with h0 | h1
  · -- case `f n = 0`
    unfold chi A_of
    simp only [Set.mem_setOf]
    by_cases hf1 : f n = 1
    · -- both 0 and 1 (trivial ring case)
      have : (1 : R) = 0 := hf1.symm.trans h0
      rw [if_pos hf1, hf1]
    · -- `f n ≠ 1`
      rw [if_neg hf1, h0]
  · -- case `f n = 1`
    unfold chi A_of
    simp only [Set.mem_setOf]
    rw [if_pos h1, h1]

/-- "Pointwise equal off small": the support of `χ_{A_of f} − f` is contained in the
    support of the idempotency defect `f*f − f`. -/
lemma supp_chi_sub_subset_supp_idem (f : Linf R) :
    supp' (R := R) (chi (R := R) (A_of f) - f)
      ⊆ supp' (R := R) (f * f - f) := by
  classical
  intro n hn
  -- contraposition on "not in RHS support"
  by_contra hnot
  have hz : f n * f n - f n = 0 := by simpa [supp'] using hnot
  have hidem : f n * f n = f n := sub_eq_zero.mp hz
  have hχ : chi (R := R) (A_of f) n = f n :=
    chi_matches_of_idem_point (R := R) f hidem
  have : chi (R := R) (A_of f) n - f n = 0 := by simp [hχ, sub_self]
  simp only [supp'] at hn
  exact hn this

section sdiff_A_of_subset_supp_sub_scoped
variable {R : Type*} [CommRing R]

/-- The symmetric difference of the extracted sets is supported where the representatives differ. -/
lemma sdiff_A_of_subset_supp_sub (f g : Linf R) :
    A_of (R := R) f △ A_of (R := R) g ⊆ supp' (R := R) (f - g) := by
  classical
  intro n hn
  rcases hn with ⟨hf, hgn1⟩ | ⟨hg, hfn1⟩
  · -- `f n = 1`, `g n ≠ 1`  ⇒  `f n ≠ g n` ⇒  `(f n - g n) ≠ 0`
    have hneq : f n ≠ g n := fun h => hgn1 (h ▸ hf : g n = 1)
    simp only [supp', Set.mem_setOf]
    exact fun h => hneq (sub_eq_zero.mp h)
  · -- `g n = 1`, `f n ≠ 1`
    have hneq : f n ≠ g n := fun h => hfn1 (h.symm ▸ hg : f n = 1)
    simp only [supp', Set.mem_setOf]
    exact fun h => hneq (sub_eq_zero.mp h)

end sdiff_A_of_subset_supp_sub_scoped

/-- A canonical (noncomputable) representative of a quotient element. -/
noncomputable def rep (q : LinfQuotRing 𝓘 R) : Linf R :=
  Classical.choose (Quot.exists_rep q)

set_option linter.unusedSectionVars false in
@[simp] lemma mk_rep (q : LinfQuotRing 𝓘 R) :
    Ideal.Quotient.mk (ISupportIdeal (R := R) 𝓘) (rep (𝓘 := 𝓘) (R := R) q) = q :=
  Classical.choose_spec (Quot.exists_rep q)

/-- The inverse-candidate: from an idempotent element of the ring-quotient to a class of sets. -/
noncomputable def PsiStoneIdem : LinfQuotRingIdem 𝓘 R → PowQuot 𝓘 :=
  fun e =>
    -- pick a representative of the underlying quotient class
    let f := rep (𝓘 := 𝓘) (R := R) e.1
    -- return the extracted set modulo 𝓘
    Quot.mk (sdiffSetoid 𝓘) (A_of (R := R) f)

/-- Pair of maps (no inverse laws yet). This avoids sorries until inverse laws are proven. -/
structure StoneMaps (𝓘 : BoolIdeal) (R : Type*) [CommRing R] [DecidableEq R] where
  toIdempotents   : PowQuot 𝓘 → LinfQuotRingIdem 𝓘 R
  fromIdempotents : LinfQuotRingIdem 𝓘 R → PowQuot 𝓘

noncomputable def stoneMaps : StoneMaps 𝓘 R where
  toIdempotents   := PhiStoneIdem 𝓘
  fromIdempotents := PsiStoneIdem 𝓘

/-! ### Stone Equivalence (requires Nontrivial R)

In nontrivial rings, we can identify sets with their characteristic functions,
which enables us to prove that PhiStoneIdem and PsiStoneIdem are inverses.
-/

section StoneEquivalence
variable [Nontrivial R]

set_option linter.unusedSectionVars false in
/-- In a nontrivial ring, A_of(χ_A) = A. -/
@[simp] lemma A_of_chi_eq (A : Set ℕ) :
    A_of (R := R) (chi (R := R) A) = A := by
  classical
  ext n
  simp only [A_of, Set.mem_setOf, chi]
  by_cases h : n ∈ A <;> simp [h, zero_ne_one']

/-- Left inverse: Ψ ∘ Φ = id on PowQuot 𝓘. -/
lemma Psi_after_Phi (q : PowQuot 𝓘) :
    PsiStoneIdem (R := R) 𝓘 (PhiStoneIdem (R := R) 𝓘 q) = q := by
  classical
  refine Quot.induction_on q ?_
  intro A
  -- Unfold the definitions
  change Quot.mk (sdiffSetoid 𝓘) (A_of (R := R) (rep (𝓘 := 𝓘) (R := R) (PhiStoneIdem (R := R) 𝓘 (Quot.mk _ A)).1)) = Quot.mk _ A
  -- Set up abbreviations
  set e := PhiStoneIdem (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) A)
  -- rep e.1 represents the same quotient class as e.1
  have hrepeq : Ideal.Quotient.mk (ISupportIdeal (R := R) 𝓘) (rep (𝓘 := 𝓘) (R := R) e.1) = e.1 :=
    mk_rep (𝓘 := 𝓘) (R := R) e.1
  -- e.1 is the quotient class of χ_A
  have he1 : e.1 = Ideal.Quotient.mk (ISupportIdeal (R := R) 𝓘) (chi (R := R) A) := by
    rfl
  -- Therefore rep e.1 - χ_A has small support
  have hdiff : Ideal.Quotient.mk (ISupportIdeal (R := R) 𝓘) (rep (𝓘 := 𝓘) (R := R) e.1 - chi (R := R) A) = 0 := by
    rw [RingHom.map_sub]
    rw [hrepeq, he1]
    simp
  -- Convert to support membership
  rw [Ideal.Quotient.eq_zero_iff_mem] at hdiff
  rw [mem_ISupportIdeal_iff] at hdiff
  -- The symmetric difference of A_of's is supported on the function difference
  have hsub : A_of (R := R) (rep (𝓘 := 𝓘) (R := R) e.1) △ A_of (R := R) (chi (R := R) A)
              ⊆ supp' (R := R) (rep (𝓘 := 𝓘) (R := R) e.1 - chi (R := R) A) :=
    sdiff_A_of_subset_supp_sub (R := R) _ _
  -- Apply downward closure
  have hsdiff_small : A_of (R := R) (rep (𝓘 := 𝓘) (R := R) e.1) △ A_of (R := R) (chi (R := R) A) ∈ 𝓘.mem :=
    𝓘.downward hsub hdiff
  -- Use A_of_chi_eq to simplify
  rw [A_of_chi_eq (R := R) A] at hsdiff_small
  -- Conclude equality in the quotient
  exact Quot.sound hsdiff_small

section Phi_after_Psi_scoped

/-- Right inverse: Φ ∘ Ψ = id on LinfQuotRingIdem 𝓘 R. -/
lemma Phi_after_Psi (e : LinfQuotRingIdem 𝓘 R) :
    PhiStoneIdem (R := R) 𝓘 (PsiStoneIdem (R := R) 𝓘 e) = e := by
  classical
  -- Bring in the instances that the proof needs but aren't in the statement
  have _ := (inferInstance : Nontrivial R)
  have _ := (inferInstance : TwoIdempotents R)
  -- We need to show equality of subtypes
  apply Subtype.ext
  -- Goal: mk(χ_{A_of f}) = e.1, where f = rep e.1
  set f := rep (𝓘 := 𝓘) (R := R) e.1
  -- rep e.1 represents the same quotient class
  have hrepeq : Ideal.Quotient.mk (ISupportIdeal (R := R) 𝓘) f = e.1 :=
    mk_rep (𝓘 := 𝓘) (R := R) e.1
  -- e is idempotent in the quotient, so f*f - f has small support
  have h_idem_quot : e.1 * e.1 = e.1 := e.2
  have h_idem_mod : Ideal.Quotient.mk (ISupportIdeal (R := R) 𝓘) (f * f - f) = 0 := by
    simp only [RingHom.map_sub, RingHom.map_mul, hrepeq, h_idem_quot, sub_self]
  rw [Ideal.Quotient.eq_zero_iff_mem, mem_ISupportIdeal_iff] at h_idem_mod
  -- χ_{A_of f} - f is supported on f*f - f
  have h_subset : supp' (R := R) (chi (R := R) (A_of (R := R) f) - f)
                  ⊆ supp' (R := R) (f * f - f) :=
    supp_chi_sub_subset_supp_idem (R := R) f
  -- Apply downward closure
  have h_small : supp' (R := R) (chi (R := R) (A_of (R := R) f) - f) ∈ 𝓘.mem :=
    𝓘.downward h_subset h_idem_mod
  -- Conclude equality in the quotient ring
  change Ideal.Quotient.mk (ISupportIdeal (R := R) 𝓘) (chi (R := R) (A_of (R := R) f)) = e.1
  rw [← hrepeq]
  apply Ideal.Quotient.eq.mpr
  rw [mem_ISupportIdeal_iff]
  exact h_small

end Phi_after_Psi_scoped

/-- The Stone equivalence between power set quotient and idempotents of the ring quotient. -/
noncomputable def StoneEquiv :
    PowQuot 𝓘 ≃ LinfQuotRingIdem 𝓘 R :=
{ toFun    := PhiStoneIdem (R := R) 𝓘,
  invFun   := PsiStoneIdem (R := R) 𝓘,
  left_inv := Psi_after_Phi (R := R) 𝓘,
  right_inv:= Phi_after_Psi (R := R) 𝓘 }

/-! ### Extensionality via Stone equivalence (nontrivial rings) -/

@[ext] lemma LinfQuotRingIdem.ext_of_psi_eq
  {e f : LinfQuotRingIdem 𝓘 R}
  (h : PsiStoneIdem (R := R) 𝓘 e = PsiStoneIdem (R := R) 𝓘 f) : e = f := by
  -- Apply Φ to both sides and use Φ ∘ Ψ = id
  simpa [Phi_after_Psi (R := R) 𝓘] using congrArg (PhiStoneIdem (R := R) 𝓘) h

end StoneEquivalence

end
end D3c4

/-! ## Boolean Algebra Bridge (chi operations) -/

section ChiBridge

section chi_operations_scoped
variable {R : Type*} [CommRing R]

/-- chi of intersection. -/
@[simp] lemma chi_inter (A B : Set ℕ) :
    chi (R := R) (A ∩ B) = chi (R := R) A * chi (R := R) B := by
  classical
  ext n
  simp only [chi, Set.mem_inter_iff]
  by_cases hA : n ∈ A <;> by_cases hB : n ∈ B <;> simp [hA, hB, mul_zero, zero_mul]

/-- chi of union. -/
@[simp] lemma chi_union (A B : Set ℕ) :
    chi (R := R) (A ∪ B) = chi (R := R) A + chi (R := R) B - chi (R := R) A * chi (R := R) B := by
  classical
  ext n
  simp only [chi, Set.mem_union]
  by_cases hA : n ∈ A <;> by_cases hB : n ∈ B <;> simp [hA, hB, add_zero, zero_add, mul_zero, zero_mul, sub_zero]

/-- chi of complement. -/
@[simp] lemma chi_compl (A : Set ℕ) :
    chi (R := R) Aᶜ = 1 - chi (R := R) A := by
  classical
  ext n
  simp only [chi, Set.mem_compl_iff]
  by_cases h : n ∈ A <;> simp [h, sub_zero]

/-- chi of symmetric difference. -/
@[simp] lemma chi_sdiff (A B : Set ℕ) :
    chi (R := R) (A △ B) = chi (R := R) A + chi (R := R) B - 2 * chi (R := R) A * chi (R := R) B := by
  classical
  ext n
  simp only [chi, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  -- Check if n is in the symmetric difference
  have hsym : n ∈ (A △ B) ↔ (n ∈ A ∧ n ∉ B) ∨ (n ∈ B ∧ n ∉ A) := by rfl
  simp only [hsym]
  by_cases hA : n ∈ A <;> by_cases hB : n ∈ B
  all_goals simp only [hA, hB, if_true, if_false, not_false, not_true, and_true, true_and,
                       and_false, false_and, or_false, false_or]
  all_goals norm_num

end chi_operations_scoped

variable {R : Type*} [CommRing R] [DecidableEq R]

set_option linter.unusedSectionVars false in
@[simp] lemma chi_empty : chi (R := R) (∅ : Set ℕ) = 0 := by
  classical
  ext n; simp [chi]

@[simp] lemma chi_univ {R} [CommRing R] [DecidableEq R] : chi (R := R) (Set.univ : Set ℕ) = 1 := by
  classical
  ext n; simp [chi]

@[simp] lemma supp'_chi {R} [CommRing R] [DecidableEq R] [Nontrivial R]
    (A : Set ℕ) :
  supp' (R := R) (chi (R := R) A) = A := by
  classical
  ext n
  by_cases h : n ∈ A
  · simp [supp', chi, h, one_ne_zero]
  · simp [supp', chi, h]

@[simp] lemma supp'_chi_sub {R} [CommRing R] [DecidableEq R] [Nontrivial R]
    (A B : Set ℕ) :
  supp' (R := R) (chi (R := R) A - chi (R := R) B) = A △ B := by
  classical
  ext n
  simp only [supp', chi, Pi.sub_apply]
  -- Unfold symmetric difference
  have hsym : n ∈ A △ B ↔ (n ∈ A ∧ n ∉ B) ∨ (n ∈ B ∧ n ∉ A) := by rfl
  simp only [hsym]
  by_cases hA : n ∈ A <;> by_cases hB : n ∈ B
  · -- Both in A and B: chi A n = 1, chi B n = 1, so diff = 0
    simp [hA, hB, sub_self]
  · -- In A but not B: chi A n = 1, chi B n = 0, so diff = 1 ≠ 0
    simp [hA, hB, zero_ne_one]
  · -- Not in A but in B: chi A n = 0, chi B n = 1, so diff = -1 ≠ 0
    simp [hA, hB, zero_sub, neg_ne_zero, zero_ne_one]
  · -- Neither in A nor B: chi A n = 0, chi B n = 0, so diff = 0
    simp [hA, hB, sub_self]

end ChiBridge

/-! ## Boolean Algebra on Idempotents -/

section BooleanAlgebraOnIdempotents
variable {R : Type*} [CommRing R] [DecidableEq R] (𝓘 : BoolIdeal)

/-- Infimum on idempotents via multiplication. -/
noncomputable def idemInf : LinfQuotRingIdem 𝓘 R → LinfQuotRingIdem 𝓘 R → LinfQuotRingIdem 𝓘 R :=
  fun e f => ⟨e.1 * f.1, by
    -- Need to show (e * f) * (e * f) = e * f when e^2 = e and f^2 = f
    calc (e.1 * f.1) * (e.1 * f.1) = e.1 * (f.1 * e.1) * f.1 := by ring
    _ = e.1 * (e.1 * f.1) * f.1 := by rw [mul_comm f.1 e.1]
    _ = (e.1 * e.1) * f.1 * f.1 := by ring
    _ = e.1 * f.1 * f.1 := by rw [e.2]
    _ = e.1 * (f.1 * f.1) := by ring
    _ = e.1 * f.1 := by rw [f.2]⟩

/-- Supremum on idempotents via x + y - xy. -/
noncomputable def idemSup : LinfQuotRingIdem 𝓘 R → LinfQuotRingIdem 𝓘 R → LinfQuotRingIdem 𝓘 R :=
  fun e f => ⟨e.1 + f.1 - e.1 * f.1, by
    -- Need to show (e + f - ef)^2 = e + f - ef when e^2 = e and f^2 = f
    have he : e.1 * e.1 = e.1 := e.2
    have hf : f.1 * f.1 = f.1 := f.2
    -- Expand and simplify using idempotency
    simp only [sub_mul, mul_sub, add_mul, mul_add]
    ring_nf
    -- Now replace all e^2 with e and f^2 with f
    simp only [sq, he, hf]
    ring⟩

/-- Complement on idempotents via 1 - x. -/
noncomputable def idemCompl : LinfQuotRingIdem 𝓘 R → LinfQuotRingIdem 𝓘 R :=
  fun e => ⟨1 - e.1, by
    -- Show (1 - e)^2 = 1 - e when e^2 = e
    have he := e.2
    ring_nf
    simp only [sq, he]
    ring⟩

@[simp] lemma idemInf_val (e f : LinfQuotRingIdem 𝓘 R) :
  (idemInf 𝓘 e f).1 = e.1 * f.1 := rfl

@[simp] lemma idemSup_val (e f : LinfQuotRingIdem 𝓘 R) :
  (idemSup 𝓘 e f).1 = e.1 + f.1 - e.1 * f.1 := rfl

@[simp] lemma idemCompl_val (e : LinfQuotRingIdem 𝓘 R) :
  (idemCompl 𝓘 e).1 = 1 - e.1 := rfl

@[simp] lemma idemInf_comm (e f : LinfQuotRingIdem 𝓘 R) :
    idemInf 𝓘 e f = idemInf 𝓘 f e := by
  ext
  simp only [idemInf_val]
  ring

@[simp] lemma idemSup_comm (e f : LinfQuotRingIdem 𝓘 R) :
    idemSup 𝓘 e f = idemSup 𝓘 f e := by
  ext
  simp only [idemSup_val]
  ring

@[simp] lemma idemCompl_involutive (e : LinfQuotRingIdem 𝓘 R) :
    idemCompl 𝓘 (idemCompl 𝓘 e) = e := by
  ext
  simp only [idemCompl_val]
  ring

/-! ### Top/Bottom idempotents and basic laws -/

noncomputable def idemTop : LinfQuotRingIdem 𝓘 R := ⟨(1 : LinfQuotRing 𝓘 R), by simp⟩
noncomputable def idemBot : LinfQuotRingIdem 𝓘 R := ⟨(0 : LinfQuotRing 𝓘 R), by simp⟩

@[simp] lemma idemTop_val : (idemTop 𝓘 : LinfQuotRingIdem 𝓘 R).1 = (1 : LinfQuotRing 𝓘 R) := rfl
@[simp] lemma idemBot_val : (idemBot 𝓘 : LinfQuotRingIdem 𝓘 R).1 = (0 : LinfQuotRing 𝓘 R) := rfl

@[simp] lemma idemInf_bot_left  (e : LinfQuotRingIdem 𝓘 R) :
  idemInf 𝓘 (idemBot 𝓘) e = idemBot 𝓘 := by
  ext; simp [idemInf_val, idemBot_val]

@[simp] lemma idemInf_bot_right (e : LinfQuotRingIdem 𝓘 R) :
  idemInf 𝓘 e (idemBot 𝓘) = idemBot 𝓘 := by
  ext; simp [idemInf_val, idemBot_val]

@[simp] lemma idemInf_top_left  (e : LinfQuotRingIdem 𝓘 R) :
  idemInf 𝓘 (idemTop 𝓘) e = e := by
  ext; simp [idemInf_val, idemTop_val]

@[simp] lemma idemInf_top_right (e : LinfQuotRingIdem 𝓘 R) :
  idemInf 𝓘 e (idemTop 𝓘) = e := by
  ext; simp [idemInf_val, idemTop_val]

@[simp] lemma idemSup_top_left  (e : LinfQuotRingIdem 𝓘 R) :
  idemSup 𝓘 (idemTop 𝓘) e = idemTop 𝓘 := by
  ext
  have : (1 : LinfQuotRing 𝓘 R) + e.1 - (1 * e.1) = (1 : LinfQuotRing 𝓘 R) := by ring
  simp [idemSup_val, idemTop_val, this]

@[simp] lemma idemSup_top_right (e : LinfQuotRingIdem 𝓘 R) :
  idemSup 𝓘 e (idemTop 𝓘) = idemTop 𝓘 := by
  ext
  have : e.1 + (1 : LinfQuotRing 𝓘 R) - (e.1 * 1) = (1 : LinfQuotRing 𝓘 R) := by ring
  simp [idemSup_val, idemTop_val, this]

@[simp] lemma idemSup_bot_left  (e : LinfQuotRingIdem 𝓘 R) :
  idemSup 𝓘 (idemBot 𝓘) e = e := by
  ext; simp [idemSup_val, idemBot_val]

@[simp] lemma idemSup_bot_right (e : LinfQuotRingIdem 𝓘 R) :
  idemSup 𝓘 e (idemBot 𝓘) = e := by
  ext; simp [idemSup_val, idemBot_val]

/-! ### Absorption laws -/

@[simp] lemma idemInf_absorb_left (e f : LinfQuotRingIdem 𝓘 R) :
  idemInf 𝓘 e (idemSup 𝓘 e f) = e := by
  ext
  have he : e.1 * e.1 = e.1 := e.2
  calc
    e.1 * (e.1 + f.1 - e.1 * f.1)
        = e.1 * e.1 + e.1 * f.1 - e.1 * e.1 * f.1 := by ring
    _   = e.1 + e.1 * f.1 - e.1 * f.1 := by simp [he]
    _   = e.1 := by ring

@[simp] lemma idemSup_absorb_left (e f : LinfQuotRingIdem 𝓘 R) :
  idemSup 𝓘 e (idemInf 𝓘 e f) = e := by
  ext
  have he : e.1 * e.1 = e.1 := e.2
  calc
    e.1 + (e.1 * f.1) - e.1 * (e.1 * f.1)
        = e.1 + e.1 * f.1 - (e.1 * e.1) * f.1 := by ring
    _   = e.1 + e.1 * f.1 - e.1 * f.1 := by simp [he]
    _   = e.1 := by ring

@[simp] lemma idemInf_absorb_right (e f : LinfQuotRingIdem 𝓘 R) :
  idemInf 𝓘 (idemSup 𝓘 e f) e = e := by
  simp [idemInf_comm 𝓘, idemInf_absorb_left]

@[simp] lemma idemSup_absorb_right (e f : LinfQuotRingIdem 𝓘 R) :
  idemSup 𝓘 (idemInf 𝓘 e f) e = e := by
  simp [idemSup_comm 𝓘, idemSup_absorb_left]

/-! ### De Morgan laws -/

@[simp] lemma idemCompl_inf (e f : LinfQuotRingIdem 𝓘 R) :
  idemCompl 𝓘 (idemInf 𝓘 e f) =
    idemSup 𝓘 (idemCompl 𝓘 e) (idemCompl 𝓘 f) := by
  ext
  simp only [idemCompl_val, idemInf_val, idemSup_val]
  -- 1 - (e f) = (1 - e) + (1 - f) - (1 - e)(1 - f)
  ring

@[simp] lemma idemCompl_sup (e f : LinfQuotRingIdem 𝓘 R) :
  idemCompl 𝓘 (idemSup 𝓘 e f) =
    idemInf 𝓘 (idemCompl 𝓘 e) (idemCompl 𝓘 f) := by
  ext
  simp only [idemCompl_val, idemSup_val, idemInf_val]
  -- 1 - (e + f - e f) = (1 - e)(1 - f)
  ring

/-! ### Associativity and idempotency -/

@[simp] lemma idemInf_assoc (e f g : LinfQuotRingIdem 𝓘 R) :
  idemInf 𝓘 (idemInf 𝓘 e f) g = idemInf 𝓘 e (idemInf 𝓘 f g) := by
  ext
  simp only [idemInf_val]
  exact mul_assoc e.1 f.1 g.1

@[simp] lemma idemSup_assoc (e f g : LinfQuotRingIdem 𝓘 R) :
  idemSup 𝓘 (idemSup 𝓘 e f) g = idemSup 𝓘 e (idemSup 𝓘 f g) := by
  ext
  -- (x + y - xy) + z - (x + y - xy)z = x + (y + z - yz) - x(y + z - yz)
  simp [idemSup_val]
  ring

@[simp] lemma idemInf_idem (e : LinfQuotRingIdem 𝓘 R) :
  idemInf 𝓘 e e = e := by
  ext; simp [idemInf_val, e.2]

@[simp] lemma idemSup_idem (e : LinfQuotRingIdem 𝓘 R) :
  idemSup 𝓘 e e = e := by
  -- e ⊔ e = e + e - e^2 = (2e - e) = e
  ext
  simp only [idemSup_val, e.2]
  ring

-- Note: Distributivity laws would go here but are omitted for now
-- as they're not required for the current Stone equivalence proof

/-! ### Complements w.r.t. ⊤/⊥ -/

@[simp] lemma idemSup_compl (e : LinfQuotRingIdem 𝓘 R) :
  idemSup 𝓘 e (idemCompl 𝓘 e) = idemTop 𝓘 := by
  -- e + (1 - e) - e(1 - e) = 1 - (e - e^2) = 1
  ext
  simp only [idemSup_val, idemCompl_val, idemTop_val, mul_sub, e.2]
  ring

@[simp] lemma idemInf_compl (e : LinfQuotRingIdem 𝓘 R) :
  idemInf 𝓘 e (idemCompl 𝓘 e) = idemBot 𝓘 := by
  -- e(1 - e) = e - e^2 = 0
  ext
  simp [idemInf_val, idemCompl_val, idemBot_val, mul_sub, e.2]

/-!  Complements of ⊥ and ⊤  -/

@[simp] lemma idemCompl_top (𝓘 : BoolIdeal) :
  idemCompl 𝓘 (idemTop 𝓘 : LinfQuotRingIdem 𝓘 R) = idemBot 𝓘 := by
  ext; simp [idemCompl_val, idemTop_val, idemBot_val]

@[simp] lemma idemCompl_bot (𝓘 : BoolIdeal) :
  idemCompl 𝓘 (idemBot 𝓘 : LinfQuotRingIdem 𝓘 R) = idemTop 𝓘 := by
  ext; simp [idemCompl_val, idemTop_val, idemBot_val]

/-! ### Idempotent difference and symmetric difference -/

noncomputable def idemDiff (𝓘 : BoolIdeal)
  (e f : LinfQuotRingIdem 𝓘 R) : LinfQuotRingIdem 𝓘 R :=
  idemInf 𝓘 e (idemCompl 𝓘 f)

noncomputable def idemXor (𝓘 : BoolIdeal)
  (e f : LinfQuotRingIdem 𝓘 R) : LinfQuotRingIdem 𝓘 R :=
  idemSup 𝓘 (idemDiff 𝓘 e f) (idemDiff 𝓘 f e)

/-- Value lemma for difference. -/
@[simp] lemma idemDiff_val (e f : LinfQuotRingIdem 𝓘 R) :
  (idemDiff 𝓘 e f).1 = e.1 - e.1 * f.1 := by
  simp [idemDiff, idemInf_val, idemCompl_val, mul_sub]

/-- Value lemma for symmetric difference. -/
@[simp] lemma idemXor_val (e f : LinfQuotRingIdem 𝓘 R) :
  (idemXor 𝓘 e f).1 = (e.1 - e.1 * f.1) + (f.1 - f.1 * e.1) - (e.1 - e.1 * f.1) * (f.1 - f.1 * e.1) := by
  simp [idemXor, idemDiff, idemSup_val, idemInf_val, idemCompl_val, mul_sub, sub_eq_add_neg]
  ring

/-! Endpoints for difference. -/
@[simp] lemma idemDiff_self (e : LinfQuotRingIdem 𝓘 R) :
  idemDiff 𝓘 e e = idemBot 𝓘 := by
  ext; simp [idemDiff, idemInf_val, idemCompl_val, idemBot_val, mul_sub, e.2]

@[simp] lemma idemDiff_bot_left (e : LinfQuotRingIdem 𝓘 R) :
  idemDiff 𝓘 (idemBot 𝓘) e = idemBot 𝓘 := by
  ext; simp [idemDiff, idemInf_val, idemCompl_val, idemBot_val]

@[simp] lemma idemDiff_bot_right (e : LinfQuotRingIdem 𝓘 R) :
  idemDiff 𝓘 e (idemBot 𝓘) = e := by
  ext; simp [idemDiff, idemInf_val, idemCompl_val, idemBot_val]

@[simp] lemma idemDiff_top_right (e : LinfQuotRingIdem 𝓘 R) :
  idemDiff 𝓘 e (idemTop 𝓘) = idemBot 𝓘 := by
  ext; simp [idemDiff, idemInf_val, idemCompl_val, idemTop_val, idemBot_val, mul_sub, e.2]

/-! Symmetric difference: basic endpoints. -/
@[simp] lemma idemXor_self (e : LinfQuotRingIdem 𝓘 R) :
  idemXor 𝓘 e e = idemBot 𝓘 := by
  ext; simp [idemXor, idemDiff, idemSup_val, idemInf_val, idemCompl_val, idemBot_val, mul_sub, e.2]

@[simp] lemma idemXor_bot_left (e : LinfQuotRingIdem 𝓘 R) :
  idemXor 𝓘 (idemBot 𝓘) e = e := by
  ext; simp [idemXor, idemDiff, idemSup_val, idemInf_val, idemCompl_val, idemBot_val]

@[simp] lemma idemXor_bot_right (e : LinfQuotRingIdem 𝓘 R) :
  idemXor 𝓘 e (idemBot 𝓘) = e := by
  ext; simp [idemXor, idemDiff, idemSup_val, idemInf_val, idemCompl_val, idemBot_val]

/-! ### idemDiff / idemXor: more endpoints and symmetry -/

@[simp] lemma idemDiff_top_left (e : LinfQuotRingIdem 𝓘 R) :
  idemDiff 𝓘 (idemTop 𝓘) e = idemCompl 𝓘 e := by
  -- (⊤ \ e) = ⊤ ⊓ ¬e = ¬e
  ext; simp [idemDiff]

@[simp] lemma idemXor_top_right (e : LinfQuotRingIdem 𝓘 R) :
  idemXor 𝓘 e (idemTop 𝓘) = idemCompl 𝓘 e := by
  -- (e △ ⊤) = (e \ ⊤) ⊔ (⊤ \ e) = ⊥ ⊔ ¬e = ¬e
  ext; simp [idemXor, idemDiff]

@[simp] lemma idemXor_top_left (e : LinfQuotRingIdem 𝓘 R) :
  idemXor 𝓘 (idemTop 𝓘) e = idemCompl 𝓘 e := by
  -- (⊤ △ e) = (⊤ \ e) ⊔ (e \ ⊤) = ¬e ⊔ ⊥ = ¬e
  ext; simp [idemXor, idemDiff]

@[simp] lemma idemXor_comm (e f : LinfQuotRingIdem 𝓘 R) :
  idemXor 𝓘 e f = idemXor 𝓘 f e := by
  -- symmetric by construction + commutativity of ⊔ and ⊓
  simp [idemXor, idemDiff, idemSup_comm 𝓘, idemInf_comm 𝓘]

@[simp] lemma idemXor_compl_right (e : LinfQuotRingIdem 𝓘 R) :
  idemXor 𝓘 e (idemCompl 𝓘 e) = idemTop 𝓘 := by
  -- (e \ ¬e) ⊔ (¬e \ e) = e ⊔ ¬e = ⊤
  ext; simp [idemXor, idemDiff]

@[simp] lemma idemXor_compl_left (e : LinfQuotRingIdem 𝓘 R) :
  idemXor 𝓘 (idemCompl 𝓘 e) e = idemTop 𝓘 := by
  ext; simp [idemXor, idemDiff]

@[simp] lemma idemDiff_compl_right (e f : LinfQuotRingIdem 𝓘 R) :
  idemDiff 𝓘 e (idemCompl 𝓘 f) = idemInf 𝓘 e f := by
  -- e \ ¬f = e ⊓ f
  ext; simp [idemDiff]

@[simp] lemma idemXor_top_top {R} [CommRing R] [DecidableEq R] (𝓘 : BoolIdeal) :
  idemXor (R := R) 𝓘 (idemTop 𝓘) (idemTop 𝓘) = idemBot 𝓘 := by
  -- ⊤ △ ⊤ = ⊥
  ext; simp [idemXor, idemDiff]

@[simp] lemma idemXor_compl_compl (e : LinfQuotRingIdem 𝓘 R) :
  idemXor 𝓘 (idemCompl 𝓘 e) (idemCompl 𝓘 e) = idemBot 𝓘 := by
  -- ¬e △ ¬e = ⊥
  ext; simp [idemXor, idemDiff]

end BooleanAlgebraOnIdempotents

/-! ## Stone Boolean Algebra Isomorphism 

This section establishes that the Stone equivalence preserves Boolean operations.
The preservation lemmas are marked @[simp] for automatic simplification.
Together with the value lemmas for idemInf/Sup/Compl, these provide a complete
simp-normal form for reasoning about Boolean operations through the Stone map.
-/

section StoneBAIso
variable {R : Type*} [CommRing R] [DecidableEq R] (𝓘 : BoolIdeal)
variable [Nontrivial R] [TwoIdempotents R]

/-- Upgraded equivalence preserving Boolean operations. -/
noncomputable def StoneBAIso : PowQuot 𝓘 ≃ LinfQuotRingIdem 𝓘 R := StoneEquiv 𝓘

/-- The Stone map preserves intersection/infimum. -/
@[simp] lemma stone_preserves_inf (A B : Set ℕ) :
    PhiStoneIdem (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) (A ∩ B)) =
    idemInf 𝓘 (PhiStoneIdem (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) A))
              (PhiStoneIdem (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) B)) := by
  apply Subtype.ext
  simp only [PhiStoneIdem, idemInf_val, chi_inter, map_mul]

/-- The Stone map preserves union/supremum. -/
@[simp] lemma stone_preserves_sup (A B : Set ℕ) :
    PhiStoneIdem (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) (A ∪ B)) =
    idemSup 𝓘 (PhiStoneIdem (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) A))
              (PhiStoneIdem (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) B)) := by
  apply Subtype.ext
  simp only [PhiStoneIdem, idemSup_val, chi_union, map_add, map_sub, map_mul]

/-- The Stone map preserves complement. -/
@[simp] lemma stone_preserves_compl (A : Set ℕ) :
    PhiStoneIdem (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) Aᶜ) =
    idemCompl 𝓘 (PhiStoneIdem (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) A)) := by
  apply Subtype.ext
  simp only [PhiStoneIdem, idemCompl_val, chi_compl, map_sub, map_one]

@[simp] lemma PhiStoneIdem_empty
  {R} [CommRing R] [DecidableEq R] (𝓘 : BoolIdeal) :
  (PhiStoneIdem (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) (∅ : Set ℕ))).1 = 0 := by
  classical
  simp [PhiStoneIdem, chi_empty]

@[simp] lemma PhiStoneIdem_univ
  {R} [CommRing R] [DecidableEq R] (𝓘 : BoolIdeal) :
  (PhiStoneIdem (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) (Set.univ : Set ℕ))).1 = 1 := by
  classical
  simp [PhiStoneIdem, chi_univ]

/-!  More Φ-preservation at the endpoints (⊥, ⊤)  -/

@[simp] lemma stone_preserves_bot
    {R} [CommRing R] [DecidableEq R] [Nontrivial R] [TwoIdempotents R]
    (𝓘 : BoolIdeal) :
  PhiStoneIdem (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) (∅ : Set ℕ)) = idemBot 𝓘 := by
  classical
  apply Subtype.ext
  simp [PhiStoneIdem, idemBot_val, chi_empty]

@[simp] lemma stone_preserves_top
    {R} [CommRing R] [DecidableEq R] [Nontrivial R] [TwoIdempotents R]
    (𝓘 : BoolIdeal) :
  PhiStoneIdem (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) (Set.univ : Set ℕ)) = idemTop 𝓘 := by
  classical
  apply Subtype.ext
  simp [PhiStoneIdem, idemTop_val, chi_univ]

/-!  Difference and symmetric difference under Φ  -/

@[simp] lemma stone_preserves_diff
    {R} [CommRing R] [DecidableEq R] [Nontrivial R] [TwoIdempotents R]
    (𝓘 : BoolIdeal) (A B : Set ℕ) :
  PhiStoneIdem (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) (A \ B)) =
    idemInf 𝓘
      (PhiStoneIdem (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) A))
      (idemCompl 𝓘 (PhiStoneIdem (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) B))) := by
  classical
  -- A \ B = A ∩ Bᶜ
  have h : A \ B = A ∩ Bᶜ := by
    ext n; simp [Set.mem_diff]
  -- Push Φ through ∩ and then through complement
  rw [h]
  rw [stone_preserves_inf]
  congr 2
  exact stone_preserves_compl 𝓘 B

@[simp] lemma stone_preserves_symmDiff
    {R} [CommRing R] [DecidableEq R] [Nontrivial R] [TwoIdempotents R]
    (𝓘 : BoolIdeal) (A B : Set ℕ) :
  PhiStoneIdem (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) (A △ B)) =
    idemSup 𝓘
      (idemInf 𝓘
        (PhiStoneIdem (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) A))
        (idemCompl 𝓘 (PhiStoneIdem (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) B))))
      (idemInf 𝓘
        (PhiStoneIdem (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) B))
        (idemCompl 𝓘 (PhiStoneIdem (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) A)))) := by
  classical
  -- Use the definitional identity A △ B = (A \ B) ∪ (B \ A)
  have : A △ B = (A \ B) ∪ (B \ A) := by rfl
  -- Push Φ through ∪, then rewrite both A\B and B\A via the previous lemma
  rw [this]
  rw [stone_preserves_sup]
  simp only [stone_preserves_diff]

/-!  Easy corollaries for endpoints under Φ (difference / symmetric difference) -/

@[simp] lemma stone_preserves_diff_self
    {R} [CommRing R] [DecidableEq R] [Nontrivial R] [TwoIdempotents R]
    (𝓘 : BoolIdeal) (A : Set ℕ) :
  PhiStoneIdem (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) (A \ A)) = idemBot 𝓘 := by
  classical
  -- Φ(A \ A) = Φ(A) ⊓ (¬Φ(A)) = ⊥
  simp [stone_preserves_diff]

@[simp] lemma stone_preserves_diff_empty
    {R} [CommRing R] [DecidableEq R] [Nontrivial R] [TwoIdempotents R]
    (𝓘 : BoolIdeal) (A : Set ℕ) :
  PhiStoneIdem (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) (A \ ∅)) =
    PhiStoneIdem (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) A) := by
  classical
  -- Φ(A \ ∅) = Φ(A) ⊓ (¬Φ(∅)) = Φ(A) ⊓ ⊤ = Φ(A)
  simp [stone_preserves_diff]

@[simp] lemma stone_preserves_symmDiff_self
    {R} [CommRing R] [DecidableEq R] [Nontrivial R] [TwoIdempotents R]
    (𝓘 : BoolIdeal) (A : Set ℕ) :
  PhiStoneIdem (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) (A △ A)) = idemBot 𝓘 := by
  classical
  -- Φ(A △ A) = (Φ(A) ⊓ ¬Φ(A)) ⊔ (Φ(A) ⊓ ¬Φ(A)) = ⊥ ⊔ ⊥ = ⊥
  simp [stone_preserves_symmDiff]

@[simp] lemma stone_preserves_symmDiff_empty
    {R} [CommRing R] [DecidableEq R] [Nontrivial R] [TwoIdempotents R]
    (𝓘 : BoolIdeal) (A : Set ℕ) :
  PhiStoneIdem (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) (A △ ∅)) =
    PhiStoneIdem (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) A) := by
  classical
  -- Φ(A △ ∅) = (Φ(A) ⊓ ¬Φ(∅)) ⊔ (Φ(∅) ⊓ ¬Φ(A)) = (Φ(A) ⊓ ⊤) ⊔ (⊥ ⊓ ¬Φ(A)) = Φ(A)
  simp [stone_preserves_symmDiff]

/-! Φ-preservation aliases using idemDiff and idemXor -/

@[simp] lemma stone_preserves_diff'
    {R} [CommRing R] [DecidableEq R] [Nontrivial R] [TwoIdempotents R]
    (𝓘 : BoolIdeal) (A B : Set ℕ) :
  PhiStoneIdem (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) (A \ B)) =
    idemDiff 𝓘
      (PhiStoneIdem (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) A))
      (PhiStoneIdem (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) B)) := by
  simp [idemDiff, stone_preserves_diff]

@[simp] lemma stone_preserves_symmDiff'
    {R} [CommRing R] [DecidableEq R] [Nontrivial R] [TwoIdempotents R]
    (𝓘 : BoolIdeal) (A B : Set ℕ) :
  PhiStoneIdem (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) (A △ B)) =
    idemXor 𝓘
      (PhiStoneIdem (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) A))
      (PhiStoneIdem (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) B)) := by
  simp [idemXor, idemDiff, stone_preserves_symmDiff]

-- Φ endpoints with univ
@[simp] lemma stone_preserves_diff_univ
    {R} [CommRing R] [DecidableEq R] [Nontrivial R] [TwoIdempotents R]
    (𝓘 : BoolIdeal) (A : Set ℕ) :
  PhiStoneIdem (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) (Set.univ \ A)) =
    idemCompl 𝓘 (PhiStoneIdem (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) A)) := by
  simp [stone_preserves_diff, stone_preserves_top]

@[simp] lemma stone_preserves_symmDiff_univ
    {R} [CommRing R] [DecidableEq R] [Nontrivial R] [TwoIdempotents R]
    (𝓘 : BoolIdeal) (A : Set ℕ) :
  PhiStoneIdem (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) (Set.univ △ A)) =
    idemCompl 𝓘 (PhiStoneIdem (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) A)) := by
  simp [stone_preserves_symmDiff, stone_preserves_top, idemXor_top_left]

/-!  More Φ-endpoints with `univ` (right-hand side) -/

@[simp] lemma stone_preserves_diff_univ_right
    {R} [CommRing R] [DecidableEq R] [Nontrivial R] [TwoIdempotents R]
    (𝓘 : BoolIdeal) (A : Set ℕ) :
  PhiStoneIdem (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) (A \ Set.univ)) = idemBot 𝓘 := by
  simp [Set.diff_univ, stone_preserves_bot]

@[simp] lemma stone_preserves_symmDiff_univ_right
    {R} [CommRing R] [DecidableEq R] [Nontrivial R] [TwoIdempotents R]
    (𝓘 : BoolIdeal) (A : Set ℕ) :
  PhiStoneIdem (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) (A △ Set.univ)) =
    idemCompl 𝓘 (PhiStoneIdem (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) A)) := by
  rw [stone_preserves_symmDiff']
  simp [idemXor_comm, stone_preserves_symmDiff_univ]

-- Φ(univ \ univ) = ⊥
@[simp] lemma stone_preserves_diff_univ_univ
    {R} [CommRing R] [DecidableEq R] [Nontrivial R] [TwoIdempotents R]
    (𝓘 : BoolIdeal) :
  PhiStoneIdem (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) (Set.univ \ (Set.univ : Set ℕ))) =
    idemBot 𝓘 := by
  simp [Set.diff_univ]

-- Φ(univ △ univ) = ⊥
@[simp] lemma stone_preserves_symmDiff_univ_univ
    {R} [CommRing R] [DecidableEq R] [Nontrivial R] [TwoIdempotents R]
    (𝓘 : BoolIdeal) :
  PhiStoneIdem (R := R) 𝓘 (Quot.mk (sdiffSetoid 𝓘) ((Set.univ : Set ℕ) △ Set.univ)) =
    idemBot 𝓘 := by
  simp

end StoneBAIso

/-! ## Path A: BooleanAlgebra Transport

We now implement the BooleanAlgebra structure on PowQuot 𝓘 and transport it
to LinfQuotRingIdem 𝓘 R via the Stone equivalence.

The preservation lemmas already establish that:
- PhiStoneIdem preserves intersection (stone_preserves_inf)
- PhiStoneIdem preserves union (stone_preserves_sup)
- PhiStoneIdem preserves complement (stone_preserves_compl)
- PhiStoneIdem preserves bottom/top (stone_preserves_bot, stone_preserves_top)
-/

section PathA_BooleanAlgebra

variable (𝓘 : BoolIdeal)

/-! ### Well-definedness lemmas for Boolean operations -/

private lemma inf_well_defined (A₁ A₂ B₁ B₂ : Set ℕ) 
    (hA : A₁ △ A₂ ∈ 𝓘.mem) (hB : B₁ △ B₂ ∈ 𝓘.mem) :
    (A₁ ∩ B₁) △ (A₂ ∩ B₂) ∈ 𝓘.mem := by
  -- The symmetric difference of intersections is contained in the union of symmetric differences
  have : (A₁ ∩ B₁) △ (A₂ ∩ B₂) ⊆ (A₁ △ A₂) ∪ (B₁ △ B₂) := by
    intro x hx
    simp only [sdiff, Set.mem_union, Set.mem_diff, Set.mem_inter_iff] at hx ⊢
    rcases hx with ⟨⟨hA₁, hB₁⟩, h₂⟩ | ⟨⟨hA₂, hB₂⟩, h₁⟩
    · -- x ∈ (A₁ ∩ B₁) \ (A₂ ∩ B₂)
      -- So x ∈ A₁, x ∈ B₁, and ¬(x ∈ A₂ ∧ x ∈ B₂)
      push_neg at h₂
      -- Either x ∉ A₂ or x ∉ B₂
      by_cases hxA₂ : x ∈ A₂
      · -- x ∈ A₁, x ∈ A₂, x ∈ B₁, x ∉ B₂
        right; left; exact ⟨hB₁, h₂ hxA₂⟩
      · -- x ∈ A₁, x ∉ A₂
        left; left; exact ⟨hA₁, hxA₂⟩
    · -- x ∈ (A₂ ∩ B₂) \ (A₁ ∩ B₁)
      -- So x ∈ A₂, x ∈ B₂, and ¬(x ∈ A₁ ∧ x ∈ B₁)
      push_neg at h₁
      -- Either x ∉ A₁ or x ∉ B₁
      by_cases hxA₁ : x ∈ A₁
      · -- x ∈ A₁, x ∈ A₂, x ∈ B₂, x ∉ B₁
        right; right; exact ⟨hB₂, h₁ hxA₁⟩
      · -- x ∉ A₁, x ∈ A₂
        left; right; exact ⟨hA₂, hxA₁⟩
  exact 𝓘.downward this (𝓘.union_mem hA hB)

private lemma sup_well_defined (A₁ A₂ B₁ B₂ : Set ℕ)
    (hA : A₁ △ A₂ ∈ 𝓘.mem) (hB : B₁ △ B₂ ∈ 𝓘.mem) :
    (A₁ ∪ B₁) △ (A₂ ∪ B₂) ∈ 𝓘.mem := by
  -- Similar to inf_well_defined
  have : (A₁ ∪ B₁) △ (A₂ ∪ B₂) ⊆ (A₁ △ A₂) ∪ (B₁ △ B₂) := by
    intro x hx
    simp only [sdiff, Set.mem_union, Set.mem_diff] at hx ⊢
    rcases hx with ⟨h₁, h₂⟩ | ⟨h₂, h₁⟩
    · rcases h₁ with hA₁ | hB₁
      · push_neg at h₂
        left; left; exact ⟨hA₁, h₂.1⟩
      · push_neg at h₂
        right; left; exact ⟨hB₁, h₂.2⟩
    · rcases h₂ with hA₂ | hB₂
      · push_neg at h₁
        left; right; exact ⟨hA₂, h₁.1⟩
      · push_neg at h₁
        right; right; exact ⟨hB₂, h₁.2⟩
  exact 𝓘.downward this (𝓘.union_mem hA hB)

private lemma compl_well_defined (A B : Set ℕ) (h : A △ B ∈ 𝓘.mem) :
    Aᶜ △ Bᶜ ∈ 𝓘.mem := by
  -- Aᶜ △ Bᶜ = A △ B
  have : Aᶜ △ Bᶜ = A △ B := by
    ext x
    simp only [sdiff, Set.mem_union, Set.mem_diff, Set.mem_compl_iff]
    tauto
  rw [this]
  exact h

/-! ### Define Boolean operations on PowQuot using Quot.liftOn -/

/-- Intersection operation on PowQuot 𝓘. -/
def PowQuot.inf (x y : PowQuot 𝓘) : PowQuot 𝓘 :=
  Quot.liftOn₂ x y 
    (fun A B => Quot.mk (sdiffSetoid 𝓘) (A ∩ B))
    -- First witness: vary B, fix A
    (fun A B B' hBB' => by
      apply Quot.sound
      apply inf_well_defined 𝓘 A A B B'
      · -- A △ A = ∅ ∈ 𝓘.mem
        rw [sdiff_self]
        exact 𝓘.empty_mem
      · exact hBB')
    -- Second witness: vary A, fix B
    (fun A A' B hAA' => by
      apply Quot.sound
      apply inf_well_defined 𝓘 A A' B B
      · exact hAA'
      · -- B △ B = ∅ ∈ 𝓘.mem
        rw [sdiff_self]
        exact 𝓘.empty_mem)

/-- Union operation on PowQuot 𝓘. -/
def PowQuot.sup (x y : PowQuot 𝓘) : PowQuot 𝓘 :=
  Quot.liftOn₂ x y
    (fun A B => Quot.mk (sdiffSetoid 𝓘) (A ∪ B))
    -- First witness: vary B, fix A  
    (fun A B B' hBB' => by
      apply Quot.sound
      apply sup_well_defined 𝓘 A A B B'
      · -- A △ A = ∅ ∈ 𝓘.mem
        rw [sdiff_self]
        exact 𝓘.empty_mem
      · exact hBB')
    -- Second witness: vary A, fix B
    (fun A A' B hAA' => by
      apply Quot.sound
      apply sup_well_defined 𝓘 A A' B B
      · exact hAA'
      · -- B △ B = ∅ ∈ 𝓘.mem
        rw [sdiff_self]
        exact 𝓘.empty_mem)

/-- Complement operation on PowQuot 𝓘. -/
def PowQuot.compl (x : PowQuot 𝓘) : PowQuot 𝓘 :=
  Quot.liftOn x
    (fun A => Quot.mk (sdiffSetoid 𝓘) Aᶜ)
    (fun A B h => by
      -- Need to show Aᶜ △ Bᶜ ∈ 𝓘.mem when A △ B ∈ 𝓘.mem
      apply Quot.sound
      apply compl_well_defined 𝓘 A B h)

/-- Bottom element of PowQuot 𝓘. -/
def PowQuot.bot : PowQuot 𝓘 := Quot.mk (sdiffSetoid 𝓘) ∅

/-- Top element of PowQuot 𝓘. -/
def PowQuot.top : PowQuot 𝓘 := Quot.mk (sdiffSetoid 𝓘) Set.univ

/-! ### BooleanAlgebra instance for PowQuot 

PowQuot has natural Boolean operations that form a Boolean algebra structure.
The complete proof requires showing all Boolean algebra axioms hold
using the well-definedness lemmas proven above.

Note: Full BooleanAlgebra instance left as future work.
The operations PowQuot.inf/sup/compl/bot/top are defined and well-defined.
Standard quotient techniques would complete the instance.
-/

/-! ### Transport BooleanAlgebra to LinfQuotRingIdem 

LinfQuotRingIdem inherits Boolean operations via the Stone equivalence.
The preservation lemmas stone_preserves_inf/sup/compl establish that
StoneEquiv (aliased as StoneBAIso) is a Boolean algebra isomorphism.

Note: Transport of BooleanAlgebra structure left as future work.
The operations idemInf/idemSup/idemCompl/idemBot/idemTop are defined.
The preservation lemmas prove StoneEquiv preserves all Boolean operations.
-/

/-! 
## Path A Implementation Summary

The Path A groundwork is now complete:
1. ✓ Well-definedness lemmas for Boolean operations on quotients
2. ✓ Definitions of PowQuot.inf/sup/compl/bot/top  
3. ✓ StoneBAIso alias restored (points to StoneEquiv)
4. ✓ All preservation lemmas showing StoneEquiv preserves Boolean ops

What remains for full Path A completion:
- Standard BooleanAlgebra instance proofs (reduce to set identities via Quot.induction)
- Transport along StoneEquiv using the preservation lemmas

The infrastructure is fully in place for these final steps.
-/

end PathA_BooleanAlgebra

/-! ## Minimal Boolean Algebra Skeleton for PowQuot

These are proof-free: they're just instances that point min, max, ᶜ, ⊥, ⊤ at your
already-defined well-defined quotient operations, plus definitional simp lemmas.

Note: We use Min/Max instances as a stepping stone. Once we build the lattice
structure (SemilatticeInf/SemilatticeSup), these will automatically promote to
Inf/Sup and give us the proper ⊓/⊔ notation. This is the standard Lean 4/Mathlib
approach: Min/Max → lattice structure → Inf/Sup.
-/

section PowQuotBooleanSkeleton

variable (𝓘 : BoolIdeal)

-- 1) Register the canonical lattice operations for PowQuot 𝓘
-- Note: Using Min/Max for now as a stepping stone. Full lattice Inf/Sup requires
-- the lattice structure to be built first. These will become Inf/Sup when we
-- construct SemilatticeInf/SemilatticeSup instances.
instance : Min (PowQuot 𝓘) := ⟨PowQuot.inf 𝓘⟩
instance : Max (PowQuot 𝓘) := ⟨PowQuot.sup 𝓘⟩
instance : HasCompl (PowQuot 𝓘) := ⟨PowQuot.compl 𝓘⟩
instance : Bot (PowQuot 𝓘) := ⟨PowQuot.bot 𝓘⟩
instance : Top (PowQuot 𝓘) := ⟨PowQuot.top 𝓘⟩

-- 2) Definitional computation rules (using min/max for now)
@[simp] lemma min_mk_mk (A B : Set ℕ) :
    (min (Quot.mk (sdiffSetoid 𝓘) A) (Quot.mk (sdiffSetoid 𝓘) B) : PowQuot 𝓘)
      = Quot.mk (sdiffSetoid 𝓘) (A ∩ B) := rfl

@[simp] lemma max_mk_mk (A B : Set ℕ) :
    (max (Quot.mk (sdiffSetoid 𝓘) A) (Quot.mk (sdiffSetoid 𝓘) B) : PowQuot 𝓘)
      = Quot.mk (sdiffSetoid 𝓘) (A ∪ B) := rfl

@[simp] lemma compl_mk (A : Set ℕ) :
    ((Quot.mk (sdiffSetoid 𝓘) A)ᶜ : PowQuot 𝓘)
      = Quot.mk (sdiffSetoid 𝓘) Aᶜ := rfl

@[simp] lemma bot_def :
    (⊥ : PowQuot 𝓘) = Quot.mk (sdiffSetoid 𝓘) (∅ : Set ℕ) := rfl

@[simp] lemma top_def :
    (⊤ : PowQuot 𝓘) = Quot.mk (sdiffSetoid 𝓘) (Set.univ : Set ℕ) := rfl

-- 3) (optional) local pretty notations (will become proper ⊓/⊔ after lattice instance)
local infixl:70 " ⊓ᵖ " => (fun x y : PowQuot 𝓘 => min x y)
local infixl:65 " ⊔ᵖ " => (fun x y : PowQuot 𝓘 => max x y)
local prefix:max "ᶜᵖ" => (fun x : PowQuot 𝓘 => xᶜ)

-- sanity pings
example (A B : Set ℕ) :
    ((Quot.mk (sdiffSetoid 𝓘) A) ⊓ᵖ (Quot.mk (sdiffSetoid 𝓘) B))
      = Quot.mk (sdiffSetoid 𝓘) (A ∩ B) := by simp

example (A B : Set ℕ) :
    ((Quot.mk (sdiffSetoid 𝓘) A) ⊔ᵖ (Quot.mk (sdiffSetoid 𝓘) B))
      = Quot.mk (sdiffSetoid 𝓘) (A ∪ B) := by simp

example (A : Set ℕ) :
    (ᶜᵖ (Quot.mk (sdiffSetoid 𝓘) A))
      = Quot.mk (sdiffSetoid 𝓘) Aᶜ := by simp

end PowQuotBooleanSkeleton

/-! ## Order Structure on PowQuot

We define the order on PowQuot via "difference small": x ≤ y iff (A \ B) ∈ 𝓘.mem.
This gives us a partial order that will support the Boolean algebra structure.
-/

/-! ## Order & Lattice structure on `PowQuot 𝓘`

We equip `PowQuot 𝓘` with the "difference small" order:
`x ≤ y`  iff for reps `A,B`,  `(A \ B) ∈ 𝓘.mem`.

Key points:
* `LE` is defined with `Quot.liftOn₂` using **two** compatibility witnesses.
* `@[simp]` mk‑lemmas expose the reps so `simp` can reduce goals to set facts.
* Meet/join come from your canonical operations, so `⊓/⊔` compute by `rfl`.
* All lattice laws are proved by nested `Quot.inductionOn` + basic set algebra.
-/

section PowQuotOrder

variable (𝓘 : BoolIdeal)

-- Make empty_mem a simp lemma locally so simp can close goals of the form ∅ ∈ 𝓘.mem
attribute [local simp] BoolIdeal.empty_mem

/-- The order on `PowQuot`: `x ≤ y` iff the difference of reps is small. -/
instance : LE (PowQuot 𝓘) where
  le x y :=
    Quot.liftOn₂ x y (fun A B : Set ℕ => (A \ B) ∈ 𝓘.mem)
      -- vary the 2nd representative (fix A)
      (fun A B B' (hBB' : B △ B' ∈ 𝓘.mem) => by
        -- show (A\B) ∈ I ↔ (A\B') ∈ I
        apply propext
        constructor
        · intro h
          -- A \ B' ⊆ (A \ B) ∪ (B △ B')
          have H : (A \ B') ⊆ (A \ B) ∪ (B △ B') := by
            intro x hx; rcases hx with ⟨hA, hB'⟩
            by_cases hB : x ∈ B
            · -- x∈B, x∉B'  ⇒ x∈B△B'
              right
              -- B △ B' = (B \ B') ∪ (B' \ B)
              -- and here x∈B\B'
              exact Or.inl ⟨hB, hB'⟩
            · -- x∉B  ⇒ x∈A\B
              left; exact ⟨hA, hB⟩
          exact 𝓘.downward H (𝓘.union_mem h hBB')
        · intro h
          -- A \ B ⊆ (A \ B') ∪ (B △ B')
          have H : (A \ B) ⊆ (A \ B') ∪ (B △ B') := by
            intro x hx; rcases hx with ⟨hA, hB⟩
            by_cases hB' : x ∈ B'
            · -- x∈B', x∉B ⇒ x∈B△B'
              right; exact Or.inr ⟨hB', hB⟩
            · -- x∉B' ⇒ x∈A\B'
              left; exact ⟨hA, hB'⟩
          exact 𝓘.downward H (𝓘.union_mem h hBB'))
      -- vary the 1st representative (fix B)
      (fun A A' B (hAA' : A △ A' ∈ 𝓘.mem) => by
        apply propext
        constructor
        · intro h
          -- A' \ B ⊆ (A \ B) ∪ (A △ A')
          have H : (A' \ B) ⊆ (A \ B) ∪ (A △ A') := by
            intro x hx; rcases hx with ⟨hA', hB⟩
            by_cases hA : x ∈ A
            · left;  exact ⟨hA, hB⟩
            · right; exact Or.inr ⟨hA', hA⟩
          exact 𝓘.downward H (𝓘.union_mem h hAA')
        · intro h
          -- A \ B ⊆ (A' \ B) ∪ (A △ A')
          have H : (A \ B) ⊆ (A' \ B) ∪ (A △ A') := by
            intro x hx; rcases hx with ⟨hA, hB⟩
            by_cases hA' : x ∈ A'
            · left;  exact ⟨hA', hB⟩
            · right; exact Or.inl ⟨hA, hA'⟩
          exact 𝓘.downward H (𝓘.union_mem h hAA'))

/-- Unfolding rule for the order on representatives. -/
@[simp] lemma mk_le_mk (A B : Set ℕ) :
    ((Quot.mk (sdiffSetoid 𝓘) A : PowQuot 𝓘) ≤ Quot.mk (sdiffSetoid 𝓘) B) ↔
    (A \ B) ∈ 𝓘.mem := Iff.rfl


/-- Preorder under "difference small". -/
instance : Preorder (PowQuot 𝓘) where
  le := (· ≤ ·)
  le_refl := by
    intro x; refine Quot.inductionOn x ?_
    intro A; simp [mk_le_mk, Set.diff_self]
  le_trans := by
    intro x y z hxy hyz
    refine Quot.inductionOn x ?_ hxy
    intro A hAy; refine Quot.inductionOn y ?_ hAy hyz
    intro B hAB; refine Quot.inductionOn z ?_ hAB
    intro C hAB hBC
    -- want: (A \ C) ∈ I, given hAB : (A \ B) ∈ I, hBC : (B \ C) ∈ I
    -- A \ C ⊆ (A \ B) ∪ (B \ C)
    have H : (A \ C) ⊆ (A \ B) ∪ (B \ C) := by
      intro x hx; rcases hx with ⟨hA, hC⟩
      by_cases hB : x ∈ B
      · right; exact ⟨hB, hC⟩
      · left;  exact ⟨hA, hB⟩
    exact 𝓘.downward H (𝓘.union_mem hAB hBC)

/-- Partial order: antisymmetry via symmetric difference. -/
instance : PartialOrder (PowQuot 𝓘) where
  le_antisymm := by
    intro x y hxy hyx
    induction x using Quot.inductionOn with | _ A =>
    induction y using Quot.inductionOn with | _ B =>
    simp only [mk_le_mk] at hxy hyx
    -- (A △ B) = (A \ B) ∪ (B \ A)
    apply Quot.sound
    have : A △ B = (A \ B) ∪ (B \ A) := by
      ext n; -- elementwise set reasoning
      simp [sdiff, Set.mem_union, Set.mem_diff]  -- uses your local `sdiff`/simp setup
    simpa [this] using 𝓘.union_mem hxy hyx

/-- Semilattice with meet: reuses your canonical `PowQuot.inf`. -/
instance : SemilatticeInf (PowQuot 𝓘) where
  inf := PowQuot.inf 𝓘
  inf_le_left := by
    intro x y; refine Quot.inductionOn x ?_
    intro A; refine Quot.inductionOn y ?_
    intro B; -- ((A ∩ B) \ A) ∈ I  since it's ∅
    simp [mk_le_mk, PowQuot.inf, Set.diff_eq_empty.mpr Set.inter_subset_left]
  inf_le_right := by
    intro x y; refine Quot.inductionOn x ?_
    intro A; refine Quot.inductionOn y ?_
    intro B
    simp [mk_le_mk, PowQuot.inf, Set.diff_eq_empty.mpr Set.inter_subset_right]
  le_inf := by
    intro x y z hxy hxz
    induction x using Quot.inductionOn with | _ A =>
    induction y using Quot.inductionOn with | _ B =>
    induction z using Quot.inductionOn with | _ C =>
    simp only [mk_le_mk, PowQuot.inf] at hxy hxz ⊢
    -- want (A \ (B ∩ C)) ∈ I  and  A \ (B ∩ C) = (A \ B) ∪ (A \ C)
    have : A \ (B ∩ C) = (A \ B) ∪ (A \ C) := by
      ext n; simp [Set.mem_diff, Set.mem_inter_iff, Set.mem_union]; tauto
    simpa [this] using 𝓘.union_mem hxy hxz

/-- Semilattice with join: reuses your canonical `PowQuot.sup`. -/
instance : SemilatticeSup (PowQuot 𝓘) where
  sup := PowQuot.sup 𝓘
  le_sup_left := by
    intro x y; refine Quot.inductionOn x ?_
    intro A; refine Quot.inductionOn y ?_
    intro B
    -- (A \ (A ∪ B)) = ∅
    simp [mk_le_mk, PowQuot.sup, Set.diff_eq_empty.mpr (Set.subset_union_left)]
  le_sup_right := by
    intro x y; refine Quot.inductionOn x ?_
    intro A; refine Quot.inductionOn y ?_
    intro B
    simp [mk_le_mk, PowQuot.sup, Set.diff_eq_empty.mpr (Set.subset_union_right)]
  sup_le := by
    intro x y z hxz hyz
    induction x using Quot.inductionOn with | _ A =>
    induction y using Quot.inductionOn with | _ B =>
    induction z using Quot.inductionOn with | _ C =>
    simp only [mk_le_mk, PowQuot.sup] at hxz hyz ⊢
    -- ((A ∪ B) \ C) = (A \ C) ∪ (B \ C)
    have : (A ∪ B) \ C = (A \ C) ∪ (B \ C) := by
      ext n; simp [Set.mem_diff, Set.mem_union]; tauto
    simpa [this] using 𝓘.union_mem hxz hyz

/-- Meet and join compute definitionally on representatives. -/
@[simp] lemma mk_inf_mk (A B : Set ℕ) :
    ((Quot.mk (sdiffSetoid 𝓘) A) ⊓ (Quot.mk (sdiffSetoid 𝓘) B) : PowQuot 𝓘)
      = Quot.mk (sdiffSetoid 𝓘) (A ∩ B) := rfl

@[simp] lemma mk_sup_mk (A B : Set ℕ) :
    ((Quot.mk (sdiffSetoid 𝓘) A) ⊔ (Quot.mk (sdiffSetoid 𝓘) B) : PowQuot 𝓘)
      = Quot.mk (sdiffSetoid 𝓘) (A ∪ B) := rfl

/-- Complement computes definitionally on representatives -/
@[simp] lemma mk_compl (A : Set ℕ) :
  ((Quot.mk (sdiffSetoid 𝓘) A : PowQuot 𝓘)ᶜ) =
  Quot.mk (sdiffSetoid 𝓘) (Aᶜ) := rfl

/-- Top element is the equivalence class of the universe -/
@[simp] lemma mk_top :
  (⊤ : PowQuot 𝓘) = Quot.mk (sdiffSetoid 𝓘) (Set.univ : Set ℕ) := rfl

/-- Bottom element is the equivalence class of the empty set -/
@[simp] lemma mk_bot :
  (⊥ : PowQuot 𝓘) = Quot.mk (sdiffSetoid 𝓘) (∅ : Set ℕ) := rfl

/-- Assemble the lattice & distributivity. -/
instance : Lattice (PowQuot 𝓘) where
  __ := (inferInstance : SemilatticeInf (PowQuot 𝓘))
  __ := (inferInstance : SemilatticeSup (PowQuot 𝓘))

instance : DistribLattice (PowQuot 𝓘) where
  __ := (inferInstance : Lattice (PowQuot 𝓘))
  le_sup_inf := by
    intro x y z
    refine Quot.inductionOn x ?_
    intro A; refine Quot.inductionOn y ?_
    intro B; refine Quot.inductionOn z ?_
    intro C
    -- After unfolding, we need to prove distributivity at the set level
    -- The goal after simp is showing a difference is in the ideal
    simp only [mk_le_mk, mk_sup_mk, mk_inf_mk]
    -- Need to show: ((A ∪ B) ∩ (A ∪ C)) \ (A ∪ B ∩ C) ∈ 𝓘.mem
    -- This is empty because (A ∪ B) ∩ (A ∪ C) ⊆ A ∪ (B ∩ C)
    have : (A ∪ B) ∩ (A ∪ C) ⊆ A ∪ (B ∩ C) := by
      intro n hn
      simp [Set.mem_inter_iff, Set.mem_union] at hn ⊢
      tauto
    rw [Set.diff_eq_empty.mpr this]
    exact 𝓘.empty_mem

/-- Boolean algebra: `sdiff` is defined as `x ⊓ yᶜ`, other fields are already in scope. -/
instance : BooleanAlgebra (PowQuot 𝓘) where
  __ := (inferInstance : DistribLattice (PowQuot 𝓘))
  compl := PowQuot.compl 𝓘
  sdiff x y := x ⊓ yᶜ
  top := ⊤
  bot := ⊥
  inf_compl_le_bot := by
    intro x
    refine Quot.inductionOn x ?_
    intro A
    show Quot.mk (sdiffSetoid 𝓘) A ⊓ (Quot.mk (sdiffSetoid 𝓘) A)ᶜ ≤ ⊥
    simp
  top_le_sup_compl := by
    intro x
    refine Quot.inductionOn x ?_
    intro A
    show ⊤ ≤ Quot.mk (sdiffSetoid 𝓘) A ⊔ (Quot.mk (sdiffSetoid 𝓘) A)ᶜ
    simp
  le_top := by
    intro x
    refine Quot.inductionOn x ?_
    intro A
    simp
  bot_le := by
    intro x
    refine Quot.inductionOn x ?_
    intro A
    simp

end PowQuotOrder

/-! ## Additional @[simp] lemmas and smoke tests for PowQuot Boolean algebra -/

section PowQuotBA_Polish

variable (𝓘 : BoolIdeal)

/-! ### Smoke tests for instance synthesis -/

-- Instance synthesis checks
#check (inferInstance : Preorder        (PowQuot 𝓘))
#check (inferInstance : PartialOrder    (PowQuot 𝓘))
#check (inferInstance : Lattice         (PowQuot 𝓘))
#check (inferInstance : DistribLattice  (PowQuot 𝓘))
#check (inferInstance : BooleanAlgebra  (PowQuot 𝓘))

-- Basic law verification
example (x y : PowQuot 𝓘) : x ⊓ y = y ⊓ x := inf_comm x y
example (x y : PowQuot 𝓘) : x ⊔ y = y ⊔ x := sup_comm x y
example (x : PowQuot 𝓘)   : x ⊓ xᶜ = ⊥     := inf_compl_eq_bot
example (x : PowQuot 𝓘)   : x ⊔ xᶜ = ⊤     := sup_compl_eq_top

-- Additional Boolean algebra laws
example (x y z : PowQuot 𝓘) : x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z) := inf_sup_left x y z
example (x y z : PowQuot 𝓘) : x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z) := sup_inf_left x y z
example (x y : PowQuot 𝓘) : (x ⊔ y)ᶜ = xᶜ ⊓ yᶜ := compl_sup
example (x y : PowQuot 𝓘) : (x ⊓ y)ᶜ = xᶜ ⊔ yᶜ := compl_inf
example (x : PowQuot 𝓘) : xᶜᶜ = x := compl_compl x
example (x y : PowQuot 𝓘) : x \ y = x ⊓ yᶜ := sdiff_eq

end PowQuotBA_Polish

/-! ## Convenience constructors and additional lemmas for PowQuot -/

namespace PowQuot

variable (𝓘 : BoolIdeal)

/-- Canonical constructor into `PowQuot 𝓘` from a set representative. -/
@[reducible] def mk (A : Set ℕ) : PowQuot 𝓘 :=
  (Quot.mk (sdiffSetoid 𝓘) A : PowQuot 𝓘)

-- Optional scoped quotient-brackets notation
scoped notation "⟦" A "⟧ₚ" => PowQuot.mk _ A

/-- Boolean difference computes as intersection with complement -/
@[simp] lemma mk_sdiff_mk (A B : Set ℕ) :
  (mk 𝓘 A \ mk 𝓘 B) = mk 𝓘 (A ∩ Bᶜ) := rfl
-- Note: When you want `A \ B`, use `by simp [Set.diff_eq]` where
-- `Set.diff_eq` is the standard identity `A \ B = A ∩ Bᶜ`

/-- Monotonicity of the constructor w.r.t. subset -/
lemma mk_le_mk_of_subset {A B : Set ℕ} (h : A ⊆ B) :
  mk 𝓘 A ≤ mk 𝓘 B := by
  -- By definition this is `(A \ B) ∈ 𝓘.mem`
  -- But `A \ B = ∅` since `A ⊆ B`
  simpa [Papers.P4Meta.StoneSupport.mk_le_mk, Set.diff_eq_empty.mpr h] using 
    (𝓘.empty_mem : (∅ : Set ℕ) ∈ 𝓘.mem)

/-- Two sets with small symmetric difference are equal in the quotient -/
lemma mk_eq_of_sdiff_mem {A B : Set ℕ} (h : (A △ B) ∈ 𝓘.mem) :
  mk 𝓘 A = mk 𝓘 B :=
  Quot.sound h

/-! ## Functoriality under ideal inclusion -/

variable {𝓘 𝓙 : BoolIdeal}

/-- Monotone map induced by an inclusion of ideals `𝓘 ≤ 𝓙`. -/
def mapOfLe (h : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem) : PowQuot 𝓘 →o PowQuot 𝓙 where
  toFun :=
    Quot.lift
      (fun A : Set ℕ => (Quot.mk (sdiffSetoid 𝓙) A : PowQuot 𝓙))
      (by
        intro A A' hAA'
        -- well-definedness: if A ~_𝓘 A' then also A ~_𝓙 A'
        exact Quot.sound (h _ hAA'))
  monotone' := by
    intro x y hxy
    -- unpack both sides to representatives and use `mk_le_mk`
    induction x using Quot.inductionOn with | _ A =>
    induction y using Quot.inductionOn with | _ B =>
    simp only [Papers.P4Meta.StoneSupport.mk_le_mk] at hxy ⊢
    -- order on PowQuot is "difference small", so inclusion of ideals finishes it
    exact h _ hxy

/-- On representatives, `mapOfLe` is literally the identity on sets. -/
@[simp] lemma mapOfLe_mk (h : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem) (A : Set ℕ) :
    mapOfLe h (mk 𝓘 A) = mk 𝓙 A := rfl

/-- `mapOfLe` preserves infimum -/
lemma mapOfLe_inf (h : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem) (x y : PowQuot 𝓘) :
    mapOfLe h (x ⊓ y) = mapOfLe h x ⊓ mapOfLe h y := by
  induction x using Quot.inductionOn with | _ A =>
  induction y using Quot.inductionOn with | _ B =>
  simp [Papers.P4Meta.StoneSupport.mk_inf_mk, mapOfLe_mk]

/-- `mapOfLe` preserves supremum -/
lemma mapOfLe_sup (h : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem) (x y : PowQuot 𝓘) :
    mapOfLe h (x ⊔ y) = mapOfLe h x ⊔ mapOfLe h y := by
  induction x using Quot.inductionOn with | _ A =>
  induction y using Quot.inductionOn with | _ B =>
  simp

/-- `mapOfLe` preserves complement -/
lemma mapOfLe_compl (h : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem) (x : PowQuot 𝓘) :
    mapOfLe h (xᶜ) = (mapOfLe h x)ᶜ := by
  induction x using Quot.inductionOn with | _ A =>
  simp

/-- `mapOfLe` preserves top -/
lemma mapOfLe_top (h : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem) :
    mapOfLe h (⊤ : PowQuot 𝓘) = (⊤ : PowQuot 𝓙) := by
  simp

/-- `mapOfLe` preserves bot -/
lemma mapOfLe_bot (h : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem) :
    mapOfLe h (⊥ : PowQuot 𝓘) = (⊥ : PowQuot 𝓙) := by
  simp

end PowQuot

/-! ### Monotonicity of mapOfLe -/

section MapOfLeMonotone

variable {𝓘 𝓙 : BoolIdeal}

/-- `mapOfLe` is monotone when `𝓘 ≤ 𝓙` (pointwise on `mem`). -/
lemma PowQuot.mapOfLe_monotone
  {𝓘 𝓙 : BoolIdeal}
  (h : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem) :
  Monotone (PowQuot.mapOfLe h) := by
  intro x y hxy
  induction x using Quot.inductionOn
  case h A =>
  induction y using Quot.inductionOn
  case h B =>
  simp only [PowQuot.mapOfLe_mk, mk_le_mk] at hxy ⊢
  exact h (A \ B) hxy

end MapOfLeMonotone

/-! ### Boolean algebra preservation properties

The mapOfLe function preserves all Boolean operations, as shown by the lemmas above:
- mapOfLe_sup: preserves supremum
- mapOfLe_inf: preserves infimum  
- mapOfLe_compl: preserves complement
- mapOfLe_top: preserves top
- mapOfLe_bot: preserves bottom
- mapOfLe_monotone: preserves order

This demonstrates that mapOfLe is a Boolean algebra homomorphism.

Note: To package this as a formal BooleanAlgHom, additional imports would be needed.
The preservation lemmas above already provide the key algebraic properties.
-/

/-! ### Local Boolean-algebra hom structure for `PowQuot` -/

/-- Boolean algebra homomorphism (local to this project).
It's the minimal structure you need: preserves `⊓`, `⊔`, `ᶜ`, `⊥`, `⊤`. -/
structure BAHom (α β) [BooleanAlgebra α] [BooleanAlgebra β] :=
  (toFun     : α → β)
  (map_inf'  : ∀ x y, toFun (x ⊓ y) = toFun x ⊓ toFun y)
  (map_sup'  : ∀ x y, toFun (x ⊔ y) = toFun x ⊔ toFun y)
  (map_compl': ∀ x,   toFun (xᶜ)    = (toFun x)ᶜ)
  (map_bot'  :        toFun ⊥        = ⊥)
  (map_top'  :        toFun ⊤        = ⊤)

namespace BAHom

variable {α β γ : Type*} [BooleanAlgebra α] [BooleanAlgebra β] [BooleanAlgebra γ]

instance : CoeFun (BAHom α β) (fun _ => α → β) where
  coe f := f.toFun

@[simp] lemma map_inf (f : BAHom α β) (x y : α) : f (x ⊓ y) = f x ⊓ f y := f.map_inf' x y
@[simp] lemma map_sup (f : BAHom α β) (x y : α) : f (x ⊔ y) = f x ⊔ f y := f.map_sup' x y
@[simp] lemma map_compl (f : BAHom α β) (x : α) : f (xᶜ) = (f x)ᶜ := f.map_compl' x
@[simp] lemma map_bot (f : BAHom α β) : f ⊥ = (⊥ : β) := f.map_bot'
@[simp] lemma map_top (f : BAHom α β) : f ⊤ = (⊤ : β) := f.map_top'

/-- Identity BA hom. -/
def id : BAHom α α where
  toFun := fun x => x
  map_inf' := fun x y => rfl
  map_sup' := fun x y => rfl
  map_compl' := fun x => rfl
  map_bot' := rfl
  map_top' := rfl

@[simp] lemma id_apply (x : α) : (BAHom.id : BAHom α α) x = x := rfl

/-- Composition of BA homs. -/
def comp (g : BAHom β γ) (f : BAHom α β) : BAHom α γ where
  toFun := fun x => g (f x)
  map_inf' := by intro x y; simp
  map_sup' := by intro x y; simp
  map_compl' := by intro x; simp
  map_bot' := by simp
  map_top' := by simp

@[simp] lemma comp_apply (g : BAHom β γ) (f : BAHom α β) (x : α) :
  (g.comp f) x = g (f x) := rfl

@[ext] lemma ext {f g : BAHom α β} (h : ∀ x, f x = g x) : f = g := by
  cases f; cases g; congr; ext x; exact h x

end BAHom

/-- Package your `mapOfLe` into a `BAHom` without extra imports. -/
def PowQuot.mapOfLeBAHom
  {𝓘 𝓙 : BoolIdeal}
  (h : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem) : BAHom (PowQuot 𝓘) (PowQuot 𝓙) where
  toFun      := PowQuot.mapOfLe h
  map_inf'   := PowQuot.mapOfLe_inf h
  map_sup'   := PowQuot.mapOfLe_sup h
  map_compl' := PowQuot.mapOfLe_compl h
  map_bot'   := PowQuot.mapOfLe_bot h
  map_top'   := PowQuot.mapOfLe_top h

@[simp] lemma PowQuot.mapOfLeBAHom_apply_mk
  {𝓘 𝓙 : BoolIdeal} (h : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem) (A : Set ℕ) :
  PowQuot.mapOfLeBAHom h (PowQuot.mk 𝓘 A) = PowQuot.mk 𝓙 A := rfl

/-- Functoriality (composition) in the obvious way. -/
@[simp] lemma PowQuot.mapOfLeBAHom_comp
  {𝓘 𝓙 𝓚 : BoolIdeal}
  (h₁ : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem)
  (h₂ : ∀ S, S ∈ 𝓙.mem → S ∈ 𝓚.mem) :
  (BAHom.comp (PowQuot.mapOfLeBAHom h₂) (PowQuot.mapOfLeBAHom h₁))
  = PowQuot.mapOfLeBAHom (fun S hS => h₂ S (h₁ S hS)) := by
  ext x
  induction x using Quot.inductionOn with | _ A =>
  rfl

@[simp] lemma PowQuot.mapOfLeBAHom_id {𝓘 : BoolIdeal} :
  PowQuot.mapOfLeBAHom (fun _ h => h) = (BAHom.id : BAHom (PowQuot 𝓘) (PowQuot 𝓘)) := by
  ext x
  induction x using Quot.inductionOn with | _ A =>
  rfl

@[simp] lemma PowQuot.mapOfLeBAHom_monotone
  {𝓘 𝓙 : BoolIdeal} (h : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem) :
  Monotone (PowQuot.mapOfLeBAHom h) :=
  PowQuot.mapOfLe_monotone h

/-! ### EqvGen → relation bridge for equality lemmas -/

section EqvGenBridge

open Relation

/-- For an equivalence relation `r`, its equivalence closure `EqvGen r` is just `r`. -/
lemma eqvGen_iff_of_equivalence {α : Type*} {r : α → α → Prop}
    (hr : Equivalence r) {a b : α} :
  EqvGen r a b ↔ r a b := by
  constructor
  · intro h
    induction h with
    | rel _ _ h => exact h
    | refl a => exact hr.refl a
    | symm _ _ _ ih => exact hr.symm ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact hr.trans ih₁ ih₂
  · intro h; exact EqvGen.rel _ _ h

/-- Equality on representatives reduces to "small" symmetric difference. -/
@[simp] lemma mk_eq_mk_iff (𝓘 : BoolIdeal) (A B : Set ℕ) :
  (PowQuot.mk 𝓘 A : PowQuot 𝓘) = PowQuot.mk 𝓘 B ↔
  (A △ B) ∈ 𝓘.mem := by
  -- Unfold to get Quot.mk equality
  show Quot.mk (sdiffSetoid 𝓘) A = Quot.mk (sdiffSetoid 𝓘) B ↔ _
  -- Quot.eq yields EqvGen of the underlying relation; fold it back
  rw [Quot.eq]
  rw [eqvGen_iff_of_equivalence (sdiffSetoid 𝓘).iseqv]
  rfl

/-- Symmetric rewrite lemma that's sometimes handier than the ↔ form. -/
@[simp] lemma mk_eq_mk (𝓘 : BoolIdeal) (A B : Set ℕ) (h : (A △ B) ∈ 𝓘.mem) :
  (PowQuot.mk 𝓘 A : PowQuot 𝓘) = PowQuot.mk 𝓘 B :=
  (mk_eq_mk_iff 𝓘 A B).mpr h

end EqvGenBridge

/-- Mapped equality convenience lemma. -/
@[simp] lemma mapOfLe_mk_eq_iff
  {𝓘 𝓙 : BoolIdeal}
  (h : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem)
  (A B : Set ℕ) :
  PowQuot.mapOfLe h (PowQuot.mk 𝓘 A) = PowQuot.mapOfLe h (PowQuot.mk 𝓘 B)
    ↔ (A △ B) ∈ 𝓙.mem := by
  simp [PowQuot.mapOfLe_mk, mk_eq_mk_iff]

/-! ### Additional convenience lemmas -/

section Convenience

variable {𝓘 : BoolIdeal}

/-- Alias for set difference that reads naturally. -/
@[simp] lemma mk_diff_mk (A B : Set ℕ) :
  PowQuot.mk 𝓘 A \ PowQuot.mk 𝓘 B = PowQuot.mk 𝓘 (A \ B) := by
  rw [PowQuot.mk_sdiff_mk, Set.diff_eq]

/-- Set-first phrasing for intersection. -/
@[simp] lemma mk_inter_mk (A B : Set ℕ) :
  PowQuot.mk 𝓘 A ⊓ PowQuot.mk 𝓘 B = PowQuot.mk 𝓘 (A ∩ B) :=
  rfl

/-- Set-first phrasing for union. -/
@[simp] lemma mk_union_mk (A B : Set ℕ) :
  PowQuot.mk 𝓘 A ⊔ PowQuot.mk 𝓘 B = PowQuot.mk 𝓘 (A ∪ B) :=
  rfl

-- Not a simp-lemma globally; use explicitly when needed.
lemma compl_eq_univ_sdiff {α : Type*} (A : Set α) : Aᶜ = Set.univ \ A := by
  ext x; simp

end Convenience

section MoreOrderLemmas
variable {𝓘 : BoolIdeal}

/-- `mk A ≤ (mk B)ᶜ` iff the intersection is small. -/
@[simp] lemma mk_le_compl_mk (A B : Set ℕ) :
  (PowQuot.mk 𝓘 A : PowQuot 𝓘) ≤ (PowQuot.mk 𝓘 B)ᶜ ↔
  (A ∩ B) ∈ 𝓘.mem := by
  -- Right side: `(A ∩ B) ∈ 𝓘.mem`
  -- Left side: `mk A ≤ mk Bᶜ` reduces to `(A \ Bᶜ) ∈ 𝓘.mem`
  -- and `A \ Bᶜ = A ∩ B`.
  simp [mk_le_mk, mk_compl, Set.diff_eq]

/-- `(mk A)ᶜ ≤ mk B` iff the co-intersection is small. -/
@[simp] lemma compl_mk_le_mk_iff (A B : Set ℕ) :
    ((PowQuot.mk 𝓘 A)ᶜ ≤ PowQuot.mk 𝓘 B) ↔ (Aᶜ ∩ Bᶜ) ∈ 𝓘.mem := by
  -- same pattern as the mapped lemma, but without mapOfLe
  simpa [mk_compl, mk_le_mk, Set.diff_eq, Set.inter_comm]
    using (compl_le_iff_compl_le :
      ((PowQuot.mk 𝓘 A)ᶜ ≤ PowQuot.mk 𝓘 B) ↔ ((PowQuot.mk 𝓘 B)ᶜ ≤ PowQuot.mk 𝓘 A))

/-- Negative form: `¬ ((mk A)ᶜ ≤ mk B)` iff the co-intersection is not small. -/
@[simp] lemma compl_mk_not_le_mk_iff (A B : Set ℕ) :
  ¬ ((PowQuot.mk 𝓘 A)ᶜ ≤ PowQuot.mk 𝓘 B) ↔ (Aᶜ ∩ Bᶜ) ∉ 𝓘.mem := by
  simpa using (not_congr (compl_mk_le_mk_iff (𝓘 := 𝓘) A B))

end MoreOrderLemmas

/-! ### Thresholds: When quotient elements equal ⊥ or ⊤
This section characterizes when quotient elements reach the Boolean algebra bounds.
Key insight: `mk A = ⊥` precisely when A itself is small (in the ideal),
and `mk A = ⊤` when the complement Aᶜ is small. -/
section TopBotIff
  variable {𝓘 : BoolIdeal}

  /-- `mk A = ⊥` iff `A` is small. -/
  @[simp] lemma mk_eq_bot_iff (A : Set ℕ) :
      (PowQuot.mk 𝓘 A : PowQuot 𝓘) = ⊥ ↔ A ∈ 𝓘.mem := by
    constructor
    · intro h
      have : (PowQuot.mk 𝓘 A : PowQuot 𝓘) ≤ ⊥ := by simp [h]
      simpa [mk_bot, mk_le_mk, Set.diff_empty] using this
    · intro hA
      apply le_antisymm
      · -- `mk A ≤ ⊥`
        simpa [mk_bot, mk_le_mk, Set.diff_empty] using hA
      · -- `⊥ ≤ mk A` since `∅ \ A = ∅ ∈ 𝓘.mem`
        have : (∅ : Set ℕ) ∈ 𝓘.mem := 𝓘.empty_mem
        simpa [mk_bot, mk_le_mk, Set.empty_diff]

  /-- `mk A = ⊤` iff `Aᶜ` is small. -/
  @[simp] lemma mk_eq_top_iff (A : Set ℕ) :
      (PowQuot.mk 𝓘 A : PowQuot 𝓘) = ⊤ ↔ Aᶜ ∈ 𝓘.mem := by
    constructor
    · intro h
      have : ⊤ ≤ (PowQuot.mk 𝓘 A : PowQuot 𝓘) := by simp [h]
      simp [mk_top, mk_le_mk] at this
      -- this : Set.univ \ A ∈ 𝓘.mem
      -- Need to show Aᶜ ∈ 𝓘.mem, and Aᶜ = Set.univ \ A
      convert this
      ext x
      simp
    · intro hAc
      apply le_antisymm
      · exact le_top
      · -- `⊤ ≤ mk A` ↔ `(univ \ A) ∈ 𝓘.mem`
        simp [mk_top, mk_le_mk]
        -- Need to show Set.univ \ A ∈ 𝓘.mem, given hAc : Aᶜ ∈ 𝓘.mem
        convert hAc
        ext x
        simp
end TopBotIff

/-! ### Negative singletons: `mk` vs. `⊥/⊤` -/
section TopBotNeg
  variable {𝓘 : BoolIdeal}

  @[simp] lemma mk_ne_bot_iff (A : Set ℕ) :
      ((PowQuot.mk 𝓘 A : PowQuot 𝓘) ≠ ⊥) ↔ A ∉ 𝓘.mem := by
    simpa using (not_congr (mk_eq_bot_iff (𝓘 := 𝓘) A))

  @[simp] lemma mk_ne_top_iff (A : Set ℕ) :
      ((PowQuot.mk 𝓘 A : PowQuot 𝓘) ≠ ⊤) ↔ Aᶜ ∉ 𝓘.mem := by
    simpa using (not_congr (mk_eq_top_iff (𝓘 := 𝓘) A))
end TopBotNeg

/-! ### ⊥/⊤ endpoints for left complements (domain) -/
section MoreTopBotLeft
  variable {𝓘 : BoolIdeal} (A : Set ℕ)

  @[simp] lemma compl_mk_eq_bot_iff :
      ((PowQuot.mk 𝓘 A)ᶜ = (⊥ : PowQuot 𝓘)) ↔ Aᶜ ∈ 𝓘.mem := by
    simpa [mk_compl] using (mk_eq_bot_iff (𝓘 := 𝓘) Aᶜ)

  @[simp] lemma compl_mk_eq_top_iff :
      ((PowQuot.mk 𝓘 A)ᶜ = (⊤ : PowQuot 𝓘)) ↔ A ∈ 𝓘.mem := by
    simpa [mk_compl] using (mk_eq_top_iff (𝓘 := 𝓘) Aᶜ)

  @[simp] lemma compl_mk_ne_bot_iff :
      ((PowQuot.mk 𝓘 A)ᶜ ≠ (⊥ : PowQuot 𝓘)) ↔ Aᶜ ∉ 𝓘.mem := by
    simpa using (not_congr (compl_mk_eq_bot_iff (𝓘 := 𝓘) A))

  @[simp] lemma compl_mk_ne_top_iff :
      ((PowQuot.mk 𝓘 A)ᶜ ≠ (⊤ : PowQuot 𝓘)) ↔ A ∉ 𝓘.mem := by
    simpa using (not_congr (compl_mk_eq_top_iff (𝓘 := 𝓘) A))
end MoreTopBotLeft

section InfSupThresholds
  variable {𝓘 : BoolIdeal}

  /-- `mk A ⊓ mk B = ⊥` iff `A ∩ B` is small. -/
  @[simp] lemma mk_inf_eq_bot_iff (A B : Set ℕ) :
      PowQuot.mk 𝓘 A ⊓ PowQuot.mk 𝓘 B = ⊥ ↔ (A ∩ B) ∈ 𝓘.mem := by
    simpa [mk_inf_mk] using mk_eq_bot_iff (A ∩ B)

  /-- `mk A ⊔ mk B = ⊤` iff `Aᶜ ∩ Bᶜ` is small (i.e. complement of the union is small). -/
  @[simp] lemma mk_sup_eq_top_iff (A B : Set ℕ) :
      PowQuot.mk 𝓘 A ⊔ PowQuot.mk 𝓘 B = ⊤ ↔ (Aᶜ ∩ Bᶜ) ∈ 𝓘.mem := by
    rw [mk_sup_mk, mk_eq_top_iff]
    simp [Set.compl_union]
end InfSupThresholds

/-! ### Non-thresholds: Negative forms of threshold lemmas
These are the negative (≠) versions of the threshold characterizations.
Useful when goals contain inequalities rather than equalities. -/
section NonThresholds
  variable {𝓘 : BoolIdeal}

  @[simp] lemma mk_inf_ne_bot_iff (A B : Set ℕ) :
      (PowQuot.mk 𝓘 A ⊓ PowQuot.mk 𝓘 B ≠ (⊥ : PowQuot 𝓘)) ↔
      (A ∩ B) ∉ 𝓘.mem := by
    -- negating your `mk_inf_eq_bot_iff`
    have := mk_inf_eq_bot_iff (𝓘 := 𝓘) A B
    simpa using (not_congr this)

  @[simp] lemma mk_sup_ne_top_iff (A B : Set ℕ) :
      (PowQuot.mk 𝓘 A ⊔ PowQuot.mk 𝓘 B ≠ (⊤ : PowQuot 𝓘)) ↔
      (Aᶜ ∩ Bᶜ) ∉ 𝓘.mem := by
    -- negating your `mk_sup_eq_top_iff`
    have := mk_sup_eq_top_iff (𝓘 := 𝓘) A B
    simpa using (not_congr this)
end NonThresholds

/-! ### MapOfLe order/equality lemmas -/
section MapOfLeOrder
  variable {𝓘 𝓙 : BoolIdeal}

  /-- Inequality between mapped reps reduces to smallness in the target ideal. -/
  @[simp] lemma mapOfLe_mk_le_mk_iff
    (h : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem) (A B : Set ℕ) :
    PowQuot.mapOfLe h (PowQuot.mk 𝓘 A) ≤
      PowQuot.mapOfLe h (PowQuot.mk 𝓘 B) ↔
    (A \ B) ∈ 𝓙.mem := by
    simpa [PowQuot.mapOfLe_mk, mk_le_mk]

  /-- Bottom/top tests after mapping, reduced to smallness in the target ideal. -/
  @[simp] lemma mapOfLe_mk_eq_bot_iff
    (h : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem) (A : Set ℕ) :
    PowQuot.mapOfLe h (PowQuot.mk 𝓘 A) = ⊥ ↔ A ∈ 𝓙.mem := by
    simpa [PowQuot.mapOfLe_mk] using (mk_eq_bot_iff (𝓘 := 𝓙) A)

  @[simp] lemma mapOfLe_mk_eq_top_iff
    (h : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem) (A : Set ℕ) :
    PowQuot.mapOfLe h (PowQuot.mk 𝓘 A) = ⊤ ↔ Aᶜ ∈ 𝓙.mem := by
    simpa [PowQuot.mapOfLe_mk] using (mk_eq_top_iff (𝓘 := 𝓙) A)
end MapOfLeOrder

/-! ### Thresholds for images under `mapOfLe` -/
section MapThresholds
  variable {𝓘 𝓙 : BoolIdeal}

  @[simp] lemma mapOfLe_inf_eq_bot_iff
      (h : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem) (A B : Set ℕ) :
      (PowQuot.mapOfLe h (PowQuot.mk 𝓘 A) ⊓
       PowQuot.mapOfLe h (PowQuot.mk 𝓘 B)) = (⊥ : PowQuot 𝓙)
      ↔ (A ∩ B) ∈ 𝓙.mem := by
    simpa [PowQuot.mapOfLe_inf, PowQuot.mapOfLe_mk]
      using (mk_inf_eq_bot_iff (𝓘 := 𝓙) A B)

  @[simp] lemma mapOfLe_sup_eq_top_iff
      (h : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem) (A B : Set ℕ) :
      (PowQuot.mapOfLe h (PowQuot.mk 𝓘 A) ⊔
       PowQuot.mapOfLe h (PowQuot.mk 𝓘 B)) = (⊤ : PowQuot 𝓙)
      ↔ (Aᶜ ∩ Bᶜ) ∈ 𝓙.mem := by
    simpa [PowQuot.mapOfLe_sup, PowQuot.mapOfLe_mk]
      using (mk_sup_eq_top_iff (𝓘 := 𝓙) A B)
end MapThresholds

/-! ### Negative singletons: images under `mapOfLe` -/
section MapTopBotNeg
  variable {𝓘 𝓙 : BoolIdeal}
  variable (h : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem)

  @[simp] lemma mapOfLe_mk_ne_bot_iff (A : Set ℕ) :
      (PowQuot.mapOfLe h (PowQuot.mk 𝓘 A) ≠ (⊥ : PowQuot 𝓙)) ↔ A ∉ 𝓙.mem := by
    simpa [PowQuot.mapOfLe_mk] using (not_congr (mk_eq_bot_iff (𝓘 := 𝓙) A))

  @[simp] lemma mapOfLe_mk_ne_top_iff (A : Set ℕ) :
      (PowQuot.mapOfLe h (PowQuot.mk 𝓘 A) ≠ (⊤ : PowQuot 𝓙)) ↔ Aᶜ ∉ 𝓙.mem := by
    simpa [PowQuot.mapOfLe_mk] using (not_congr (mk_eq_top_iff (𝓘 := 𝓙) A))
end MapTopBotNeg

/-! ### Non-thresholds for images under `mapOfLe` -/
section MapNonThresholds
  variable {𝓘 𝓙 : BoolIdeal}

  @[simp] lemma mapOfLe_inf_ne_bot_iff
      (h : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem) (A B : Set ℕ) :
      (PowQuot.mapOfLe h (PowQuot.mk 𝓘 A) ⊓
       PowQuot.mapOfLe h (PowQuot.mk 𝓘 B)) ≠ (⊥ : PowQuot 𝓙)
      ↔ (A ∩ B) ∉ 𝓙.mem := by
    have := mapOfLe_inf_eq_bot_iff (𝓘 := 𝓘) (𝓙 := 𝓙) h A B
    simpa using (not_congr this)

  @[simp] lemma mapOfLe_sup_ne_top_iff
      (h : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem) (A B : Set ℕ) :
      (PowQuot.mapOfLe h (PowQuot.mk 𝓘 A) ⊔
       PowQuot.mapOfLe h (PowQuot.mk 𝓘 B)) ≠ (⊤ : PowQuot 𝓙)
      ↔ (Aᶜ ∩ Bᶜ) ∉ 𝓙.mem := by
    have := mapOfLe_sup_eq_top_iff (𝓘 := 𝓘) (𝓙 := 𝓙) h A B
    simpa using (not_congr this)
end MapNonThresholds

/-! ### ⊥/⊤ endpoints for left complements (mapped) -/
section MapTopBotLeft
  variable {𝓘 𝓙 : BoolIdeal}
  variable (h : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem) (A : Set ℕ)

  @[simp] lemma mapOfLe_compl_mk_eq_bot_iff :
      ((PowQuot.mapOfLe h (PowQuot.mk 𝓘 A))ᶜ = (⊥ : PowQuot 𝓙)) ↔ Aᶜ ∈ 𝓙.mem := by
    simpa [PowQuot.mapOfLe_mk, PowQuot.mapOfLe_compl, mk_compl]
      using (mk_eq_bot_iff (𝓘 := 𝓙) Aᶜ)

  @[simp] lemma mapOfLe_compl_mk_eq_top_iff :
      ((PowQuot.mapOfLe h (PowQuot.mk 𝓘 A))ᶜ = (⊤ : PowQuot 𝓙)) ↔ A ∈ 𝓙.mem := by
    simpa [PowQuot.mapOfLe_mk, PowQuot.mapOfLe_compl, mk_compl]
      using (mk_eq_top_iff (𝓘 := 𝓙) Aᶜ)

  @[simp] lemma mapOfLe_compl_mk_ne_bot_iff :
      ((PowQuot.mapOfLe h (PowQuot.mk 𝓘 A))ᶜ ≠ (⊥ : PowQuot 𝓙)) ↔ Aᶜ ∉ 𝓙.mem := by
    simpa using (not_congr (mapOfLe_compl_mk_eq_bot_iff (𝓘 := 𝓘) (𝓙 := 𝓙) h A))

  @[simp] lemma mapOfLe_compl_mk_ne_top_iff :
      ((PowQuot.mapOfLe h (PowQuot.mk 𝓘 A))ᶜ ≠ (⊤ : PowQuot 𝓙)) ↔ A ∉ 𝓙.mem := by
    simpa using (not_congr (mapOfLe_compl_mk_eq_top_iff (𝓘 := 𝓘) (𝓙 := 𝓙) h A))
end MapTopBotLeft

/-! ### Small helpers -/
section SmallHelpers
  variable {A B : Set ℕ}

  /-- If `A ⊆ B` then `A △ B = B \ A`. -/
  lemma symmDiff_eq_diff_of_subset (hAB : A ⊆ B) : A △ B = B \ A := by
    ext x; constructor
    · intro hx
      rcases hx with ⟨hA, hB⟩ | ⟨hB, hA⟩
      · exact (False.elim (hB (hAB hA)))
      · exact ⟨hB, hA⟩
    · rintro ⟨hB, hA⟩
      exact Or.inr ⟨hB, hA⟩

  /-- If `B ⊆ A` then `A △ B = A \ B`. -/
  lemma symmDiff_eq_diff_of_superset (hBA : B ⊆ A) : A △ B = A \ B := by
    ext x; constructor
    · intro hx
      rcases hx with ⟨hA, hB⟩ | ⟨hB, hA⟩
      · exact ⟨hA, hB⟩
      · exact (False.elim (hA (hBA hB)))
    · intro hx
      exact Or.inl hx
end SmallHelpers

/-! ### Subset to order -/
section SubsetToOrder
  variable {𝓘 : BoolIdeal} {A B : Set ℕ}

  lemma mk_le_mk_of_subset (hAB : A ⊆ B) :
      (PowQuot.mk 𝓘 A : PowQuot 𝓘) ≤ PowQuot.mk 𝓘 B := by
    -- `A \ B = ∅`, and `∅ ∈ 𝓘.mem`.
    rw [mk_le_mk]
    convert 𝓘.empty_mem
    exact Set.diff_eq_empty.mpr hAB
end SubsetToOrder

/-! ### `mk` is monotone in the set argument -/
section MkMonotone
  variable {𝓘 : BoolIdeal}

  /-- `mk` is monotone: from `A ⊆ B` we get `mk A ≤ mk B`. -/
  lemma mk_monotone : Monotone (fun A : Set ℕ => (PowQuot.mk 𝓘 A : PowQuot 𝓘)) := by
    intro A B hAB
    exact (mk_le_mk_of_subset (𝓘 := 𝓘) (A := A) (B := B) hAB)

  attribute [mono] mk_monotone
end MkMonotone

/-! ### Strict order: Characterizing < in terms of sets
The strict order x < y requires both x ≤ y (A \ B small) and x ≠ y (A △ B not small).
This captures the idea that A is "strictly below" B in the quotient. -/
section StrictOrder
  variable {𝓘 : BoolIdeal}

  -- Strict inequality iff `A \ B` is small but we do not have mk-equality
  lemma mk_lt_mk_iff (A B : Set ℕ) :
      (PowQuot.mk 𝓘 A : PowQuot 𝓘) < PowQuot.mk 𝓘 B
      ↔ ((A \ B) ∈ 𝓘.mem ∧ (A △ B) ∉ 𝓘.mem) := by
    constructor
    · intro h
      have hle : (PowQuot.mk 𝓘 A) ≤ (PowQuot.mk 𝓘 B) := le_of_lt h
      have hneq : (PowQuot.mk 𝓘 A) ≠ (PowQuot.mk 𝓘 B) := ne_of_lt h
      have hAB : (A \ B) ∈ 𝓘.mem := by simpa [mk_le_mk] using hle
      have hΔ : (A △ B) ∉ 𝓘.mem := by
        -- If it were small then mk A = mk B by `mk_eq_mk_iff`.
        -- Contradict `hneq`.
        intro hsmall
        have : (PowQuot.mk 𝓘 A) = (PowQuot.mk 𝓘 B) :=
          (mk_eq_mk_iff (𝓘 := 𝓘) A B).mpr hsmall
        exact hneq this
      exact ⟨hAB, hΔ⟩
    · intro ⟨hAB, hΔ⟩
      have hle : (PowQuot.mk 𝓘 A) ≤ (PowQuot.mk 𝓘 B) := by
        simpa [mk_le_mk] using hAB
      have hneq : (PowQuot.mk 𝓘 A) ≠ (PowQuot.mk 𝓘 B) := by
        intro hEq
        have : (A △ B) ∈ 𝓘.mem :=
          (mk_eq_mk_iff (𝓘 := 𝓘) A B).mp hEq
        exact hΔ this
      exact lt_of_le_of_ne hle hneq
end StrictOrder

/-! ### Strict order under `mapOfLe` -/
section MapStrictOrder
  variable {𝓘 𝓙 : BoolIdeal}

  @[simp] lemma mapOfLe_mk_lt_mk_iff
      (h : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem) (A B : Set ℕ) :
      PowQuot.mapOfLe h (PowQuot.mk 𝓘 A)
        < PowQuot.mapOfLe h (PowQuot.mk 𝓘 B)
      ↔ ((A \ B) ∈ 𝓙.mem ∧ (A △ B) ∉ 𝓙.mem) := by
    constructor
    · intro hlt
      have hle : PowQuot.mapOfLe h (PowQuot.mk 𝓘 A)
                ≤ PowQuot.mapOfLe h (PowQuot.mk 𝓘 B) := le_of_lt hlt
      have hneq : PowQuot.mapOfLe h (PowQuot.mk 𝓘 A)
                ≠ PowQuot.mapOfLe h (PowQuot.mk 𝓘 B) := ne_of_lt hlt
      have hAB : (A \ B) ∈ 𝓙.mem := by
        simpa [PowQuot.mapOfLe_mk, mk_le_mk] using hle
      have hΔ : (A △ B) ∉ 𝓙.mem := by
        intro hsmall
        have : PowQuot.mapOfLe h (PowQuot.mk 𝓘 A)
              = PowQuot.mapOfLe h (PowQuot.mk 𝓘 B) :=
          (mapOfLe_mk_eq_iff (𝓘 := 𝓘) (𝓙 := 𝓙) h A B).mpr hsmall
        exact hneq this
      exact ⟨hAB, hΔ⟩
    · intro ⟨hAB, hΔ⟩
      have hle : PowQuot.mapOfLe h (PowQuot.mk 𝓘 A)
              ≤ PowQuot.mapOfLe h (PowQuot.mk 𝓘 B) := by
        simpa [PowQuot.mapOfLe_mk, mk_le_mk] using hAB
      have hneq : PowQuot.mapOfLe h (PowQuot.mk 𝓘 A)
                ≠ PowQuot.mapOfLe h (PowQuot.mk 𝓘 B) := by
        intro hEq
        have : (A △ B) ∈ 𝓙.mem :=
          (mapOfLe_mk_eq_iff (𝓘 := 𝓘) (𝓙 := 𝓙) h A B).mp hEq
        exact hΔ this
      exact lt_of_le_of_ne hle hneq
end MapStrictOrder

/-! ### Subset → order/strict order in the image -/
section MapSubsetToOrder
  variable {𝓘 𝓙 : BoolIdeal} {A B : Set ℕ}
  variable (h : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem)

  /-- If `A ⊆ B` then `mapOfLe h (mk A) ≤ mapOfLe h (mk B)`. -/
  lemma mapOfLe_mk_le_mk_of_subset (hAB : A ⊆ B) :
      PowQuot.mapOfLe h (PowQuot.mk 𝓘 A) ≤ PowQuot.mapOfLe h (PowQuot.mk 𝓘 B) := by
    -- `(A \ B) = ∅`, and `∅ ∈ 𝓙.mem`.
    simpa [PowQuot.mapOfLe_mk, mk_le_mk] using
      (show (A \ B) ∈ 𝓙.mem from by
        simpa [Set.diff_eq_empty.mpr hAB] using (𝓙.empty_mem))

  /-- Strict order from a subset when the "gap" is not small in the target ideal. -/
  lemma mapOfLe_mk_lt_mk_of_subset_not_small
      (hAB : A ⊆ B) (hGap : (B \ A) ∉ 𝓙.mem) :
      PowQuot.mapOfLe h (PowQuot.mk 𝓘 A) < PowQuot.mapOfLe h (PowQuot.mk 𝓘 B) := by
    classical
    have h₁ : (A \ B) ∈ 𝓙.mem := by
      simpa [Set.diff_eq_empty.mpr hAB] using (𝓙.empty_mem)
    have : (A △ B) = (B \ A) := symmDiff_eq_diff_of_subset hAB
    exact (mapOfLe_mk_lt_mk_iff (𝓘 := 𝓘) (𝓙 := 𝓙) h A B).2 ⟨h₁, by simpa [this] using hGap⟩
end MapSubsetToOrder

/-! ### Order to smallness, mapped: `x ≤ (y)ᶜ` -/
section MapOrderToSmallness
  variable {𝓘 𝓙 : BoolIdeal}
  variable (h : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem)

  @[simp] lemma mapOfLe_mk_le_compl_mk_iff (A B : Set ℕ) :
      PowQuot.mapOfLe h (PowQuot.mk 𝓘 A)
        ≤ (PowQuot.mapOfLe h (PowQuot.mk 𝓘 B))ᶜ
      ↔ (A ∩ B) ∈ 𝓙.mem := by
    simpa [PowQuot.mapOfLe_mk, mk_le_compl_mk]
end MapOrderToSmallness

/-! ### Order to smallness, mapped (complement on the left) -/
section MapOrderToSmallnessLeft
  variable {𝓘 𝓙 : BoolIdeal}
  variable (h : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem)

  @[simp] lemma mapOfLe_compl_mk_le_mk_iff (A B : Set ℕ) :
      ((PowQuot.mapOfLe h (PowQuot.mk 𝓘 A))ᶜ
         ≤ PowQuot.mapOfLe h (PowQuot.mk 𝓘 B))
      ↔ (Aᶜ ∩ Bᶜ) ∈ 𝓙.mem := by
    -- use xᶜ ≤ y ↔ yᶜ ≤ x, then reduce to mk_le_mk on the target side
    simpa [PowQuot.mapOfLe_compl, PowQuot.mapOfLe_mk, mk_compl, mk_le_mk,
           Set.diff_eq, Set.inter_comm]
      using (compl_le_iff_compl_le :
        ((PowQuot.mapOfLe h (PowQuot.mk 𝓘 A))ᶜ ≤ PowQuot.mapOfLe h (PowQuot.mk 𝓘 B))
          ↔ ((PowQuot.mapOfLe h (PowQuot.mk 𝓘 B))ᶜ ≤ PowQuot.mapOfLe h (PowQuot.mk 𝓘 A)))

  /-- Negative form: `¬ ((mapOfLe h (mk A))ᶜ ≤ mapOfLe h (mk B))` iff co-intersection not small. -/
  @[simp] lemma mapOfLe_compl_mk_not_le_mk_iff (A B : Set ℕ) :
    ¬ ((PowQuot.mapOfLe h (PowQuot.mk 𝓘 A))ᶜ ≤ PowQuot.mapOfLe h (PowQuot.mk 𝓘 B)) 
    ↔ (Aᶜ ∩ Bᶜ) ∉ 𝓙.mem := by
    simpa using (not_congr (mapOfLe_compl_mk_le_mk_iff (𝓘 := 𝓘) (𝓙 := 𝓙) h A B))

end MapOrderToSmallnessLeft

/-! ### Disjointness / complements, reduced to smallness -/
section DisjointCompl
  variable {𝓘 : BoolIdeal}

  /-- Disjointness of representatives corresponds to a small intersection. -/
  @[simp] lemma disjoint_mk_iff (A B : Set ℕ) :
      Disjoint (PowQuot.mk 𝓘 A : PowQuot 𝓘) (PowQuot.mk 𝓘 B) ↔
      (A ∩ B) ∈ 𝓘.mem := by
    -- In a Boolean algebra: `Disjoint x y ↔ x ⊓ y = ⊥`.
    -- Then apply your `mk_inf_eq_bot_iff`.
    simpa [disjoint_iff, mk_inf_mk] using
      (mk_inf_eq_bot_iff (A := A) (B := B))

  /-- Complementarity of representatives corresponds to "disjoint & covers ⊤". -/
  @[simp] lemma isCompl_mk_iff (A B : Set ℕ) :
      IsCompl (PowQuot.mk 𝓘 A : PowQuot 𝓘) (PowQuot.mk 𝓘 B) ↔
      ((A ∩ B) ∈ 𝓘.mem ∧ (Aᶜ ∩ Bᶜ) ∈ 𝓘.mem) := by
    -- In a Boolean algebra: `IsCompl x y ↔ x ⊓ y = ⊥ ∧ x ⊔ y = ⊤`.
    -- Use your `mk_inf_eq_bot_iff` and `mk_sup_eq_top_iff`.
    simp only [isCompl_iff, mk_inf_mk, mk_sup_mk, disjoint_iff, codisjoint_iff]
    exact ⟨fun ⟨h1, h2⟩ => ⟨mk_inf_eq_bot_iff A B |>.mp h1, mk_sup_eq_top_iff A B |>.mp h2⟩,
           fun ⟨h1, h2⟩ => ⟨mk_inf_eq_bot_iff A B |>.mpr h1, mk_sup_eq_top_iff A B |>.mpr h2⟩⟩
end DisjointCompl

/-! ### Disjointness/complements transported along `mapOfLe` -/
section MapOfLe_DisjointCompl
  variable {𝓘 𝓙 : BoolIdeal}
  variable (h : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem)

  @[simp] lemma mapOfLe_disjoint_iff (A B : Set ℕ) :
      Disjoint (PowQuot.mapOfLe h (PowQuot.mk 𝓘 A))
               (PowQuot.mapOfLe h (PowQuot.mk 𝓘 B)) ↔
      (A ∩ B) ∈ 𝓙.mem := by
    -- Reduce to `inf = ⊥`, push `mapOfLe` through, then apply the threshold.
    simpa [disjoint_iff, PowQuot.mapOfLe_inf, PowQuot.mapOfLe_mk]
      using (mk_inf_eq_bot_iff (𝓘 := 𝓙) (A := A) (B := B))

  @[simp] lemma mapOfLe_isCompl_iff (A B : Set ℕ) :
      IsCompl (PowQuot.mapOfLe h (PowQuot.mk 𝓘 A))
              (PowQuot.mapOfLe h (PowQuot.mk 𝓘 B)) ↔
      ((A ∩ B) ∈ 𝓙.mem ∧ (Aᶜ ∩ Bᶜ) ∈ 𝓙.mem) := by
    -- Reduce to `(inf = ⊥) ∧ (sup = ⊤)`, push through `mapOfLe`, then use thresholds.
    simp only [isCompl_iff, PowQuot.mapOfLe_inf, PowQuot.mapOfLe_sup, PowQuot.mapOfLe_mk,
               disjoint_iff, codisjoint_iff]
    exact ⟨fun ⟨h1, h2⟩ => ⟨mk_inf_eq_bot_iff A B |>.mp h1, mk_sup_eq_top_iff A B |>.mp h2⟩,
           fun ⟨h1, h2⟩ => ⟨mk_inf_eq_bot_iff A B |>.mpr h1, mk_sup_eq_top_iff A B |>.mpr h2⟩⟩
  
  /-- `mapOfLe` preserves disjointness (monotone direction). -/
  lemma mapOfLe_preserves_disjoint
    {𝓘 𝓙 : BoolIdeal} (h : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem)
    (A B : Set ℕ) :
    Disjoint (PowQuot.mk 𝓘 A : PowQuot 𝓘) (PowQuot.mk 𝓘 B) →
    Disjoint (PowQuot.mapOfLe h (PowQuot.mk 𝓘 A))
             (PowQuot.mapOfLe h (PowQuot.mk 𝓘 B)) := by
    intro hAB
    have hI : (A ∩ B) ∈ 𝓘.mem := (disjoint_mk_iff (𝓘 := 𝓘) A B).1 hAB
    have hJ : (A ∩ B) ∈ 𝓙.mem := h _ hI
    simpa using (mapOfLe_disjoint_iff (𝓘 := 𝓘) (𝓙 := 𝓙) h A B).2 hJ

  /-- `mapOfLe` preserves complementarity (monotone direction). -/
  lemma mapOfLe_preserves_isCompl
    {𝓘 𝓙 : BoolIdeal} (h : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem)
    (A B : Set ℕ) :
    IsCompl (PowQuot.mk 𝓘 A : PowQuot 𝓘) (PowQuot.mk 𝓘 B) →
    IsCompl (PowQuot.mapOfLe h (PowQuot.mk 𝓘 A))
            (PowQuot.mapOfLe h (PowQuot.mk 𝓘 B)) := by
    intro hAB
    rcases (isCompl_mk_iff (𝓘 := 𝓘) A B).1 hAB with ⟨hI1, hI2⟩
    have hJ1 : (A ∩ B) ∈ 𝓙.mem := h _ hI1
    have hJ2 : (Aᶜ ∩ Bᶜ) ∈ 𝓙.mem := h _ hI2
    exact (mapOfLe_isCompl_iff (𝓘 := 𝓘) (𝓙 := 𝓙) h A B).2 ⟨hJ1, hJ2⟩
end MapOfLe_DisjointCompl

/-! ### More disjointness-with-complements -/
section DisjointComplMore
  variable {𝓘 : BoolIdeal} (A B : Set ℕ)

  /-- Disjoint with a complement on the right. -/
  @[simp] lemma disjoint_mk_compl_right :
      Disjoint (PowQuot.mk 𝓘 A) ((PowQuot.mk 𝓘 B)ᶜ) ↔ (A \ B) ∈ 𝓘.mem := by
    -- `Disjoint x y ↔ x ⊓ y = ⊥`, push `ᶜ` through and reduce to smallness.
    simp only [disjoint_iff, mk_compl, mk_inf_mk, mk_eq_bot_iff, Set.diff_eq]

  /-- Disjoint with a complement on the left. -/
  @[simp] lemma disjoint_compl_left_mk :
      Disjoint ((PowQuot.mk 𝓘 A)ᶜ) (PowQuot.mk 𝓘 B) ↔ (B \ A) ∈ 𝓘.mem := by
    -- symmetric to the previous: swap roles and use `Set.diff_eq`.
    simp only [disjoint_iff, mk_compl, mk_inf_mk, mk_eq_bot_iff, Set.diff_eq, Set.inter_comm]
end DisjointComplMore

/-! ### Disjoint as order: Bridge between disjointness and order relations
Key theorem: Disjoint x y ↔ x ≤ yᶜ in Boolean algebras.
This section provides the bridge lemmas connecting disjointness to order. -/
section DisjointAsOrder
  variable {𝓘 : BoolIdeal}

  @[simp] lemma disjoint_mk_iff_le_compl (A B : Set ℕ) :
      Disjoint (PowQuot.mk 𝓘 A) (PowQuot.mk 𝓘 B)
      ↔ (PowQuot.mk 𝓘 A : PowQuot 𝓘) ≤ (PowQuot.mk 𝓘 B)ᶜ := by
    -- Boolean algebra fact: `Disjoint x y ↔ x ≤ yᶜ`
    -- Use your mk-lemmas on both sides.
    constructor
    · intro h
      -- `x ⊓ y = ⊥` ⇒ `x ≤ yᶜ`; reduce with your iff lemmas
      -- (either by general BA facts or directly by smallness).
      -- Here we go via smallness:
      have : (A ∩ B) ∈ 𝓘.mem := (disjoint_mk_iff (𝓘 := 𝓘) A B).1 h
      simpa [mk_le_compl_mk] using this
    · intro h
      -- `x ≤ yᶜ` ⇒ `x ⊓ y = ⊥`
      have : (A ∩ B) ∈ 𝓘.mem := by
        simpa [mk_le_compl_mk] using h
      exact (disjoint_mk_iff (𝓘 := 𝓘) A B).2 this
end DisjointAsOrder

/-! ### Disjoint as order, in the image -/
section MapDisjointAsOrder
  variable {𝓘 𝓙 : BoolIdeal}
  variable (h : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem)

  @[simp] lemma mapOfLe_disjoint_iff_le_compl (A B : Set ℕ) :
      Disjoint (PowQuot.mapOfLe h (PowQuot.mk 𝓘 A))
               (PowQuot.mapOfLe h (PowQuot.mk 𝓘 B))
      ↔ PowQuot.mapOfLe h (PowQuot.mk 𝓘 A)
           ≤ (PowQuot.mapOfLe h (PowQuot.mk 𝓘 B))ᶜ := by
    -- Both sides rewrite to `(A ∩ B) ∈ 𝓙.mem`
    have h₁ := mapOfLe_disjoint_iff (𝓘 := 𝓘) (𝓙 := 𝓙) h A B
    have h₂ := (mk_le_compl_mk (𝓘 := 𝓙) A B)
    -- turn the RHS order into smallness via mk-lemmas:
    simpa [PowQuot.mapOfLe_mk] using h₁.trans h₂.symm
end MapDisjointAsOrder

/-! ### Order isomorphism when the ideals coincide on smallness -/
section MapOrderIso
  variable {𝓘 𝓙 : BoolIdeal}

  /-- If `𝓘.mem` and `𝓙.mem` agree pointwise, the quotients are order‑isomorphic. -/
  def mapOfLe_orderIso_of_iff
      (hiff : ∀ S, S ∈ 𝓘.mem ↔ S ∈ 𝓙.mem) :
      PowQuot 𝓘 ≃o PowQuot 𝓙 :=
  { toEquiv :=
    { toFun    := PowQuot.mapOfLe (fun S h => (hiff S).1 h)
      invFun   := PowQuot.mapOfLe (fun S h => (hiff S).2 h)
      left_inv := by
        intro x; refine Quot.inductionOn x ?_; intro A
        simp [PowQuot.mapOfLe_mk]
      right_inv := by
        intro y; refine Quot.inductionOn y ?_; intro A
        simp [PowQuot.mapOfLe_mk] },
    map_rel_iff' := by
      intro x y; refine Quot.induction_on₂ x y ?_; intro A B
      -- translate both sides to smallness of `(A \ B)` and use `hiff`
      have h₁ : PowQuot.mapOfLe (fun S h => (hiff S).1 h) (PowQuot.mk 𝓘 A)
                ≤ PowQuot.mapOfLe (fun S h => (hiff S).1 h) (PowQuot.mk 𝓘 B)
               ↔ (A \ B) ∈ 𝓙.mem := by
        simpa [PowQuot.mapOfLe_mk, mk_le_mk]
      have h₂ : (PowQuot.mk 𝓘 A : PowQuot 𝓘) ≤ PowQuot.mk 𝓘 B
               ↔ (A \ B) ∈ 𝓘.mem := by
        simpa [mk_le_mk]
      simpa [h₂] using h₁.trans ⟨fun h => (hiff (A \ B)).2 h, fun h => (hiff (A \ B)).1 h⟩ }

  @[simp] lemma mapOfLe_orderIso_of_iff_apply_mk
      (hiff : ∀ S, S ∈ 𝓘.mem ↔ S ∈ 𝓙.mem) (A : Set ℕ) :
      mapOfLe_orderIso_of_iff (𝓘 := 𝓘) (𝓙 := 𝓙) hiff (PowQuot.mk 𝓘 A)
        = PowQuot.mk 𝓙 A := by
    simp [mapOfLe_orderIso_of_iff, PowQuot.mapOfLe_mk]

  @[simp] lemma mapOfLe_orderIso_of_iff_symm_apply_mk
      (hiff : ∀ S, S ∈ 𝓘.mem ↔ S ∈ 𝓙.mem) (A : Set ℕ) :
      (mapOfLe_orderIso_of_iff (𝓘 := 𝓘) (𝓙 := 𝓙) hiff).symm (PowQuot.mk 𝓙 A)
        = PowQuot.mk 𝓘 A := by
    -- The symm of an OrderIso reverses its effect, and since forward map takes 𝓘 to 𝓙,
    -- the backward map takes 𝓙 to 𝓘
    apply OrderIso.injective (mapOfLe_orderIso_of_iff hiff)
    rw [OrderIso.apply_symm_apply]
    simp [mapOfLe_orderIso_of_iff_apply_mk]

  /-- The forward map is injective when ideals agree pointwise. -/
  lemma mapOfLe_injective_of_iff {𝓘 𝓙 : BoolIdeal}
      (hiff : ∀ S, S ∈ 𝓘.mem ↔ S ∈ 𝓙.mem) :
      Function.Injective (PowQuot.mapOfLe (fun S h => (hiff S).1 h)) := by
    simpa [mapOfLe_orderIso_of_iff] using
      (mapOfLe_orderIso_of_iff (𝓘 := 𝓘) (𝓙 := 𝓙) hiff).injective

  /-- The forward map is surjective when ideals agree pointwise. -/
  lemma mapOfLe_surjective_of_iff {𝓘 𝓙 : BoolIdeal}
      (hiff : ∀ S, S ∈ 𝓘.mem ↔ S ∈ 𝓙.mem) :
      Function.Surjective (PowQuot.mapOfLe (fun S h => (hiff S).1 h)) := by
    simpa [mapOfLe_orderIso_of_iff] using
      (mapOfLe_orderIso_of_iff (𝓘 := 𝓘) (𝓙 := 𝓙) hiff).surjective
end MapOrderIso

/-! ### Functoriality of `mapOfLe` -/
section MapOfLeFunctoriality
  variable {𝓘 𝓙 𝓚 : BoolIdeal}

  /-- Composition: mapping `𝓘 ⟶ 𝓙 ⟶ 𝓚` equals mapping along the composed inclusion. -/
  lemma mapOfLe_comp
      (h₁ : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem)
      (h₂ : ∀ S, S ∈ 𝓙.mem → S ∈ 𝓚.mem)
      (x : PowQuot 𝓘) :
      PowQuot.mapOfLe h₂ (PowQuot.mapOfLe h₁ x)
        = PowQuot.mapOfLe (fun _ h => h₂ _ (h₁ _ h)) x := by
    refine Quot.induction_on x ?_; intro A
    simp [PowQuot.mapOfLe_mk]

  /-- Identity: mapping along the identity inclusion is the identity map. -/
  @[simp] lemma mapOfLe_id (x : PowQuot 𝓘) :
      PowQuot.mapOfLe (fun S (h : S ∈ 𝓘.mem) => h) x = x := by
    refine Quot.induction_on x ?_; intro A
    simp [PowQuot.mapOfLe_mk]

  /-- Symmetric form of composition: composed inclusion equals composition of mappings. -/
  lemma mapOfLe_comp' {𝓘 𝓙 𝓚 : BoolIdeal}
      (h₁ : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem)
      (h₂ : ∀ S, S ∈ 𝓙.mem → S ∈ 𝓚.mem)
      (x : PowQuot 𝓘) :
      PowQuot.mapOfLe (fun S h => h₂ _ (h₁ _ h)) x
        = PowQuot.mapOfLe h₂ (PowQuot.mapOfLe h₁ x) := 
    (mapOfLe_comp h₁ h₂ x).symm
end MapOfLeFunctoriality

/-! ### Mapping preserves ⊥ and ⊤ -/
section MapThresholdEnds
  variable {𝓘 𝓙 : BoolIdeal}
  variable (h : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem)

  @[simp] lemma mapOfLe_bot : PowQuot.mapOfLe h (⊥ : PowQuot 𝓘) = ⊥ := by
    -- `⊥ = mk ∅`, and mapping preserves `mk` on representatives.
    simp [mk_bot, PowQuot.mapOfLe_mk]

  @[simp] lemma mapOfLe_top : PowQuot.mapOfLe h (⊤ : PowQuot 𝓘) = ⊤ := by
    -- `⊤ = mk univ`.
    simp [mk_top, PowQuot.mapOfLe_mk]
end MapThresholdEnds

/-! ### IsCompl lemmas for mk complements -/
section IsComplMore
  variable {𝓘 : BoolIdeal} (A : Set ℕ)

  /-- The quotient complement is indeed a complement. -/
  @[simp] lemma isCompl_mk_compl :
      IsCompl (PowQuot.mk 𝓘 A) ((PowQuot.mk 𝓘 A)ᶜ) :=
    isCompl_compl

  /-- And identifying `(mk A)ᶜ` with `mk Aᶜ`. -/
  @[simp] lemma isCompl_mk_mk_compl :
      IsCompl (PowQuot.mk 𝓘 A) (PowQuot.mk 𝓘 Aᶜ) := by
    have h := isCompl_compl (x := PowQuot.mk 𝓘 A)
    simp only [mk_compl] at h
    exact h
end IsComplMore

/-! ### Absorption with complements -/
section Absorption
  variable {𝓘 : BoolIdeal} (A : Set ℕ)

  @[simp] lemma mk_inf_compl :
      PowQuot.mk 𝓘 A ⊓ (PowQuot.mk 𝓘 A)ᶜ = (⊥ : PowQuot 𝓘) := by
    simpa using (isCompl_mk_compl (𝓘 := 𝓘) A).inf_eq_bot

  @[simp] lemma mk_sup_compl :
      PowQuot.mk 𝓘 A ⊔ (PowQuot.mk 𝓘 A)ᶜ = (⊤ : PowQuot 𝓘) := by
    simpa using (isCompl_mk_compl (𝓘 := 𝓘) A).sup_eq_top

  @[simp] lemma mk_inf_mk_compl :
      PowQuot.mk 𝓘 A ⊓ PowQuot.mk 𝓘 Aᶜ = (⊥ : PowQuot 𝓘) := by
    simpa [mk_compl] using (isCompl_mk_mk_compl (𝓘 := 𝓘) A).inf_eq_bot

  @[simp] lemma mk_sup_mk_compl :
      PowQuot.mk 𝓘 A ⊔ PowQuot.mk 𝓘 Aᶜ = (⊤ : PowQuot 𝓘) := by
    simpa [mk_compl] using (isCompl_mk_mk_compl (𝓘 := 𝓘) A).sup_eq_top
end Absorption

/-! ### Mapped disjoint-complement variants -/
section MapOfLe_DisjointComplMore
  variable {𝓘 𝓙 : BoolIdeal}
  variable (h : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem) (A B : Set ℕ)

  /-- Disjoint in the image with a complement on the right. -/
  @[simp] lemma mapOfLe_disjoint_compl_right_iff :
      Disjoint (PowQuot.mapOfLe h (PowQuot.mk 𝓘 A))
               ((PowQuot.mapOfLe h (PowQuot.mk 𝓘 B))ᶜ)
        ↔ (A \ B) ∈ 𝓙.mem := by
    -- Reduce to `inf = ⊥`, push `mapOfLe` and `ᶜ`, then use your threshold.
    simp only [disjoint_iff, PowQuot.mapOfLe_mk]
    simp only [mk_compl, mk_inf_mk, mk_eq_bot_iff, Set.diff_eq]

  /-- Disjoint in the image with a complement on the left. -/
  @[simp] lemma mapOfLe_compl_left_disjoint_iff :
      Disjoint ((PowQuot.mapOfLe h (PowQuot.mk 𝓘 A))ᶜ)
               (PowQuot.mapOfLe h (PowQuot.mk 𝓘 B))
        ↔ (B \ A) ∈ 𝓙.mem := by
    simp only [disjoint_iff, PowQuot.mapOfLe_mk]
    simp only [mk_compl, mk_inf_mk, mk_eq_bot_iff, Set.diff_eq, Set.inter_comm]
end MapOfLe_DisjointComplMore

/-! ### Mapped absorption forms -/
section MapAbsorption
  variable {𝓘 𝓙 : BoolIdeal} (h : ∀ S, S ∈ 𝓘.mem → S ∈ 𝓙.mem) (A : Set ℕ)

  @[simp] lemma mapOfLe_mk_inf_compl :
      (PowQuot.mapOfLe h (PowQuot.mk 𝓘 A)) ⊓
      (PowQuot.mapOfLe h (PowQuot.mk 𝓘 A))ᶜ = (⊥ : PowQuot 𝓙) := by
    -- direct `simp`: map to `mk 𝓙 A` then use absorption above
    simpa [PowQuot.mapOfLe_mk] using
      (mk_inf_compl (𝓘 := 𝓙) A)

  @[simp] lemma mapOfLe_mk_sup_compl :
      (PowQuot.mapOfLe h (PowQuot.mk 𝓘 A)) ⊔
      (PowQuot.mapOfLe h (PowQuot.mk 𝓘 A))ᶜ = (⊤ : PowQuot 𝓙) := by
    simpa [PowQuot.mapOfLe_mk] using
      (mk_sup_compl (𝓘 := 𝓙) A)

  @[simp] lemma mapOfLe_mk_inf_mk_compl :
      (PowQuot.mapOfLe h (PowQuot.mk 𝓘 A)) ⊓
      (PowQuot.mapOfLe h (PowQuot.mk 𝓘 Aᶜ)) = (⊥ : PowQuot 𝓙) := by
    simpa [PowQuot.mapOfLe_mk] using
      (mk_inf_mk_compl (𝓘 := 𝓙) A)

  @[simp] lemma mapOfLe_mk_sup_mk_compl :
      (PowQuot.mapOfLe h (PowQuot.mk 𝓘 A)) ⊔
      (PowQuot.mapOfLe h (PowQuot.mk 𝓘 Aᶜ)) = (⊤ : PowQuot 𝓙) := by
    simpa [PowQuot.mapOfLe_mk] using
      (mk_sup_mk_compl (𝓘 := 𝓙) A)
end MapAbsorption

/-! 
### PowQuot goal reducer pattern (cheatsheet)

When proving goals about `PowQuot 𝓘`:
```lean
refine Quot.inductionOn x ?_; intro A
refine Quot.inductionOn y ?_; intro B
-- now use mk-lemmas to expose reps:
simp [mk_le_mk, mk_inf_mk, mk_sup_mk, mk_compl, mk_top, mk_bot]
-- close with ideal facts: `𝓘.empty_mem`, `𝓘.union_mem`, `𝓘.downward`
-- and set identities: diff_inter_union, union_diff_eq, subset_union_inter
```
-/

/-! ## Handy set inclusion identities

These are the key identities used throughout the Boolean algebra proofs.
They enable us to apply 𝓘.union_mem and 𝓘.downward.
Not in global simp set to avoid loops - use locally with `simp [diff_inter_union]`.
-/

section SetInclusionLemmas

-- Distribution of difference over intersection
lemma diff_inter_union {α : Type*} (A B C : Set α) : 
  A \ (B ∩ C) = (A \ B) ∪ (A \ C) := by
  ext x; simp [Set.mem_diff, Set.mem_inter_iff, Set.mem_union]
  tauto

-- Distribution of union over difference  
lemma union_diff_eq {α : Type*} (A B C : Set α) :
  (A ∪ B) \ C = (A \ C) ∪ (B \ C) := by
  ext x; simp [Set.mem_diff, Set.mem_union]
  tauto

-- Subset relationship for distributivity
lemma subset_union_inter {α : Type*} (A B C : Set α) :
  A ⊆ (A ∪ B) ∩ (A ∪ C) := by
  intro x hx
  exact ⟨Or.inl hx, Or.inl hx⟩

end SetInclusionLemmas

/-!
## Generalization Note

The entire construction generalizes seamlessly from `Set ℕ` to `Set α` for any type `α`.
When ready to generalize:

1. Add parameter `{α : Type*}` at the module level
2. Replace all occurrences of `Set ℕ` with `Set α`
3. Update `BoolIdeal` to be parametrized by `α`:
   ```lean
   structure BoolIdeal (α : Type*) where
     mem : Set (Set α)
     empty_mem : ∅ ∈ mem
     union_mem : ∀ {A B}, A ∈ mem → B ∈ mem → (A ∪ B) ∈ mem
     downward : ∀ {A B}, A ⊆ B → B ∈ mem → A ∈ mem
   ```
4. All proofs remain identical - they only use set algebra, no special properties of ℕ

The mk-lemmas, instances, and `mapOfLe` all port without changes.
No decidability assumptions are needed for the order/lattice/Boolean algebra proofs.
-/

/-!
## Roadmap to Full BooleanAlgebra Instance (COMPLETED ✅)

Sketch (no code here, just a precise checklist):

1) Define the order (choose C1 or C2).

  -- C1 (order = "difference small")
  def LE.le : PowQuot 𝓘 → PowQuot 𝓘 → Prop :=
    Quot.liftOn₂ … (fun A B => (A \ B) ∈ 𝓘.mem) (well_defined_proof)

  instance : LE (PowQuot 𝓘) := ⟨LE.le 𝓘⟩
  instance : Preorder (PowQuot 𝓘) := { le := (· ≤ ·), le_refl := …, le_trans := … }
  instance : PartialOrder (PowQuot 𝓘) := { le_antisymm := … }

2) Build lattice instances that promote Min/Max to Inf/Sup:
  - instance : SemilatticeInf (PowQuot 𝓘) := { inf := min, inf_le_left := ..., inf_le_right := ..., le_inf := ... }
  - instance : SemilatticeSup (PowQuot 𝓘) := { sup := max, le_sup_left := ..., le_sup_right := ..., sup_le := ... }
  - After these instances, Min/Max automatically become Inf/Sup (⊓/⊔) in the API

3) Lattice & Distributive:
  - Each lattice axiom is a `Quot.induction` that reduces to standard set inclusions/identities.
  - Distributivity follows from set distributivity: A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)

4) BooleanAlgebra.mk:
   supply:
     inf_compl_le_bot : ∀ x, x ⊓ xᶜ ≤ ⊥       -- reduces to A ∩ Aᶜ = ∅
     top_le_sup_compl : ∀ x, ⊤ ≤ x ⊔ xᶜ       -- reduces to A ∪ Aᶜ = univ
     sdiff_eq         : x \ y = x ⊓ yᶜ        -- definitional for SDiff α if you register it
     himp_eq          : x ⇨ y = xᶜ ⊔ y        -- for HImp α in Boolean algebras

5) (Optional) Package the Stone map as a Boolean isomorphism: 
   all three preservation lemmas are done.
-/

end StoneSupport

/-! ### Calibration Program

The constructive principles needed for surjectivity of Φ_I depend on I:
- For FinIdeal: constructively provable (no extra axioms)
- For DensityZeroIdeal: requires principles related to WLPO
- For other ideals: calibrate case by case

This provides a flexible testbed for measuring constructive strength.
-/

/-!
## PowQuot cheatsheet (via smallness in the ideal)

**Thresholds**
* `mk_eq_bot_iff A`        ↔  `A ∈ 𝓘.mem`
* `mk_eq_top_iff A`        ↔  `Aᶜ ∈ 𝓘.mem`
* `mk_inf_eq_bot_iff A B`  ↔  `A ∩ B ∈ 𝓘.mem`
* `mk_sup_eq_top_iff A B`  ↔  `Aᶜ ∩ Bᶜ ∈ 𝓘.mem`
* `mk_ne_bot_iff A`        ↔  `A ∉ 𝓘.mem`
* `mk_ne_top_iff A`        ↔  `Aᶜ ∉ 𝓘.mem`
* `compl_mk_eq_bot_iff A`  ↔  `Aᶜ ∈ 𝓘.mem`
* `compl_mk_eq_top_iff A`  ↔  `A ∈ 𝓘.mem`

**Equality/Order**
* `mk_eq_mk_iff A B`       ↔  `A △ B ∈ 𝓘.mem`
* `mk_le_mk A B`           ↔  `A \ B ∈ 𝓘.mem`
* `mk_le_compl_mk A B`     ↔  `A ∩ B ∈ 𝓘.mem`
* `compl_mk_le_mk_iff A B` ↔  `Aᶜ ∩ Bᶜ ∈ 𝓘.mem`

**Disjoint/Compl**
* `disjoint_mk_iff A B`    ↔  `A ∩ B ∈ 𝓘.mem`
* `isCompl_mk_iff A B`     ↔  `(A ∩ B) ∈ 𝓘.mem ∧ (Aᶜ ∩ Bᶜ) ∈ 𝓘.mem`

**Strict order**
* `mk_lt_mk_iff A B`       ↔  `(A \ B) ∈ 𝓘.mem ∧ (A △ B) ∉ 𝓘.mem`

**Mapped analogues (`𝓘 ⟶ 𝓙` via `h`)**: replace `mk 𝓘 …` by `mapOfLe h (mk 𝓘 …)`,
  and replace membership in `𝓘.mem` with `𝓙.mem`.
  * `mapOfLe_compl_mk_le_mk_iff A B` ↔  `Aᶜ ∩ Bᶜ ∈ 𝓙.mem` (left-complement bridge)
  * `mapOfLe_compl_mk_not_le_mk_iff A B` ↔  `Aᶜ ∩ Bᶜ ∉ 𝓙.mem` (negative left-complement)
  * `mapOfLe_compl_mk_eq_bot_iff A` ↔  `Aᶜ ∈ 𝓙.mem`
  * `mapOfLe_compl_mk_eq_top_iff A` ↔  `A ∈ 𝓙.mem`
-/

end Papers.P4Meta