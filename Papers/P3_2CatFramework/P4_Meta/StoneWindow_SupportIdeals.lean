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

/-- The class of `χ_A` is idempotent in the ring quotient. -/
lemma chi_idem_in_quot (𝓘 : BoolIdeal) (A : Set ℕ) :
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

/-! ## D3(c4). Two idempotents hypothesis and equivalence scaffold -/

section D3c4
open Classical
variable {R : Type*}

/-- Rings with only two idempotents, 0 and 1. -/
class TwoIdempotents (R : Type*) [Semiring R] : Prop :=
  (resolve : ∀ x : R, x * x = x → x = 0 ∨ x = 1)

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

/-- Support of negation is the same as the support. -/
lemma supp'_neg (f : Linf R) : supp' (R := R) (-f) = supp' (R := R) f := by
  ext n; by_cases h : f n = 0 <;> simp [supp', h]

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

/-- A canonical (noncomputable) representative of a quotient element. -/
noncomputable def rep (q : LinfQuotRing 𝓘 R) : Linf R :=
  Classical.choose (Quot.exists_rep q)

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

/-
-- TODO (D3(c4)): Once `PsiStoneIdem` is implemented (via `TwoIdempotents.resolve`),
-- prove the inverse laws and construct:
-- noncomputable def StoneEquiv :
--   PowQuot 𝓘 ≃ LinfQuotRingIdem 𝓘 R := 
-- { toFun := PhiStoneIdem 𝓘, 
--   invFun := PsiStoneIdem 𝓘, 
--   left_inv := ..., 
--   right_inv := ... }
-/

end
end D3c4

end StoneSupport

-- The interface is provided as a minimal skeleton with 0 sorries
-- Full quotient construction and isomorphism proof deferred

/-! ### Calibration Program

The constructive principles needed for surjectivity of Φ_I depend on I:
- For FinIdeal: constructively provable (no extra axioms)
- For DensityZeroIdeal: requires principles related to WLPO
- For other ideals: calibrate case by case

This provides a flexible testbed for measuring constructive strength.
-/

end Papers.P4Meta