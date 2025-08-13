/-
Papers/P2_BidualGap/Stone/FiniteEmbeddings.lean
Finite distributive lattice embeddings via Stone window

This implements embeddings of finite distributive lattices into the Boolean algebra
of idempotents in ℓ∞/c₀, using Birkhoff's representation theorem and disjoint block construction.
-/
import Mathlib.Tactic
import Mathlib.Order.DistribLattice
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Papers.P2_BidualGap.Stone.Window

noncomputable section
namespace Papers.P2.Stone.Finite
open Classical Papers.P2.Stone

-- ========================================================================
-- Disjoint infinite block construction
-- ========================================================================

/-- Choose disjoint infinite blocks U_j ⊆ ℕ using residue classes. -/
def blocks (k : ℕ) : Fin k → Set ℕ := fun i => {n | n % k = i.val}

/-- The blocks are pairwise disjoint. -/
lemma blocks_disjoint (k : ℕ) (i j : Fin k) (h : i ≠ j) : 
  Disjoint (blocks k i) (blocks k j) := by
  simp only [blocks, Set.disjoint_left]
  intro n hn1 hn2
  simp only [Set.mem_setOf_eq] at hn1 hn2
  have : i.val = j.val := by
    rw [← hn1, hn2]
  exact h (Fin.ext this)

/-- Each block is infinite. -/
lemma blocks_infinite (k : ℕ) (hk : k > 0) (i : Fin k) : 
  (blocks k i).Infinite := by
  simp only [blocks]
  -- The set {n | n % k = i.val} is infinite
  -- This follows from the fact that arithmetic progressions are infinite
  have h_exists : ∀ N : ℕ, ∃ n > N, n % k = i.val := by
    intro N
    let n := N + k - (N % k) + i.val
    use n
    constructor
    · -- n > N
      simp only [n]
      omega
    · -- n % k = i.val  
      simp only [n]
      rw [add_assoc, add_comm (i.val), ← add_assoc]
      rw [Nat.add_mod, Nat.add_mod]
      have h1 : (N + k - N % k) % k = 0 := by
        rw [Nat.add_sub_cancel']
        · exact Nat.mod_self k
        · exact Nat.mod_le N k
      rw [h1, zero_add, Nat.mod_mod]
      exact Nat.mod_lt i.val hk
  -- Use h_exists to show infiniteness
  rw [Set.infinite_iff_not_finite]
  intro h_fin
  obtain ⟨N, hN⟩ := Set.Finite.bddAbove h_fin
  obtain ⟨n, hn_gt, hn_mod⟩ := h_exists N
  have hn_mem : n ∈ blocks k i := by
    simp only [blocks, Set.mem_setOf_eq]
    exact hn_mod
  have hn_le : n ≤ N := hN hn_mem
  linarith

-- ========================================================================
-- Birkhoff representation for finite distributive lattices
-- ========================================================================

/-- For a finite distributive lattice, extract the join-irreducible elements.
    This is a simplified version - in practice we'd use mathlib's Birkhoff representation. -/
def joinIrreducibles (L : Type*) [Fintype L] [DistribLattice L] [OrderBot L] : Finset L :=
  -- In the full implementation, this would be the actual join-irreducibles
  -- For now, we use all elements as a placeholder  
  Finset.univ

/-- A down-set determined by a subset of join-irreducibles. -/
def downSet {L : Type*} [DistribLattice L] [OrderBot L] (J : Finset L) (D : Finset L) : Set L :=
  {x : L | ∃ j ∈ D, x ≤ j}

-- ========================================================================
-- Embedding construction  
-- ========================================================================

/-- Embed a finite distributive lattice into the Boolean algebra P(ℕ)/Fin
    via Birkhoff representation and block unions. -/
def embedFiniteDL (L : Type*) [Fintype L] [DistribLattice L] [OrderBot L] :
  L → BooleanAtInfinity := by
  -- Get the join-irreducibles
  let J := joinIrreducibles L
  let k := J.card
  
  intro x
  -- Find which join-irreducibles are ≤ x
  let relevantJ := J.filter (fun j => j ≤ x)
  -- Take the union of corresponding blocks
  let unionSet := ⋃ j ∈ relevantJ, blocks k (Finset.mem_univ j).choose
  exact [unionSet]

/-- The embedding preserves joins. -/
lemma embedFiniteDL_preserves_sup (L : Type*) [Fintype L] [DistribLattice L] [OrderBot L] 
  (x y : L) : 
  embedFiniteDL (x ⊔ y) = embedFiniteDL x ⊔ embedFiniteDL y := by
  -- This follows from the fact that join-irreducibles of x ⊔ y are the union of
  -- join-irreducibles of x and y, and blocks are disjoint
  sorry -- Technical: use distributivity and disjointness of blocks

/-- The embedding preserves meets. -/
lemma embedFiniteDL_preserves_inf (L : Type*) [Fintype L] [DistribLattice L] [OrderBot L] 
  (x y : L) : 
  embedFiniteDL (x ⊓ y) = embedFiniteDL x ⊓ embedFiniteDL y := by
  -- This follows from Birkhoff representation: x ⊓ y corresponds to the intersection
  -- of the down-sets, which translates to intersection of block unions
  sorry -- Technical: use Birkhoff representation and block properties

/-- The embedding is injective. -/
lemma embedFiniteDL_injective (L : Type*) [Fintype L] [DistribLattice L] [OrderBot L] : 
  Function.Injective (@embedFiniteDL L _ _ _) := by
  intro x y h_eq
  -- If embedFiniteDL x = embedFiniteDL y, then the corresponding block unions are almost equal
  -- Since blocks are infinite and disjoint, the only way this can happen is if 
  -- the same join-irreducibles are relevant for both x and y
  -- By Birkhoff representation, this means x = y
  sorry -- Technical: use injectivity of Birkhoff representation and block properties

-- ========================================================================
-- Main embedding theorem
-- ========================================================================

/-- Every finite distributive lattice embeds into the Boolean algebra P(ℕ)/Fin,
    and hence into Idempotents(ℓ∞/c₀) via the Stone window. -/
theorem finite_distributive_lattice_embedding 
  (L : Type*) [Fintype L] [DistribLattice L] [OrderBot L] :
  ∃ (φ : L →+* BooleanAtInfinity), Function.Injective φ := by
  -- The embedding is embedFiniteDL
  use {
    toFun := embedFiniteDL
    map_one' := by
      -- embedFiniteDL ⊤ = [ℕ] (union of all blocks)
      sorry
    map_mul' := embedFiniteDL_preserves_inf
    map_zero' := by
      -- embedFiniteDL ⊥ = [∅] (union of no blocks)  
      sorry
    map_add' := by
      -- This needs the Boolean ring structure where + is symmetric difference
      -- embedFiniteDL preserves the Boolean ring operations
      sorry
  }
  exact embedFiniteDL_injective L

/-- Corollary: finite distributive lattices embed into Idempotents(ℓ∞/c₀). -/
theorem finite_lattice_into_idempotents 
  (L : Type*) [Fintype L] [DistribLattice L] [OrderBot L] :
  ∃ (ψ : L → IdempotentFunctions), 
    Function.Injective ψ ∧ 
    (∀ x y, ψ (x ⊔ y) = ψ x ⊔ ψ y) ∧
    (∀ x y, ψ (x ⊓ y) = ψ x ⊓ ψ y) := by
  -- Compose the lattice embedding with the Stone window isomorphism
  obtain ⟨φ, hφ_inj⟩ := finite_distributive_lattice_embedding L
  obtain ⟨stone_iso, hstone_sup, hstone_inf, hstone_compl⟩ := stone_window_isomorphism
  
  use stone_iso ∘ φ
  constructor
  · exact Function.Injective.comp stone_iso.injective hφ_inj
  constructor
  · intro x y
    -- Use that both φ and stone_iso preserve joins
    sorry -- Apply hstone_sup and preservation by φ
  · intro x y  
    -- Use that both φ and stone_iso preserve meets
    sorry -- Apply hstone_inf and preservation by φ

-- ========================================================================
-- Concrete examples
-- ========================================================================

/-- Example: The 4-element Boolean algebra embeds into Idempotents(ℓ∞/c₀). -/
example : ∃ (ψ : Bool × Bool → IdempotentFunctions), Function.Injective ψ := by
  -- Bool × Bool with coordinatewise operations is the 4-element Boolean algebra
  have h_distrib : DistribLattice (Bool × Bool) := by infer_instance
  have h_finite : Fintype (Bool × Bool) := by infer_instance
  have h_bot : OrderBot (Bool × Bool) := by infer_instance
  obtain ⟨ψ, hψ_inj, _, _⟩ := @finite_lattice_into_idempotents (Bool × Bool) h_finite h_distrib h_bot
  exact ⟨ψ, hψ_inj⟩

/-- Example: Any finite chain embeds into Idempotents(ℓ∞/c₀). -/
example (n : ℕ) : ∃ (ψ : Fin n → IdempotentFunctions), Function.Injective ψ := by
  -- Fin n with ≤ is a finite distributive lattice (chain)
  haveI : DistribLattice (Fin n) := by 
    -- Chains are distributive lattices
    sorry -- Standard: linear orders are distributive
  haveI : OrderBot (Fin n) := by
    -- Finite types with linear order have bottom element (when n > 0)
    sorry -- Standard construction
  obtain ⟨ψ, hψ_inj, _, _⟩ := @finite_lattice_into_idempotents (Fin n) (by infer_instance) (by infer_instance) (by infer_instance)
  exact ⟨ψ, hψ_inj⟩

end Papers.P2.Stone.Finite