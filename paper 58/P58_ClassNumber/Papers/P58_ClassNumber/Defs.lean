/-
  Paper 58: Class Number Correction — Definitions
  Core structures for quadratic imaginary fields, fractional ideals,
  totally real cubics, and Weil lattice data.
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# Definitions

We define lightweight structures capturing the arithmetic data needed for
the class-number correction formula h · Nm(𝔞) = f.

All structures store explicit integer/rational data; no Mathlib algebraic
number theory is imported.
-/

/-- A quadratic imaginary field K = ℚ(√-d), represented by its invariants. -/
structure QuadImagField where
  d : ℕ               -- d in ℚ(√-d), assumed square-free
  d_pos : d > 0
  disc : ℤ            -- Δ_K (fundamental discriminant)
  abs_disc : ℕ        -- |Δ_K|
  class_num : ℕ       -- h_K
  abs_disc_eq : abs_disc = disc.natAbs

/-- K = ℚ(√-5): h_K = 2, Δ_K = -20, |Δ_K| = 20 -/
def K_sqrt5 : QuadImagField where
  d := 5
  d_pos := by norm_num
  disc := -20
  abs_disc := 20
  class_num := 2
  abs_disc_eq := by native_decide

/-- An O_K-ideal basis, represented by its ℤ-basis elements and norm.
    Basis elements α, β ∈ K are stored as (re_num/re_den, im_num/im_den · √-d).
    The ideal norm Nm(𝔞) is stored directly. -/
structure IdealBasis where
  /-- First basis element: α = α_re_num/α_re_den + (α_im_num/α_im_den)·√-d -/
  α_re_num : ℤ
  α_re_den : ℕ
  α_im_num : ℤ
  α_im_den : ℕ
  /-- Second basis element: β -/
  β_re_num : ℤ
  β_re_den : ℕ
  β_im_num : ℤ
  β_im_den : ℕ
  /-- Ideal norm Nm(𝔞) -/
  ideal_norm : ℕ
  ideal_norm_pos : ideal_norm > 0
  /-- Denominators are positive -/
  α_re_den_pos : α_re_den > 0
  α_im_den_pos : α_im_den > 0
  β_re_den_pos : β_re_den > 0
  β_im_den_pos : β_im_den > 0

/-- The trivial ideal O_K = ℤ ⊕ ℤ·√-d (free case, Nm = 1).
    Basis: {1, √-d}. -/
def trivialIdeal : IdealBasis where
  α_re_num := 1; α_re_den := 1; α_im_num := 0; α_im_den := 1
  β_re_num := 0; β_re_den := 1; β_im_num := 1; β_im_den := 1
  ideal_norm := 1
  ideal_norm_pos := by norm_num
  α_re_den_pos := by norm_num
  α_im_den_pos := by norm_num
  β_re_den_pos := by norm_num
  β_im_den_pos := by norm_num

/-- The non-trivial ideal 𝔭 = (2, 1+√-5) for K = ℚ(√-5).
    Basis: {2, 1+√-5}. Nm(𝔭) = 2. -/
def ideal_p_K5 : IdealBasis where
  α_re_num := 2; α_re_den := 1; α_im_num := 0; α_im_den := 1
  β_re_num := 1; β_re_den := 1; β_im_num := 1; β_im_den := 1
  ideal_norm := 2
  ideal_norm_pos := by norm_num
  α_re_den_pos := by norm_num
  α_im_den_pos := by norm_num
  β_re_den_pos := by norm_num
  β_im_den_pos := by norm_num

/-- A totally real cubic field, identified by conductor f where disc(F) = f². -/
structure TotallyRealCubic where
  conductor : ℕ       -- f, where disc(F) = f²
  conductor_pos : conductor > 0

/-- Classification of Steinitz type -/
inductive SteinitzType where
  | free      : SteinitzType   -- Nm(𝔞) = 1, lattice is O_K · w₀
  | nonFree   : SteinitzType   -- Nm(𝔞) = 2, lattice is 𝔭 · w₀ (for h_K = 2)
  | inert     : SteinitzType   -- f is inert in K, no CM fourfold exists
  deriving DecidableEq, Repr

/-- Weil lattice data for the h_K > 1 case.
    Stores the arithmetic of the corrected formula h · Nm(𝔞) = f. -/
structure WeilLatticeData where
  K : QuadImagField
  F : TotallyRealCubic
  steinitz : SteinitzType
  ideal : IdealBasis
  /-- Hermitian self-intersection h = h_num / h_den -/
  h_num : ℤ
  h_den : ℕ
  h_den_pos : h_den > 0
  /-- The fundamental identity: h_num · Nm(𝔞) = conductor · h_den -/
  fundamental_identity : h_num * ideal.ideal_norm = F.conductor * h_den
