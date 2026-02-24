/-
  Paper 52: Decidability Transfer via Specialization
  Defs/GeometricAxioms.lean — Granular geometric axiomatic interface

  DESIGN PRINCIPLE: Each axiom corresponds to a specific proposition
  or theorem in the paper, not to the final conclusion. The main theorem
  must physically invoke sub_lefschetz_non_degenerate to bridge from
  geometry to algebra.

  TECHNICAL NOTE: We use a structure `GeometricData K` to bundle all
  geometric inputs (abelian varieties, Chow rings, specialization map,
  pairing) with their algebraic structure. This cleanly passes the
  K-module instances through to sub_lefschetz_non_degenerate.
-/
import Papers.P52_DecidabilityTransfer.Core.SubLefschetzNonDegenerate
import Mathlib.Algebra.Module.Submodule.Range

open scoped BigOperators

namespace Papers.P52

variable {K : Type*} [Field K]

-- ============================================================
-- Geometric Data Bundle
-- ============================================================

/-- A `GeometricData K` packages the geometric inputs for the
    decidability transfer: two abelian varieties (generic fiber A_Q
    and special fiber A_p), their Chow rings as K-vector spaces,
    the specialization map, and the intersection pairing. -/
structure GeometricData (K : Type*) [Field K] where
  /-- Chow ring of the generic fiber (char 0) -/
  CH_Q : Type*
  /-- Chow ring of the special fiber (char p) -/
  CH_p : Type*
  [instACG_Q : AddCommGroup CH_Q]
  [instMod_Q : Module K CH_Q]
  [instACG_p : AddCommGroup CH_p]
  [instMod_p : Module K CH_p]
  /-- Dimension of the special fiber -/
  dim_p : ℕ
  /-- Specialization map (K-linear) -/
  sp : CH_Q →ₗ[K] CH_p
  /-- Numerical intersection pairing on CH_p (bilinear form) -/
  int_pair : CH_p →ₗ[K] CH_p →ₗ[K] K
  /-- Numerical triviality predicate on CH_Q -/
  is_num_triv : CH_Q → Prop
  /-- Homological triviality predicate on CH_Q -/
  is_hom_triv : CH_Q → Prop

attribute [instance] GeometricData.instACG_Q GeometricData.instMod_Q
attribute [instance] GeometricData.instACG_p GeometricData.instMod_p

-- ============================================================
-- Granular Geometric Axioms (NOT the conclusion!)
-- ============================================================

/-- **Proposition 2.2**: If Z ≡_num 0 over Q, then sp(Z) is orthogonal
    to the entire liftable subspace U = im(sp). -/
def Prop22 (G : GeometricData K) : Prop :=
  ∀ (Z : G.CH_Q), G.is_num_triv Z →
    ∀ W ∈ LinearMap.range G.sp,
      G.int_pair (G.sp Z) W = 0

/-- **Proposition 2.1**: If sp(Z) = 0, then Z ≡_hom 0 over Q.
    (Smooth proper base change, SGA 4½.) -/
def Prop21 (G : GeometricData K) : Prop :=
  ∀ (Z : G.CH_Q), G.sp Z = 0 → G.is_hom_triv Z

/-- **Sections 3–4: Lefschetz Architecture for g ≤ 3**.
    im(sp) decomposes into definite primitive components.
    At g = 4 this fails: exotic Tate classes break anisotropicity. -/
def LefschetzArch (G : GeometricData K) : Prop :=
  G.dim_p ≤ 3 →
  ∃ (ι : Type*) (_ : Fintype ι) (_ : DecidableEq ι)
    (U_comp : ι → Submodule K G.CH_p),
    (∀ i, U_comp i ≤ LinearMap.range G.sp) ∧
    (∀ u ∈ LinearMap.range G.sp,
      ∃ (parts : ι → G.CH_p),
        (∀ i, parts i ∈ U_comp i) ∧ u = ∑ i, parts i) ∧
    (∀ i j, i ≠ j →
      ∀ x ∈ U_comp i, ∀ y ∈ U_comp j,
        G.int_pair x y = 0) ∧
    (∀ i, IsAnisotropicOn G.int_pair (U_comp i))

end Papers.P52
