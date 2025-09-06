import Papers.P4_SpectralGeometry.Discrete.NeckGraph
import Papers.P4_SpectralGeometry.Discrete.TuringEncoding
import Mathlib.Data.Matrix.Basic

/-!
# Common Definitions for Discrete CPW Model

This module consolidates common definitions used across multiple files
to reduce duplication and ensure consistency.

## Contents
* Vector types and inner products
* Rayleigh quotient (unified for both ℚ and ℝ)
* Orthogonality conditions
* Spectral gap definitions
-/

namespace Papers.P4_SpectralGeometry.Discrete

/-! ## Vector Types -/

/-- A rational vector on a discrete structure -/
def RationalVector (T : Type*) [Fintype T] := T → ℚ

/-- A real vector on a discrete structure -/
def RealVector (T : Type*) [Fintype T] := T → ℝ

/-- Convert rational vector to real -/
def RationalVector.toReal {T : Type*} [Fintype T] (v : RationalVector T) : RealVector T :=
  fun i => (v i : ℝ)

/-! ## Inner Products -/

/-- Rational inner product -/
def innerProductℚ {T : Type*} [Fintype T] (u v : RationalVector T) : ℚ :=
  Finset.univ.sum (fun i => u i * v i)

/-- Real inner product -/
def innerProductℝ {T : Type*} [Fintype T] (u v : RealVector T) : ℝ :=
  Finset.univ.sum (fun i => u i * v i)

notation "⟪" u ", " v "⟫_ℚ" => innerProductℚ u v
notation "⟪" u ", " v "⟫" => innerProductℝ u v

/-! ## Orthogonality -/

/-- A vector is orthogonal to constants if its sum is zero -/
def orthogonalToConstants {T : Type*} [Fintype T] {K : Type*} [AddCommMonoid K] 
    (v : T → K) : Prop :=
  Finset.univ.sum v = 0

/-! ## Rayleigh Quotient -/

/-- General Rayleigh quotient for any field -/
noncomputable def RayleighQuotient {T : Type*} [Fintype T] {K : Type*} [Field K] [DecidableEq K]
    (L : Matrix T T K) (v : T → K) : K :=
  let Lv : T → K := fun i => Finset.univ.sum (fun j => L i j * v j)
  let num := Finset.univ.sum (fun i => v i * Lv i)
  let den := Finset.univ.sum (fun i => v i * v i)
  if den = 0 then 0 else num / den

/-- Rayleigh quotient for discrete neck torus (rational) -/
noncomputable def RayleighQuotientℚ (T : DiscreteNeckTorus) 
    (v : RationalVector T.Vertex) : ℚ :=
  RayleighQuotient T.discreteLaplacian v

/-- Rayleigh quotient for discrete neck torus (real) -/
noncomputable def RayleighQuotientℝ (T : DiscreteNeckTorus) 
    (v : RealVector T.Vertex) : ℝ :=
  let L := T.discreteLaplacian.map (fun x => (x : ℝ))
  RayleighQuotient L v

/-- Rayleigh quotient for Turing neck torus (rational) -/
noncomputable def RayleighQuotientTuring (T : TuringNeckTorus) (N : ℕ)
    (v : RationalVector T.Vertex) : ℚ :=
  RayleighQuotient (T.perturbedLaplacian N) v

/-! ## Spectral Gap Characterizations -/

/-- Variational characterization of spectral gap (real) -/
noncomputable def spectralGapVariational (T : DiscreteNeckTorus) : ℝ :=
  sInf {RayleighQuotientℝ T v | (v : RealVector T.Vertex) 
    (hv : ¬(∀ x, v x = 0)) (horth : orthogonalToConstants v)}

/-- Spectral gap predicate for Π₁ encoding -/
def spectralGapPredicate {T : Type*} [Fintype T] 
    (L : Matrix T T ℚ) (threshold : ℚ) : Prop :=
  ∀ v : RationalVector T, (∃ x, v x ≠ 0) → orthogonalToConstants v → 
    RayleighQuotient L v ≥ threshold

end Papers.P4_SpectralGeometry.Discrete