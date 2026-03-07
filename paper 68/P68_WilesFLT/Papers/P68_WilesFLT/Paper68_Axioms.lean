/-
  Paper 68: The Logical Cost of Fermat's Last Theorem
  Paper68_Axioms.lean — Shared axiom file

  This file declares all opaque types and axiomatized deep theorems
  used in Targets 1 and 2. Deep theorems are NOT formalized; they
  are axiomatized with precise literature references.

  Axiomatized deep theorems:
  - B1: Brochard's finite-level criterion (Compositio Math. 2017, Thm 1.1)
  - B2: Effective Chebotarev (Lagarias–Montgomery–Odlyzko 1979; Ahn–Kwon 2019)
  - B3: Discriminant computability (standard algebraic number theory)

  CRM hierarchy and stage classifications for the Asymmetry Theorem.

  Author: Paul C.-K. Lee
  Date: February 2026
  Zero sorry. Zero warnings target.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Defs

-- ============================================================
-- § 1. Opaque Types
-- ============================================================

/-- An Artinian local ring (opaque; only axiomatized properties used). -/
axiom ArtinLocalRing : Type

/-- A module over an Artinian local ring (opaque). -/
axiom ArtinModule : ArtinLocalRing → Type

/-- Embedding dimension of an Artinian local ring. -/
axiom embDim : ArtinLocalRing → ℕ

/-- Flatness of a module over a local morphism A → B. -/
axiom IsFlat (A B : ArtinLocalRing) (M : ArtinModule B) : Prop

/-- Freeness of a B-module. -/
axiom IsFreeModule (B : ArtinLocalRing) (M : ArtinModule B) : Prop

/-- A number field (opaque). -/
axiom NumberField : Type

/-- The absolute discriminant of a number field. -/
axiom absDisc : NumberField → ℕ

/-- A conjugacy class in the Galois group of L/ℚ (opaque). -/
axiom ConjClass : NumberField → Type

/-- Frobenius element at prime q in L/ℚ lands in a conjugacy class. -/
axiom frobInClass (L : NumberField) (q : ℕ) (C : ConjClass L) : Prop

/-- A residual Galois representation ρ̄ : G_ℚ → GL₂(𝔽_p),
    parameterized by conductor N and prime p. -/
axiom ResidualRep (N p : ℕ) : Type

/-- The splitting field L₂ for the Taylor–Wiles application at level n = 2. -/
axiom twSplittingField (N p : ℕ) (ρbar : ResidualRep N p) : NumberField

-- ============================================================
-- § 2. Axiomatized Deep Theorems (Target 1)
-- ============================================================

/-- Axiom B1: Brochard's finite-level criterion (de Smit's conjecture).
    If the Artinian quotient at level n = 2 satisfies the embedding-dimension
    condition, then the patched module is free (R ≅ T).
    Reference: Brochard, Compositio Math. 153 (2017), Theorem 1.1. -/
axiom brochard_finite_criterion
  (A B : ArtinLocalRing) (M : ArtinModule B)
  (hflat : IsFlat A B M)
  (hedim : embDim B ≤ embDim A) :
  IsFreeModule B M

/-- Axiom B2: Effective Chebotarev (unconditional).
    For a finite Galois extension L/ℚ with computable absolute discriminant d_L,
    and a conjugacy class C in Gal(L/ℚ), there exists a prime q ≤ d_L^12577
    with Frob(q) ∈ C, where 12577 is an absolute constant.
    Reference: Lagarias–Montgomery–Odlyzko (1979); Ahn–Kwon (2019). -/
axiom effective_chebotarev
  (L : NumberField) (C : ConjClass L)
  (d_L : ℕ) (hdisc : absDisc L = d_L) :
  ∃ q : ℕ, Nat.Prime q ∧ q ≤ d_L ^ 12577 ∧ frobInClass L q C

/-- Axiom B3: Discriminant computability and positivity.
    The splitting field L₂ for the Taylor–Wiles application at level n = 2
    has positive discriminant computable from (N, p, ρ̄).
    Note: Within the opaque-type framework, bare existence (∃ d, absDisc L = d)
    would be vacuously true. The positivity clause d > 0 records the
    mathematical content that L₂ is a genuine number field extension.
    Reference: Standard algebraic number theory (Hensel bounds). -/
axiom tw_disc_computable
  (N p : ℕ) (ρbar : ResidualRep N p) :
  ∃ d : ℕ, d > 0 ∧ absDisc (twSplittingField N p ρbar) = d

-- ============================================================
-- § 3. CRM Hierarchy (Target 2)
-- ============================================================

/-- The constructive reverse mathematics hierarchy.
    BISH ⊂ MP ⊂ WKL ⊂ LLPO ⊂ WLPO ⊂ LPO ⊂ CLASS. -/
inductive CRMLevel where
  | BISH  : CRMLevel
  | MP    : CRMLevel
  | WKL   : CRMLevel  -- Weak König's Lemma (compactness / inverse limits)
  | LLPO  : CRMLevel
  | WLPO  : CRMLevel
  | LPO   : CRMLevel
  | CLASS : CRMLevel
  deriving DecidableEq, Repr

namespace CRMLevel

/-- The join (maximum) of two CRM levels, by exhaustive pattern match.
    Defined so that `simp [join]` or `decide` reduces on concrete constructors. -/
def join : CRMLevel → CRMLevel → CRMLevel
  | BISH,  b      => b
  | a,     BISH   => a
  | CLASS, _      => CLASS
  | _,     CLASS  => CLASS
  | LPO,   _      => LPO
  | _,     LPO    => LPO
  | WLPO,  _      => WLPO
  | _,     WLPO   => WLPO
  | LLPO,  _      => LLPO
  | _,     LLPO   => LLPO
  | WKL,   _      => WKL
  | _,     WKL    => WKL
  | MP,    MP     => MP

/-- BISH is strictly below WLPO. -/
theorem bish_ne_wlpo : BISH ≠ WLPO := by decide

end CRMLevel
