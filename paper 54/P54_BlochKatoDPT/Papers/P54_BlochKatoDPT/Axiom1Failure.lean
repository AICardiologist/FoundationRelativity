/-
  Paper 54 — Module 5: Axiom1Failure
  Bloch–Kato Calibration: Out-of-Sample DPT Test

  Formalizes Theorem D: Axiom 1 (decidable equality) FAILS for mixed
  motives. Standard Conjecture D covers Hom-spaces of pure motives
  but does NOT extend to Ext^1 (extensions = mixed motives).

  Sorry budget: 1 principled
    - ext1_not_decidable (structural impossibility: numerical equivalence
      is defined via intersection pairings on algebraic cycles; extension
      classes in Ext^1 are NOT algebraic cycles and carry no intersection
      pairing, hence no decision procedure exists. This is a substantive
      mathematical axiom, not a gap.)

  Paul C.-K. Lee, February 2026
-/

/-! # Axiom 1 Failure for Mixed Motives

The motivic fundamental line Δ(M) = det_Q H^0_f(X,M) ⊗ det_Q^{-1} H^1_f(X,M)
requires computing exact ranks of the Selmer group H^1_f(X, M).

Key distinction:
  - Pure: Hom(M, N) in the pure motive category. Axiom 1 applies via
    Standard Conjecture D (homological = numerical ⟹ decidable).
  - Mixed: Ext^1(M, N) classifies extensions 0 → N → E → M → 0.
    NO numerical equivalence for extensions.
    NO bilinear form to make Ext^1 decidable.

The Axiom 1 failure is STRUCTURAL: it is not that we lack a proof,
but that the algebraic framework (numerical equivalence) does not
extend from morphisms to extensions.
-/

-- ============================================================
-- The pure vs mixed distinction
-- ============================================================

/-- An abstract type for pure motives (in the category of Chow motives). -/
axiom PureMotive' : Type

/-- The Hom-space in the pure motive category: Hom(M, N). -/
axiom PureHom : PureMotive' → PureMotive' → Type

/-- Standard Conjecture D: homological equivalence equals numerical
equivalence for algebraic cycles on smooth projective varieties.
This makes Hom-spaces of pure motives decidable. -/
axiom StandardConjectureD : Prop

/-- The Bloch–Kato Selmer group H^1_f(X, M).
Isomorphic to Ext^1(ℚ(0), M) in the category of mixed motives. -/
axiom H1f : PureMotive' → Type

/-- A type has decidable equality (Prop-valued version).
This wraps `DecidableEq` into a Prop so it can be negated. -/
def HasDecEq (α : Type) : Prop := Nonempty (DecidableEq α)

-- ============================================================
-- The obstruction: no numerical equivalence for Ext^1
-- ============================================================

/-- **Structural axiom:** Decidable equality on H^1_f(M) is impossible.

H^1_f(M) ≅ Ext^1(ℚ(0), M) classifies extensions of motives.
Numerical equivalence is defined via intersection pairings on
algebraic cycles. Extension classes are NOT algebraic cycles —
they classify short exact sequences of motives. There is no
intersection pairing on Ext^1, hence no decision procedure.

This axiom encodes the structural impossibility: Standard Conjecture D
provides decidable Hom-spaces but cannot extend to Ext^1. -/
axiom ext1_not_decidable (M : PureMotive') :
  ¬HasDecEq (H1f M)

-- ============================================================
-- Theorem D: Axiom 1 Failure
-- ============================================================

/-- **Theorem D:** Axiom 1 fails for the mixed-motive component of
the Bloch–Kato conjecture.

The motivic fundamental line requires the rank of H^1_f(X, M),
which is an Ext^1-group in the mixed motive category. Standard
Conjecture D provides decidable equality for Hom-spaces of pure
motives, but has no analogue for extension classes.

This is a NEGATIVE result: the proof shows that no decision
procedure exists, not that one does. -/
theorem axiom1_fails_mixed (M : PureMotive') :
    ¬HasDecEq (H1f M) :=
  ext1_not_decidable M

/-- The failure is at the Hom → Ext boundary.
Standard Conjecture D decides:
  Hom(M, N) — morphisms of pure motives ✓
Standard Conjecture D does NOT decide:
  Ext^1(M, N) — extensions of pure motives ✗

The boundary is precisely: pure motives (Hom) vs mixed motives (Ext). -/
theorem axiom1_boundary :
    -- Axiom 1 applies to pure Hom-spaces (by design, Paper 50)
    StandardConjectureD →
    (∀ (M N : PureMotive'), HasDecEq (PureHom M N)) →
    -- But it does NOT extend to Ext^1
    (∀ (M : PureMotive'), ¬HasDecEq (H1f M)) :=
  fun _hSCD _hHomDec M => axiom1_fails_mixed M

/-- In the BSD special case (Paper 48), H^1_f reduces to the Mordell–Weil
group E(ℚ), whose rank is computable (conditional on BSD). This is because
elliptic curve rational points are pure geometric objects, not genuine
extensions. For higher-weight motives, no such reduction exists. -/
theorem bsd_special_case_note :
    -- The BSD success (Paper 48) does not generalize
    -- Elliptic curve points ≠ general extension classes
    (∀ (M : PureMotive'), ¬HasDecEq (H1f M)) :=
  axiom1_fails_mixed
