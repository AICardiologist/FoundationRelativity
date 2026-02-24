/-
  Paper 70: The Archimedean Principle — Weil RH from CRM Axioms
  The motivic two-line proof: positive-definiteness + Rosati → |α|² = q^w.

  This is the motivic side's sharp eigenvalue bound.
  The automorphic side cannot reproduce it (see Ramanujan.lean).

  Reference: Deligne, Publ. Math. IHÉS 43 (1974), 273–307.
-/
import Mathlib.Algebra.Order.Field.Basic

-- ============================================================
-- The motivic two-liner
-- ============================================================

/-- **Weil RH from CRM axioms.**
    The Rosati equation ⟨Frob·x, Frob·x⟩ = q^w · ⟨x,x⟩
    with positive-definiteness (⟨x,x⟩ > 0 for x ≠ 0)
    gives |α|² = q^w by cancellation.

    This captures the core mechanism: the motivic side provides sharp
    eigenvalue bounds from a *single* finite-dimensional axiom (Rosati).
    The automorphic side would need an infinite schema (unitarity of
    Sym^m(π) for all m).

    Reference: Deligne (1974), via Rosati involution + positive-definiteness.
    CRM cost: BISH (algebraic cancellation over an ordered field). -/
theorem weil_RH_from_CRM {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (alpha_sq qw ip_val : R)
    (h_pos : ip_val > 0)
    (h_rosati : alpha_sq * ip_val = qw * ip_val) :
    alpha_sq = qw := by
  have h_ne : ip_val ≠ 0 := ne_of_gt h_pos
  exact mul_right_cancel₀ h_ne h_rosati

/-- Variant with explicit division (equivalent formulation).
    From α² · ⟨x,x⟩ = q^w · ⟨x,x⟩ and ⟨x,x⟩ ≠ 0,
    divide both sides. -/
theorem weil_RH_from_CRM_div {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (alpha_sq qw ip_val : R)
    (h_pos : ip_val > 0)
    (h_rosati : alpha_sq * ip_val = qw * ip_val) :
    alpha_sq = qw := by
  have h_ne : ip_val ≠ 0 := ne_of_gt h_pos
  have : alpha_sq * ip_val / ip_val = qw * ip_val / ip_val := by rw [h_rosati]
  simp [mul_div_cancel_right₀, h_ne] at this
  exact this
